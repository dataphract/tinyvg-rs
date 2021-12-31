//! A library for reading and writing the TinyVG vector graphics format.
//!
//! # Examples
//!
//! ## Reading a TinyVG file
//!
//! ```no_run
//! use std::fs::File;
//!
//! use tinyvg::{Cmd, ColorTableEncoding, TinyVgReader};
//! # use tinyvg::TinyVgError;
//!
//! # pub fn f() -> tinyvg::Result<()> {
//! let mut f = File::open("example.tvg")?;
//! let mut r = TinyVgReader::new(&mut f);
//!
//! let header = r.read_header()?;
//!
//! let table = match r.read_color_table()? {
//!     ColorTableEncoding::Rgba8888(r) => r.collect::<Result<Vec<_>, _>>()?,
//!     _ => panic!("expected RGBA8888 color encoding"),
//! };
//!
//! let mut commands: Vec<Cmd> = Vec::new();
//! let mut cr = r.read_commands()?;
//! while let Some(cmd) = cr.read_cmd()? {
//!     commands.push(cmd.try_into()?);
//! }
//!
//! println!("Number of commands: {}", commands.len());
//! # Ok(())
//! # }
//! ```

use std::{
    fmt,
    io::{self, Read, Write},
    iter,
    marker::PhantomData,
    ops::{BitAnd, Shl, Shr, Sub},
};

use arrayvec::ArrayVec;
use byteorder::{ReadBytesExt, WriteBytesExt, LE};

const MAGIC: [u8; 2] = [0x72, 0x56];
const VERSION: u8 = 1;

pub type Result<T> = std::result::Result<T, TinyVgError>;

#[derive(Debug)]
pub enum ErrorKind {
    Io(io::Error),
    InvalidData,
    OutOfRange,
    Unsupported,
    NoSuchColor,
    BadPosition,
    Fatal,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::Io(e) => write!(f, "I/O error: {}", e),
            ErrorKind::InvalidData => write!(f, "Invalid data"),
            ErrorKind::OutOfRange => write!(f, "Value out of range"),
            ErrorKind::Unsupported => write!(f, "Unsupported"),
            ErrorKind::NoSuchColor => write!(f, "No such color"),
            ErrorKind::BadPosition => write!(f, "Bad position"),
            ErrorKind::Fatal => write!(f, "Fatal error"),
        }
    }
}

#[derive(Debug)]
pub struct TinyVgError {
    kind: ErrorKind,
    msg: &'static str,
}

impl fmt::Display for TinyVgError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.msg)
    }
}

impl std::error::Error for TinyVgError {}

impl From<ErrorKind> for TinyVgError {
    fn from(kind: ErrorKind) -> Self {
        TinyVgError { kind, msg: "" }
    }
}

impl From<io::Error> for TinyVgError {
    fn from(e: io::Error) -> Self {
        TinyVgError {
            kind: ErrorKind::Io(e),
            msg: "",
        }
    }
}

// VarUInt encoding/decoding ======================================================================

trait ReadVarU32Ext: Read {
    fn read_var_u32(&mut self) -> Result<u32> {
        let mut out = 0;

        // Read up to 5 bytes of VarUInt encoding.
        //
        // The first 4 bytes use the low 7 bits for the value and set the high
        // bit when there are more bytes to read.
        for i in 0..4 {
            let b = self.read_u8()?;

            // Mask off the high bit and shift into position.
            out |= ((b & 0x7F) as u32) << (7 * i);

            // If the high bit is clear, there are no more bytes to read.
            if b & 0x80 == 0 {
                return Ok(out);
            }
        }

        // If the full 5 bytes are used, the high 4 bits of the 5th byte must be
        // 0b1000.
        let b = self.read_u8()?;
        if b & 0xF0 != 0x00 {
            return Err(TinyVgError {
                kind: ErrorKind::InvalidData,
                msg: "Invalid 5th byte in VarUInt encoding",
            });
        }

        // Mask off the high 4 bits and shift into position.
        out |= ((b & 0x0F) as u32) << 28;

        Ok(out)
    }
}

impl<R: Read> ReadVarU32Ext for R {}

trait WriteVarU32Ext: Write {
    fn write_var_u32(&mut self, value: u32) -> io::Result<usize> {
        if value < (1 << 14) {
            if value < (1 << 7) {
                self.write_all(&[value as u8])?;

                Ok(1)
            } else {
                self.write_all(&[(0x80 | value & 0x7F) as u8, (value >> 7) as u8])?;

                Ok(2)
            }
        } else if value < (1 << 28) {
            if value < (1 << 21) {
                self.write_all(&[
                    (0x80 | value & 0x7F) as u8,
                    (0x80 | (value >> 7) & 0x7F) as u8,
                    (value >> 14) as u8,
                ])?;

                Ok(3)
            } else {
                self.write_all(&[
                    (0x80 | value & 0x7F) as u8,
                    (0x80 | (value >> 7) & 0x7F) as u8,
                    (0x80 | (value >> 14) & 0x7F) as u8,
                    (value >> 21) as u8,
                ])?;

                Ok(4)
            }
        } else {
            self.write_all(&[
                (0x80 | value & 0x7F) as u8,
                (0x80 | (value >> 7) & 0x7F) as u8,
                (0x80 | (value >> 14) & 0x7F) as u8,
                (0x80 | (value >> 21) & 0x7F) as u8,
                (value >> 28) as u8,
            ])?;

            Ok(5)
        }
    }
}

impl<W: Write> WriteVarU32Ext for W {}

// Colors =========================================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ColorEncodingTag {
    Rgba8888 = 0,
    Rgb565 = 1,
    RgbaF32 = 2,
    Custom = 3,
}

impl TryFrom<u8> for ColorEncodingTag {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<ColorEncodingTag> {
        use ColorEncodingTag::*;
        match value {
            0 => Ok(Rgba8888),
            1 => Ok(Rgb565),
            2 => Ok(RgbaF32),
            3 => Ok(Custom),
            _ => Err(TinyVgError {
                kind: ErrorKind::InvalidData,
                msg: "unrecognized color encoding tag",
            }),
        }
    }
}

/// A color encoded as RGBA8888.
///
/// This color has red, green, blue and alpha channels, each encoded as a `u8`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rgba8888 {
    pub red: u8,
    pub green: u8,
    pub blue: u8,
    pub alpha: u8,
}

impl From<Rgb565> for Rgba8888 {
    fn from(c: Rgb565) -> Self {
        Rgba8888 {
            red: c.red() << 3,
            green: c.green() << 2,
            blue: c.blue() << 3,
            alpha: 1,
        }
    }
}

/// A color encoded as RGB565.
///
/// This color has a 5-bit red channel, a 6-bit green channel, and a 5-bit blue
/// channel.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rgb565 {
    bytes: [u8; 2],
}

impl Rgb565 {
    pub fn new(red: u8, green: u8, blue: u8) -> Option<Rgb565> {
        if red >= (1 << 5) || green >= (1 << 6) || blue >= (1 << 5) {
            None
        } else {
            Some(Rgb565 {
                bytes: [green << 5 | red, blue << 3 | green >> 3],
            })
        }
    }

    pub fn red(&self) -> u8 {
        self.bytes[0].bits(0, 5)
    }

    pub fn green(&self) -> u8 {
        self.bytes[1].bits(0, 3) << 3 | self.bytes[0].bits(5, 3)
    }

    pub fn blue(&self) -> u8 {
        self.bytes[1].bits(3, 5)
    }
}

/// A color encoded as RGBAF32.
///
/// This color has red, green, blue and alpha channels, each encoded as an `f32`
/// in the range [0.0, 1.0].
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct RgbaF32 {
    red: f32,
    green: f32,
    blue: f32,
    alpha: f32,
}

impl RgbaF32 {
    pub fn red(&self) -> f32 {
        self.red
    }

    pub fn green(&self) -> f32 {
        self.green
    }

    pub fn blue(&self) -> f32 {
        self.blue
    }

    pub fn alpha(&self) -> f32 {
        self.alpha
    }
}

impl From<Rgba8888> for RgbaF32 {
    fn from(c: Rgba8888) -> Self {
        RgbaF32 {
            red: c.red as f32 / 255.0,
            green: c.green as f32 / 255.0,
            blue: c.blue as f32 / 255.0,
            alpha: c.alpha as f32 / 255.0,
        }
    }
}

impl From<Rgb565> for RgbaF32 {
    fn from(c: Rgb565) -> Self {
        Self::from(Rgba8888::from(c))
    }
}

/// A trait for TinyVG color table encodings.
///
/// Implementors of this trait can be read from and written to the TinyVG color
/// table.
pub trait ColorEncoding: Sized {
    // TODO: end users should not be able to implement this method.
    fn tag() -> ColorEncodingTag;

    /// Reads a single entry from the color table.
    fn read_table_entry<R: Read>(reader: R) -> Result<Self>;

    /// Writes a single entry to the color table.
    fn write_table_entry<W: Write>(&self, writer: W) -> Result<()>;
}

impl ColorEncoding for Rgba8888 {
    fn tag() -> ColorEncodingTag {
        ColorEncodingTag::Rgba8888
    }

    fn read_table_entry<R: Read>(mut reader: R) -> Result<Rgba8888> {
        let red = reader.read_u8()?;
        let green = reader.read_u8()?;
        let blue = reader.read_u8()?;
        let alpha = reader.read_u8()?;

        Ok(Rgba8888 {
            red,
            green,
            blue,
            alpha,
        })
    }

    fn write_table_entry<W: Write>(&self, mut writer: W) -> Result<()> {
        writer.write_u8(self.red)?;
        writer.write_u8(self.green)?;
        writer.write_u8(self.blue)?;
        writer.write_u8(self.alpha)?;

        Ok(())
    }
}

impl ColorEncoding for Rgb565 {
    fn tag() -> ColorEncodingTag {
        ColorEncodingTag::Rgb565
    }

    fn read_table_entry<R: Read>(mut reader: R) -> Result<Rgb565> {
        let mut bytes = [0u8; 2];
        reader.read_exact(&mut bytes)?;

        Ok(Rgb565 { bytes })
    }

    fn write_table_entry<W: Write>(&self, mut writer: W) -> Result<()> {
        writer.write_all(&self.bytes)?;

        Ok(())
    }
}

impl ColorEncoding for RgbaF32 {
    fn tag() -> ColorEncodingTag {
        ColorEncodingTag::RgbaF32
    }

    fn read_table_entry<R: Read>(mut reader: R) -> Result<RgbaF32> {
        let red = reader.read_f32::<LE>()?;
        let green = reader.read_f32::<LE>()?;
        let blue = reader.read_f32::<LE>()?;
        let alpha = reader.read_f32::<LE>()?;

        // TODO: Values must be between 0.0 and 1.0. Validate here?
        Ok(RgbaF32 {
            red,
            green,
            blue,
            alpha,
        })
    }

    fn write_table_entry<W: Write>(&self, mut writer: W) -> Result<()> {
        writer.write_f32::<LE>(self.red)?;
        writer.write_f32::<LE>(self.green)?;
        writer.write_f32::<LE>(self.blue)?;
        writer.write_f32::<LE>(self.alpha)?;

        Ok(())
    }
}

impl ColorEncoding for () {
    fn tag() -> ColorEncodingTag {
        ColorEncodingTag::Custom
    }

    fn read_table_entry<R: Read>(_reader: R) -> Result<()> {
        Ok(())
    }

    fn write_table_entry<W: Write>(&self, _writer: W) -> Result<()> {
        Ok(())
    }
}

pub enum ColorTableEncoding<'a, R: Read, C: ColorEncoding = ()> {
    Rgba8888(ColorTableEntries<'a, R, Rgba8888>),
    Rgb565(ColorTableEntries<'a, R, Rgb565>),
    RgbaF32(ColorTableEntries<'a, R, RgbaF32>),
    Custom(ColorTableEntries<'a, R, C>),
}

impl<'a, R: Read> ColorTableEncoding<'a, R, ()> {
    pub fn to_rgba_f32(self) -> ToRgbaF32<'a, R> {
        ToRgbaF32 { encoding: self }
    }
}

pub struct ToRgbaF32<'a, R: Read> {
    encoding: ColorTableEncoding<'a, R, ()>,
}

impl<'a, R: Read> Iterator for ToRgbaF32<'a, R> {
    type Item = Result<RgbaF32>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.encoding {
            ColorTableEncoding::Rgba8888(ref mut r) => r.next().map(|res| res.map(RgbaF32::from)),
            ColorTableEncoding::Rgb565(ref mut r) => r.next().map(|res| res.map(RgbaF32::from)),
            ColorTableEncoding::RgbaF32(ref mut r) => r.next().map(|res| res.map(RgbaF32::from)),
            ColorTableEncoding::Custom(_) => Some(Err(TinyVgError {
                kind: ErrorKind::Unsupported,
                msg: "cannot convert custom type to RGBAF32",
            })),
        }
    }
}

/// An iterator over the entries of the TinyVG color table.
pub struct ColorTableEntries<'a, R: Read, C: ColorEncoding> {
    header: TinyVgHeader,
    tvg: &'a mut TinyVgReader<R>,
    phantom: PhantomData<C>,
}

impl<'a, R: Read, C: ColorEncoding> ColorTableEntries<'a, R, C> {
    fn new(tvg: &'a mut TinyVgReader<R>) -> Self {
        ColorTableEntries {
            header: *tvg.header.as_ref().unwrap(),
            tvg,
            phantom: PhantomData,
        }
    }
}

impl<'a, R: Read, C: ColorEncoding> Iterator for ColorTableEntries<'a, R, C> {
    type Item = Result<C>;

    fn next(&mut self) -> Option<Self::Item> {
        (self.tvg.colors_read < self.header.color_count).then(|| {
            let entry = C::read_table_entry(&mut self.tvg.reader)?;
            self.tvg.colors_read += 1;
            Ok(entry)
        })
    }
}

impl<'a, R: Read, C: ColorEncoding> ExactSizeIterator for ColorTableEntries<'a, R, C> {
    fn len(&self) -> usize {
        (self.header.color_count - self.tvg.colors_read) as usize
    }
}

// Coordinates ====================================================================================

/// Indicates the possible range of coordinates in the image.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoordinateRange {
    /// Coordinates are signed 16-bit integers, with a range of [-32768, 32767].
    Default = 0,
    /// Coordinates are signed 8-bit integers, with a range of [-128, 127].
    Reduced = 1,
    /// Coordinates are signed 32-bit integers, with a range of [-2147483648, 2147483647].
    Enhanced = 2,
}

impl CoordinateRange {
    fn read_default<R: Read>(reader: &mut R) -> io::Result<i32> {
        reader.read_i16::<LE>().map(i16::into)
    }

    fn read_reduced<R: Read>(reader: &mut R) -> io::Result<i32> {
        let v = reader.read_i8().map(i8::into)?;
        Ok(v)
    }

    fn read_enhanced<R: Read>(reader: &mut R) -> io::Result<i32> {
        reader.read_i32::<LE>()
    }

    /// Returns a function which reads the correct `Unit` width for this
    /// `CoordinateRange`.
    ///
    /// The returned function reads unscaled unit values; the correct value is
    /// obtained by dividing by the scale factor specified in the header.
    fn read_fn<R: Read>(self) -> fn(&mut R) -> io::Result<i32> {
        match self {
            CoordinateRange::Default => CoordinateRange::read_default,
            CoordinateRange::Reduced => CoordinateRange::read_reduced,
            CoordinateRange::Enhanced => CoordinateRange::read_enhanced,
        }
    }

    fn write_default<W: Write>(writer: &mut W, value: i32) -> Result<()> {
        let v = value.try_into().map_err(|_| ErrorKind::OutOfRange)?;
        writer.write_i16::<LE>(v)?;

        Ok(())
    }

    fn write_reduced<W: Write>(writer: &mut W, value: i32) -> Result<()> {
        let v = value.try_into().map_err(|_| ErrorKind::OutOfRange)?;
        writer.write_i8(v)?;

        Ok(())
    }

    fn write_enhanced<W: Write>(writer: &mut W, value: i32) -> Result<()> {
        writer.write_i32::<LE>(value)?;

        Ok(())
    }

    /// Returns a function which writes the correct `Unit` width for this
    /// `CoordinateRange`.
    ///
    /// The returned function writes unscaled unit values; the value passed in
    /// by the caller should already be multiplied by the scaling factor.
    fn write_fn<W: Write>(self) -> fn(&mut W, i32) -> Result<()> {
        match self {
            CoordinateRange::Default => CoordinateRange::write_default,
            CoordinateRange::Reduced => CoordinateRange::write_reduced,
            CoordinateRange::Enhanced => CoordinateRange::write_enhanced,
        }
    }
}

impl TryFrom<u8> for CoordinateRange {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<CoordinateRange> {
        use CoordinateRange::*;
        match value {
            0 => Ok(Default),
            1 => Ok(Reduced),
            2 => Ok(Enhanced),
            _ => Err(TinyVgError {
                kind: ErrorKind::InvalidData,
                msg: "unrecognized coordinate range tag",
            }),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum StyleId {
    FlatColor = 0,
    LinearGradient = 1,
    RadialGradient = 2,
}

impl TryFrom<u8> for StyleId {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<Self> {
        match value {
            0 => Ok(StyleId::FlatColor),
            1 => Ok(StyleId::LinearGradient),
            2 => Ok(StyleId::RadialGradient),
            _ => Err(TinyVgError {
                kind: ErrorKind::InvalidData,
                msg: "unrecognized style type tag",
            }),
        }
    }
}

/// The style of an element.
#[derive(Clone, Debug, PartialEq)]
pub enum Style {
    /// The entire element is a single color.
    FlatColor { color: u32 },
    /// The element is colored with a linear gradient.
    LinearGradient {
        start: Point,
        end: Point,
        start_color: u32,
        end_color: u32,
    },
    /// The element is colored with a radial gradient.
    RadialGradient {
        start: Point,
        end: Point,
        start_color: u32,
        end_color: u32,
    },
}

impl Style {
    fn id(&self) -> StyleId {
        match self {
            Style::FlatColor { .. } => StyleId::FlatColor,
            Style::LinearGradient { .. } => StyleId::LinearGradient,
            Style::RadialGradient { .. } => StyleId::RadialGradient,
        }
    }
}

/// A point in 2-D space.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Point {
    /// The point's x-coordinate.
    pub x: f32,

    /// The point's y-coordinate.
    pub y: f32,
}

/// A stream of [`Point`]s being read from TinyVG data.
pub struct Points<'a, 'b, R: Read> {
    remaining: u32,
    reader: &'a mut CommandReader<'b, R>,
}

impl<'a, 'b, R: Read> Iterator for Points<'a, 'b, R> {
    type Item = Result<Point>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining > 0 {
            let point = self.reader.read_point();

            if point.is_ok() {
                self.remaining -= 1;
            } else {
                self.reader.errored = true;
            }

            Some(point)
        } else {
            None
        }
    }
}

impl<'a, 'b, R: Read> Drop for Points<'a, 'b, R> {
    fn drop(&mut self) {
        // Attempt to read through the remaining points.
        while let Some(res) = self.next() {
            // If a read fails, set the error flag in the CommandReader, causing
            // future reads to fail as well.
            if res.is_err() {
                self.reader.errored = true;
            }
        }
    }
}

/// A rectangle.
#[derive(Clone, Debug, PartialEq)]
pub struct Rect {
    pub x: f32,
    pub y: f32,
    pub width: f32,
    pub height: f32,
}

/// A stream of [`Rect`]s being read from TinyVG data.
pub struct Rects<'a, 'b, R: Read> {
    remaining: u32,
    reader: &'a mut CommandReader<'b, R>,
}

impl<'a, 'b, R: Read> Iterator for Rects<'a, 'b, R> {
    type Item = Result<Rect>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining > 0 {
            let rect = self.reader.read_rect();

            if rect.is_ok() {
                self.remaining -= 1;
            } else {
                self.reader.errored = true;
            }

            Some(rect)
        } else {
            None
        }
    }
}

impl<'a, 'b, R: Read> Drop for Rects<'a, 'b, R> {
    fn drop(&mut self) {
        // Attempt to read through the remaining rects.
        while let Some(res) = self.next() {
            // If a read fails, set the error flag in the CommandReader, causing
            // future reads to fail as well.
            if res.is_err() {
                self.reader.errored = true;
            }
        }
    }
}

/// The direction of rotation of an arc.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ArcSweep {
    /// The arc sweeps in the clockwise direction.
    Cw = 0,
    /// The arc sweeps in the counter-clockwise (or anti-clockwise) direction.
    Ccw = 1,
}

impl TryFrom<u8> for ArcSweep {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<Self> {
        match value {
            0 => Ok(ArcSweep::Cw),
            1 => Ok(ArcSweep::Ccw),
            _ => Err(TinyVgError {
                kind: ErrorKind::InvalidData,
                msg: "unrecognized arc sweep value",
            }),
        }
    }
}

// Paths ==========================================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum PathInstrId {
    Line = 0,
    HorizontalLine = 1,
    VerticalLine = 2,
    CubicBezier = 3,
    ArcCircle = 4,
    ArcEllipse = 5,
    Close = 6,
    QuadraticBezier = 7,
}

impl PathInstrId {
    fn with_line_width(self, has_line_width: bool) -> u8 {
        (has_line_width as u8) << 4 | self as u8
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PathInstrKind {
    Line {
        to: Point,
    },
    HorizontalLine {
        to_x: f32,
    },
    VerticalLine {
        to_y: f32,
    },
    CubicBezier {
        control_0: Point,
        control_1: Point,
        to: Point,
    },
    ArcCircle {
        large_arc: bool,
        sweep: ArcSweep,
        radius: f32,
        to: Point,
    },
    ArcEllipse {
        large_arc: bool,
        sweep: ArcSweep,
        radius_x: f32,
        radius_y: f32,
        rotation_deg: f32,
        to: Point,
    },
    Close,
    QuadraticBezier {
        control: Point,
        to: Point,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct PathInstr {
    pub kind: PathInstrKind,
    pub line_width: Option<f32>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Segment {
    pub start: Point,
    pub instrs: Vec<PathInstr>,
}

// This is the capacity used by the Zig implementation.
const MAX_SEGMENTS: usize = 1024;

/// An iterator over [`Segment`]s read from TinyVG data.
pub struct Segments<'a, 'b, R: Read> {
    lengths: arrayvec::IntoIter<u32, MAX_SEGMENTS>,
    reader: &'a mut CommandReader<'b, R>,
}

impl<'a, 'b, R: Read> Iterator for Segments<'a, 'b, R> {
    type Item = Result<Segment>;

    fn next(&mut self) -> Option<Self::Item> {
        self.lengths.next().map(|len| self.reader.read_segment(len))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Path {
    pub segments: Vec<Segment>,
}

/// A line segment.
#[derive(Clone, Debug, PartialEq)]
pub struct Line {
    /// The start point of the line segment.
    pub start: Point,
    /// The end point of the line segment.
    pub end: Point,
}

/// An iterator over [`Line`]s read from TinyVG data.
pub struct Lines<'a, 'b, R: Read> {
    remaining: u32,
    reader: &'a mut CommandReader<'b, R>,
}

impl<'a, 'b, R: Read> Iterator for Lines<'a, 'b, R> {
    type Item = Result<Line>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining > 0 {
            let line = self.reader.read_line();

            if line.is_ok() {
                self.remaining -= 1;
            } else {
                self.reader.errored = true;
            }

            Some(line)
        } else {
            None
        }
    }
}

impl<'a, 'b, R: Read> Drop for Lines<'a, 'b, R> {
    fn drop(&mut self) {
        // Attempt to read through the remaining lines.
        while let Some(res) = self.next() {
            // If a read fails, set the error flag in the CommandReader, causing
            // future reads to fail as well.
            if res.is_err() {
                self.reader.errored = true;
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum CmdId {
    EndOfDocument = 0,
    FillPoly = 1,
    FillRects = 2,
    FillPath = 3,
    DrawLines = 4,
    DrawLoop = 5,
    DrawStrip = 6,
    DrawPath = 7,
    OutlineFillPoly = 8,
    OutlineFillRects = 9,
    OutlineFillPath = 10,
}

impl CmdId {
    fn with_style_id(self, style: StyleId) -> u8 {
        ((style as u8) << 6) | self as u8
    }
}

impl TryFrom<u8> for CmdId {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<Self> {
        use CmdId::*;

        let cmd = match value {
            0 => EndOfDocument,
            1 => FillPoly,
            2 => FillRects,
            3 => FillPath,
            4 => DrawLines,
            5 => DrawLoop,
            6 => DrawStrip,
            7 => DrawPath,
            8 => OutlineFillPoly,
            9 => OutlineFillRects,
            10 => OutlineFillPath,
            _ => {
                return Err(TinyVgError {
                    kind: ErrorKind::InvalidData,
                    msg: "unrecognized command tag",
                });
            }
        };

        Ok(cmd)
    }
}

pub enum CmdReader<'a, 'b, R: Read> {
    FillPoly {
        fill_style: Style,
        points: Points<'a, 'b, R>,
    },
    FillRects {
        fill_style: Style,
        rects: Rects<'a, 'b, R>,
    },
    FillPath {
        fill_style: Style,
        segments: Segments<'a, 'b, R>,
    },
    DrawLines {
        line_style: Style,
        width: f32,
        lines: Lines<'a, 'b, R>,
    },
    DrawLoop {
        line_style: Style,
        width: f32,
        points: Points<'a, 'b, R>,
    },
    DrawStrip {
        line_style: Style,
        width: f32,
        points: Points<'a, 'b, R>,
    },
    DrawPath {
        line_style: Style,
        width: f32,
        segments: Segments<'a, 'b, R>,
    },
    OutlineFillPoly {
        fill_style: Style,
        line_style: Style,
        line_width: f32,
        points: Points<'a, 'b, R>,
    },
    OutlineFillRects {
        fill_style: Style,
        line_style: Style,
        line_width: f32,
        rects: Rects<'a, 'b, R>,
    },
    OutlineFillPath {
        fill_style: Style,
        line_style: Style,
        line_width: f32,
        segments: Segments<'a, 'b, R>,
    },
}

impl<'a, 'b, R: Read> TryInto<Cmd> for CmdReader<'a, 'b, R> {
    type Error = TinyVgError;

    fn try_into(self) -> Result<Cmd> {
        let cmd = match self {
            CmdReader::FillPoly { fill_style, points } => Cmd::FillPoly {
                fill_style,
                points: points.collect::<Result<_>>()?,
            },

            CmdReader::FillRects { fill_style, rects } => Cmd::FillRects {
                fill_style,
                rects: rects.collect::<Result<_>>()?,
            },

            CmdReader::FillPath {
                fill_style,
                segments,
            } => Cmd::FillPath {
                fill_style,
                segments: segments.collect::<Result<_>>()?,
            },

            CmdReader::DrawLines {
                line_style,
                width,
                lines,
            } => Cmd::DrawLines {
                line_style,
                width,
                lines: lines.collect::<Result<_>>()?,
            },

            CmdReader::DrawLoop {
                line_style,
                width,
                points,
            } => Cmd::DrawLoop {
                line_style,
                width,
                points: points.collect::<Result<_>>()?,
            },

            CmdReader::DrawStrip {
                line_style,
                width,
                points,
            } => Cmd::DrawStrip {
                line_style,
                width,
                points: points.collect::<Result<_>>()?,
            },

            CmdReader::DrawPath {
                line_style,
                width,
                segments,
            } => Cmd::DrawPath {
                line_style,
                width,
                segments: segments.collect::<Result<_>>()?,
            },

            CmdReader::OutlineFillPoly {
                fill_style,
                line_style,
                line_width,
                points,
            } => Cmd::OutlineFillPoly {
                fill_style,
                line_style,
                line_width,
                points: points.collect::<Result<_>>()?,
            },

            CmdReader::OutlineFillRects {
                fill_style,
                line_style,
                line_width,
                rects,
            } => Cmd::OutlineFillRects {
                fill_style,
                line_style,
                line_width,
                rects: rects.collect::<Result<_>>()?,
            },

            CmdReader::OutlineFillPath {
                fill_style,
                line_style,
                line_width,
                segments,
            } => Cmd::OutlineFillPath {
                fill_style,
                line_style,
                line_width,
                segments: segments.collect::<Result<_>>()?,
            },
        };

        Ok(cmd)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Cmd {
    FillPoly {
        fill_style: Style,
        points: Vec<Point>,
    },
    FillRects {
        fill_style: Style,
        rects: Vec<Rect>,
    },
    FillPath {
        fill_style: Style,
        segments: Vec<Segment>,
    },
    DrawLines {
        line_style: Style,
        width: f32,
        lines: Vec<Line>,
    },
    DrawLoop {
        line_style: Style,
        width: f32,
        points: Vec<Point>,
    },
    DrawStrip {
        line_style: Style,
        width: f32,
        points: Vec<Point>,
    },
    DrawPath {
        line_style: Style,
        width: f32,
        segments: Vec<Segment>,
    },
    OutlineFillPoly {
        fill_style: Style,
        line_style: Style,
        line_width: f32,
        points: Vec<Point>,
    },
    OutlineFillRects {
        fill_style: Style,
        line_style: Style,
        line_width: f32,
        rects: Vec<Rect>,
    },
    OutlineFillPath {
        fill_style: Style,
        line_style: Style,
        line_width: f32,
        segments: Vec<Segment>,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TinyVgHeader {
    pub scale: u8,
    pub encoding: ColorEncodingTag,
    pub range: CoordinateRange,
    pub width: u32,
    pub height: u32,
    pub color_count: u32,
}

// TinyVG reading =================================================================================

pub struct CommandReader<'a, R: Read> {
    // TODO: provide more context
    errored: bool,

    header: TinyVgHeader,
    read_unit_fn: fn(&mut R) -> io::Result<i32>,
    tvg: &'a mut TinyVgReader<R>,
}

impl<'a, R: Read> CommandReader<'a, R> {
    fn read_count(&mut self) -> Result<u32> {
        let v = self.tvg.reader.read_var_u32()?;
        v.checked_add(1).ok_or(TinyVgError {
            kind: ErrorKind::OutOfRange,
            msg: "count overflowed a u32",
        })
    }

    fn read_style(&mut self, id: StyleId) -> Result<Style> {
        let style = match id {
            StyleId::FlatColor => Style::FlatColor {
                color: self.tvg.reader.read_var_u32()?,
            },
            StyleId::LinearGradient => Style::LinearGradient {
                start: self.read_point()?,
                end: self.read_point()?,
                start_color: self.tvg.reader.read_var_u32()?,
                end_color: self.tvg.reader.read_var_u32()?,
            },
            StyleId::RadialGradient => Style::RadialGradient {
                start: self.read_point()?,
                end: self.read_point()?,
                start_color: self.tvg.reader.read_var_u32()?,
                end_color: self.tvg.reader.read_var_u32()?,
            },
        };

        Ok(style)
    }

    fn read_unit(&mut self) -> io::Result<f32> {
        let num = (self.read_unit_fn)(&mut self.tvg.reader)?;
        Ok(num as f32 / (1 << self.header.scale) as f32)
    }

    fn read_point(&mut self) -> Result<Point> {
        let x = self.read_unit()?;
        let y = self.read_unit()?;

        Ok(Point { x, y })
    }

    fn read_points<'b>(&'b mut self, point_count: u32) -> Points<'b, 'a, R> {
        Points {
            remaining: point_count,
            reader: self,
        }
    }

    fn read_line(&mut self) -> Result<Line> {
        let start = self.read_point()?;
        let end = self.read_point()?;

        Ok(Line { start, end })
    }

    fn read_lines<'b>(&'b mut self, line_count: u32) -> Lines<'b, 'a, R> {
        Lines {
            remaining: line_count,
            reader: self,
        }
    }

    fn read_rect(&mut self) -> Result<Rect> {
        let x = self.read_unit()?;
        let y = self.read_unit()?;
        let width = self.read_unit()?;
        let height = self.read_unit()?;

        Ok(Rect {
            x,
            y,
            width,
            height,
        })
    }

    fn read_rects<'b>(&'b mut self, rect_count: u32) -> Rects<'b, 'a, R> {
        Rects {
            remaining: rect_count,
            reader: self,
        }
    }

    fn read_path_instr(&mut self) -> Result<PathInstr> {
        let tag = self.tvg.reader.read_u8()?;

        let instr = tag.bits(0, 3);
        let has_line_width = tag.bits(4, 1) == 1;

        let line_width = has_line_width.then(|| self.read_unit()).transpose()?;

        let kind = match instr {
            0 => PathInstrKind::Line {
                to: self.read_point()?,
            },
            1 => PathInstrKind::HorizontalLine {
                to_x: self.read_unit()?,
            },
            2 => PathInstrKind::VerticalLine {
                to_y: self.read_unit()?,
            },
            3 => PathInstrKind::CubicBezier {
                control_0: self.read_point()?,
                control_1: self.read_point()?,
                to: self.read_point()?,
            },
            4 => {
                let flags = self.tvg.reader.read_u8()?;
                let large_arc = flags.bits(0, 1) == 1;
                let sweep = ArcSweep::try_from(flags.bits(1, 1))?;
                let radius = self.read_unit()?;
                let to = self.read_point()?;

                PathInstrKind::ArcCircle {
                    large_arc,
                    sweep,
                    radius,
                    to,
                }
            }
            5 => {
                let flags = self.tvg.reader.read_u8()?;
                let large_arc = flags.bits(0, 1) == 1;
                let sweep = ArcSweep::try_from(flags.bits(1, 1))?;
                let radius_x = self.read_unit()?;
                let radius_y = self.read_unit()?;
                let rotation_deg = self.read_unit()?;
                let to = self.read_point()?;

                PathInstrKind::ArcEllipse {
                    large_arc,
                    sweep,
                    radius_x,
                    radius_y,
                    rotation_deg,
                    to,
                }
            }
            6 => PathInstrKind::Close,
            7 => PathInstrKind::QuadraticBezier {
                control: self.read_point()?,
                to: self.read_point()?,
            },
            _ => {
                return Err(TinyVgError {
                    kind: ErrorKind::InvalidData,
                    msg: "unrecognized path instruction tag",
                });
            }
        };

        Ok(PathInstr { kind, line_width })
    }

    fn read_segment(&mut self, instr_count: u32) -> Result<Segment> {
        let start = self.read_point()?;
        let instrs = iter::repeat_with(|| self.read_path_instr())
            .take(instr_count as usize)
            .collect::<Result<Vec<_>>>()?;

        Ok(Segment { start, instrs })
    }

    fn read_segments<'b>(&'b mut self, segment_count: u32) -> Result<Segments<'b, 'a, R>> {
        let ct_usize: usize = segment_count
            .try_into()
            .expect("segment count overflows a usize");
        if ct_usize > MAX_SEGMENTS {
            return Err(TinyVgError {
                kind: ErrorKind::Unsupported,
                msg: "too many segments in path",
            });
        }

        let lengths: ArrayVec<u32, MAX_SEGMENTS> = iter::repeat_with(|| self.read_count())
            .take(ct_usize)
            .collect::<Result<_>>()?;

        Ok(Segments {
            lengths: lengths.into_iter(),
            reader: self,
        })
    }

    pub fn read_cmd<'b>(&'b mut self) -> Result<Option<CmdReader<'b, 'a, R>>> {
        if self.errored {
            return Err(TinyVgError {
                kind: ErrorKind::Fatal,
                msg: "reader previously errored",
            });
        }

        if self.tvg.commands_finished {
            return Ok(None);
        }

        let tag = self.tvg.reader.read_u8()?;
        let id = CmdId::try_from(tag.bits(0, 6))?;
        let prim_style = StyleId::try_from(tag.bits(6, 2))?;

        let cmd = match id {
            CmdId::EndOfDocument => {
                self.tvg.commands_finished = true;
                None
            }

            CmdId::FillPoly => {
                let point_count = self.read_count()?;
                Some(CmdReader::FillPoly {
                    fill_style: self.read_style(prim_style)?,
                    points: self.read_points(point_count),
                })
            }

            CmdId::FillRects => {
                let rect_count = self.read_count()?;

                Some(CmdReader::FillRects {
                    fill_style: self.read_style(prim_style)?,
                    rects: self.read_rects(rect_count),
                })
            }

            CmdId::FillPath => {
                let segment_count = self.read_count()?;

                Some(CmdReader::FillPath {
                    fill_style: self.read_style(prim_style)?,
                    segments: self.read_segments(segment_count)?,
                })
            }

            CmdId::DrawLines => {
                let line_count = self.read_count()?;

                Some(CmdReader::DrawLines {
                    line_style: self.read_style(prim_style)?,
                    width: self.read_unit()?,
                    lines: self.read_lines(line_count),
                })
            }

            CmdId::DrawLoop => {
                let point_count = self.read_count()?;
                Some(CmdReader::DrawLoop {
                    line_style: self.read_style(prim_style)?,
                    width: self.read_unit()?,
                    points: self.read_points(point_count),
                })
            }

            CmdId::DrawStrip => {
                let point_count = self.read_count()?;

                Some(CmdReader::DrawStrip {
                    line_style: self.read_style(prim_style)?,
                    width: self.read_unit()?,
                    points: self.read_points(point_count),
                })
            }

            CmdId::DrawPath => {
                let segment_count = self.read_count()?;

                Some(CmdReader::DrawPath {
                    line_style: self.read_style(prim_style)?,
                    width: self.read_unit()?,
                    segments: self.read_segments(segment_count)?,
                })
            }

            CmdId::OutlineFillPoly => {
                let head = self.tvg.reader.read_u8()?;
                let point_count: u32 = (head.bits(0, 6) + 1).into();
                let line_style_id = StyleId::try_from(head.bits(6, 2))?;

                Some(CmdReader::OutlineFillPoly {
                    fill_style: self.read_style(prim_style)?,
                    line_style: self.read_style(line_style_id)?,
                    line_width: self.read_unit()?,
                    points: self.read_points(point_count),
                })
            }

            CmdId::OutlineFillRects => {
                let head = self.tvg.reader.read_u8()?;
                let rect_count: u32 = (head.bits(0, 6) + 1).into();
                let line_style_id = StyleId::try_from(head.bits(6, 2))?;

                Some(CmdReader::OutlineFillRects {
                    fill_style: self.read_style(prim_style)?,
                    line_style: self.read_style(line_style_id)?,
                    line_width: self.read_unit()?,
                    rects: self.read_rects(rect_count),
                })
            }

            CmdId::OutlineFillPath => {
                let head = self.tvg.reader.read_u8()?;
                let segment_count: u32 = (head.bits(0, 6) + 1).into();
                let line_style_id = StyleId::try_from(head.bits(6, 2))?;

                Some(CmdReader::OutlineFillPath {
                    fill_style: self.read_style(prim_style)?,
                    line_style: self.read_style(line_style_id)?,
                    line_width: self.read_unit()?,
                    segments: self.read_segments(segment_count)?,
                })
            }
        };

        Ok(cmd)
    }
}

/// A TinyVG data stream reader.
pub struct TinyVgReader<R: Read> {
    header: Option<TinyVgHeader>,
    colors_read: u32,
    commands_finished: bool,
    reader: R,
}

impl<R: Read> TinyVgReader<R> {
    /// Constructs a new `TinyVgReader` wrapping a reader.
    pub fn new(reader: R) -> TinyVgReader<R> {
        TinyVgReader {
            header: None,
            colors_read: 0,
            commands_finished: false,
            reader,
        }
    }

    /// Reads the TinyVG header.
    ///
    /// # Errors
    ///
    /// This method returns an error if the TinyVG header has already been read.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use std::fs::File;
    /// use tinyvg::TinyVgReader;
    ///
    /// let mut r = TinyVgReader::new(File::open("example.tvg")?);
    ///
    /// // Reading the header at the start of the data succeeds.
    /// assert!(r.read_header().is_ok());
    ///
    /// // Attempting to read the header again fails.
    /// assert!(r.read_header().is_err());
    ///
    /// # Ok(())
    /// # }
    /// ```
    pub fn read_header(&mut self) -> Result<TinyVgHeader> {
        match self.header {
            Some(_) => Err(TinyVgError {
                kind: ErrorKind::BadPosition,
                msg: "reader not positioned at beginning of data",
            }),
            None => {
                let header = read_header(&mut self.reader)?;
                self.header = Some(header);
                Ok(header)
            }
        }
    }

    /// Begins reading the color table.
    ///
    /// The returned [`ColorTableEncoding`] can be pattern-matched to handle
    /// each possible encoding differently. If this is not desired, the standard
    /// encodings can be converted to RGBAF32 using
    /// [`ColorTableEncoding::to_rgba_f32`].
    ///
    /// # Example
    ///
    /// ```no_run
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use std::fs::File;
    /// use tinyvg::{RgbaF32, TinyVgReader};
    ///
    /// let mut r = TinyVgReader::new(File::open("example.tvg")?);
    /// let header = r.read_header()?;
    ///
    /// let colors: Vec<RgbaF32> = r.read_color_table()?
    ///     .to_rgba_f32()
    ///     .collect::<Result<_, _>>()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn read_color_table(&mut self) -> Result<ColorTableEncoding<R, ()>> {
        self.read_custom_color_table::<()>()
    }

    pub fn read_custom_color_table<C: ColorEncoding>(
        &mut self,
    ) -> Result<ColorTableEncoding<R, C>> {
        let header = match self.header {
            Some(header) => header,
            None => {
                return Err(TinyVgError {
                    kind: ErrorKind::BadPosition,
                    msg: "reader not positioned at beginning of color table",
                });
            }
        };

        if self.colors_read >= header.color_count {
            return Err(TinyVgError {
                kind: ErrorKind::BadPosition,
                msg: "color table has already been read",
            });
        }

        let enc = match header.encoding {
            ColorEncodingTag::Rgba8888 => {
                ColorTableEncoding::Rgba8888(ColorTableEntries::new(self))
            }
            ColorEncodingTag::Rgb565 => ColorTableEncoding::Rgb565(ColorTableEntries::new(self)),
            ColorEncodingTag::RgbaF32 => ColorTableEncoding::RgbaF32(ColorTableEntries::new(self)),
            ColorEncodingTag::Custom => ColorTableEncoding::Custom(ColorTableEntries::new(self)),
        };

        Ok(enc)
    }

    pub fn read_commands(&mut self) -> Result<CommandReader<R>> {
        let header = match self.header {
            Some(header) => header,
            None => {
                return Err(TinyVgError {
                    kind: ErrorKind::BadPosition,
                    msg: "reader not positioned at beginning of commands",
                });
            }
        };

        if self.commands_finished {
            return Err(TinyVgError {
                kind: ErrorKind::BadPosition,
                msg: "all commands have already been read",
            });
        }

        Ok(CommandReader {
            errored: false,
            header,
            read_unit_fn: header.range.read_fn(),
            tvg: self,
        })
    }

    pub fn finish(self) -> std::result::Result<R, Self> {
        if self.commands_finished {
            Ok(self.reader)
        } else {
            Err(self)
        }
    }
}

fn read_header<R: Read>(mut reader: R) -> Result<TinyVgHeader> {
    let magic = {
        let mut m = [0u8; 2];
        reader.read_exact(&mut m)?;
        m
    };

    if magic != MAGIC {
        return Err(TinyVgError {
            kind: ErrorKind::InvalidData,
            msg: "incorrect magic number",
        });
    }

    let version = reader.read_u8()?;

    if version != VERSION {
        return Err(TinyVgError {
            kind: ErrorKind::InvalidData,
            msg: "incorrect version number",
        });
    }

    let scale_enc_range = reader.read_u8()?;
    let scale = scale_enc_range.bits(0, 4);
    let encoding = scale_enc_range.bits(4, 2).try_into()?;
    let range: CoordinateRange = scale_enc_range.bits(6, 2).try_into()?;

    // Select the appropriate read function for the coordinate range.
    let read_unit_fn = range.read_fn::<R>();

    let width = read_unit_fn(&mut reader)?
        .try_into()
        .map_err(|_| ErrorKind::InvalidData)?;
    let height = read_unit_fn(&mut reader)?
        .try_into()
        .map_err(|_| ErrorKind::InvalidData)?;

    let color_count = reader.read_var_u32()?;

    Ok(TinyVgHeader {
        scale,
        encoding,
        range,
        width,
        height,
        color_count,
    })
}

// TinyVG writing =================================================================================

pub struct TinyVgWriter<W: Write> {
    writer: W,
}

impl<W: Write> TinyVgWriter<W> {
    pub fn new(writer: W) -> TinyVgWriter<W> {
        TinyVgWriter { writer }
    }

    pub fn write_header(mut self, header: TinyVgHeader) -> Result<ColorTableWriter<W>> {
        self.writer.write_all(&MAGIC)?;
        self.writer.write_u8(VERSION)?;

        let params = (header.range as u8) << 6 | (header.encoding as u8) << 4 | header.scale as u8;
        self.writer.write_u8(params)?;

        let write_unit_fn = header.range.write_fn();
        write_unit_fn(
            &mut self.writer,
            header.width.try_into().map_err(|_| ErrorKind::OutOfRange)?,
        )?;
        write_unit_fn(
            &mut self.writer,
            header
                .height
                .try_into()
                .map_err(|_| ErrorKind::OutOfRange)?,
        )?;

        Ok(ColorTableWriter {
            header,
            writer: self.writer,
        })
    }
}

pub struct ColorTableWriter<W: Write> {
    header: TinyVgHeader,
    writer: W,
}

impl<W: Write> ColorTableWriter<W> {
    pub fn write_color_table<I, C>(mut self, colors: I) -> Result<CommandWriter<W>>
    where
        I: ExactSizeIterator<Item = C>,
        C: ColorEncoding,
    {
        if C::tag() != self.header.encoding {
            return Err(TinyVgError {
                kind: ErrorKind::InvalidData,
                msg: "color table writer encoding does not match header",
            });
        }

        let color_count: u32 = colors.len().try_into().map_err(|_| ErrorKind::OutOfRange)?;

        self.writer.write_var_u32(color_count)?;

        let mut written: u32 = 0;
        for color in colors {
            color.write_table_entry(&mut self.writer)?;
            written = written.checked_add(1).ok_or(ErrorKind::OutOfRange)?;

            if written > color_count {
                return Err(TinyVgError {
                    kind: ErrorKind::InvalidData,
                    msg: "number of colors written did not match provided iterator length",
                });
            }
        }

        let write_unit_fn = self.header.range.write_fn();

        Ok(CommandWriter {
            header: self.header,
            color_count,
            write_unit_fn,
            writer: self.writer,
        })
    }
}

pub struct CommandWriter<W: Write> {
    header: TinyVgHeader,
    color_count: u32,
    write_unit_fn: fn(&mut W, i32) -> Result<()>,
    writer: W,
}

impl<W: Write> CommandWriter<W> {
    fn write_unit(&mut self, unit: f32) -> Result<()> {
        let unscaled = unit * (1 << self.header.scale) as f32;

        // TODO: Casting to i32 will clamp values to [i32::MIN, i32::MAX].
        // It's probably preferable to range check the unscaled value directly
        // with the supported coordinate range and potentially error out.
        (self.write_unit_fn)(&mut self.writer, unscaled as i32)?;

        Ok(())
    }

    fn write_count(&mut self, count: usize) -> Result<()> {
        let as_u32: u32 = count.try_into().map_err(|_| ErrorKind::OutOfRange)?;
        self.writer
            .write_var_u32(as_u32.checked_sub(1).ok_or(ErrorKind::InvalidData)?)?;

        Ok(())
    }

    const U6_MAX: u8 = (1 << 6) - 1;
    fn write_styled_count(&mut self, count: usize, style_id: StyleId) -> Result<()> {
        let count = count.checked_sub(1).ok_or(TinyVgError {
            kind: ErrorKind::InvalidData,
            msg: "count must be at least 1",
        })?;

        if count > Self::U6_MAX as usize {
            return Err(TinyVgError {
                kind: ErrorKind::OutOfRange,
                msg: "count too high for this command type",
            });
        }

        self.writer
            .write_u8((style_id as u8) << 6 | (count as u8))?;

        Ok(())
    }

    fn write_point(&mut self, point: Point) -> Result<()> {
        self.write_unit(point.x)?;
        self.write_unit(point.y)?;

        Ok(())
    }

    fn write_points<P>(&mut self, points: P) -> Result<()>
    where
        P: ExactSizeIterator<Item = Point>,
    {
        for point in points {
            self.write_point(point)?;
        }

        Ok(())
    }

    fn write_line(&mut self, line: Line) -> Result<()> {
        self.write_point(line.start)?;
        self.write_point(line.end)?;

        Ok(())
    }

    fn write_lines<L>(&mut self, lines: L) -> Result<()>
    where
        L: ExactSizeIterator<Item = Line>,
    {
        for line in lines {
            self.write_line(line)?;
        }

        Ok(())
    }

    fn write_rect(&mut self, rect: Rect) -> Result<()> {
        self.write_unit(rect.x)?;
        self.write_unit(rect.y)?;
        self.write_unit(rect.width)?;
        self.write_unit(rect.height)?;

        Ok(())
    }

    fn write_rects<R>(&mut self, rects: R) -> Result<()>
    where
        R: ExactSizeIterator<Item = Rect>,
    {
        for rect in rects {
            self.write_rect(rect)?;
        }

        Ok(())
    }

    fn write_style(&mut self, style: Style) -> Result<()> {
        match style {
            Style::FlatColor { color } => {
                if color >= self.color_count {
                    return Err(ErrorKind::NoSuchColor.into());
                }

                self.writer.write_var_u32(color)?;
            }
            Style::LinearGradient {
                start,
                end,
                start_color,
                end_color,
            }
            | Style::RadialGradient {
                start,
                end,
                start_color,
                end_color,
            } => {
                if start_color >= self.color_count || end_color >= self.color_count {
                    return Err(ErrorKind::NoSuchColor.into());
                }

                self.write_point(start)?;
                self.write_point(end)?;
                self.writer.write_var_u32(start_color)?;
                self.writer.write_var_u32(end_color)?;
            }
        }

        Ok(())
    }

    fn write_path_instr(&mut self, instr: PathInstr) -> Result<()> {
        let (has_width, width) = match instr.line_width {
            Some(w) => (true, w),
            None => (false, 0.0),
        };

        match instr.kind {
            PathInstrKind::Line { to } => {
                self.writer
                    .write_u8(PathInstrId::Line.with_line_width(has_width))?;
                if has_width {
                    self.write_unit(width)?;
                }
                self.write_point(to)?;
            }

            PathInstrKind::HorizontalLine { to_x } => {
                self.writer
                    .write_u8(PathInstrId::HorizontalLine.with_line_width(has_width))?;
                if has_width {
                    self.write_unit(width)?;
                }
                self.write_unit(to_x)?;
            }

            PathInstrKind::VerticalLine { to_y } => {
                self.writer
                    .write_u8(PathInstrId::VerticalLine.with_line_width(has_width))?;
                if has_width {
                    self.write_unit(width)?;
                }
                self.write_unit(to_y)?;
            }

            PathInstrKind::CubicBezier {
                control_0,
                control_1,
                to,
            } => {
                self.writer
                    .write_u8(PathInstrId::CubicBezier.with_line_width(has_width))?;
                if has_width {
                    self.write_unit(width)?;
                }
                self.write_point(control_0)?;
                self.write_point(control_1)?;
                self.write_point(to)?;
            }

            PathInstrKind::ArcCircle {
                large_arc,
                sweep,
                radius,
                to,
            } => {
                self.writer
                    .write_u8(PathInstrId::ArcCircle.with_line_width(has_width))?;
                if has_width {
                    self.write_unit(width)?;
                }
                let flags = (sweep as u8) << 1 | large_arc as u8;
                self.writer.write_u8(flags)?;
                self.write_unit(radius)?;
                self.write_point(to)?;
            }

            PathInstrKind::ArcEllipse {
                large_arc,
                sweep,
                radius_x,
                radius_y,
                rotation_deg,
                to,
            } => {
                self.writer
                    .write_u8(PathInstrId::ArcEllipse.with_line_width(has_width))?;
                if has_width {
                    self.write_unit(width)?;
                }
                let flags = (sweep as u8) << 1 | large_arc as u8;
                self.writer.write_u8(flags)?;
                self.write_unit(radius_x)?;
                self.write_unit(radius_y)?;
                self.write_unit(rotation_deg)?;
                self.write_point(to)?;
            }

            PathInstrKind::Close => {
                self.writer
                    .write_u8(PathInstrId::Close.with_line_width(has_width))?;
                if has_width {
                    self.write_unit(width)?;
                }
            }

            PathInstrKind::QuadraticBezier { control, to } => {
                self.writer
                    .write_u8(PathInstrId::QuadraticBezier.with_line_width(has_width))?;
                if has_width {
                    self.write_unit(width)?;
                }
                self.write_point(control)?;
                self.write_point(to)?;
            }
        }

        Ok(())
    }

    fn write_segment(&mut self, segment: Segment) -> Result<()> {
        self.write_count(segment.instrs.len())?;
        self.write_point(segment.start)?;
        for instr in segment.instrs {
            self.write_path_instr(instr)?;
        }

        Ok(())
    }

    fn write_segments(&mut self, segments: Vec<Segment>) -> Result<()> {
        for segment in segments {
            self.write_segment(segment)?;
        }

        Ok(())
    }

    pub fn write_command(&mut self, command: Cmd) -> Result<()> {
        match command {
            Cmd::FillPoly { fill_style, points } => {
                self.writer
                    .write_u8(CmdId::FillPoly.with_style_id(fill_style.id()))?;
                self.write_count(points.len())?;
                self.write_style(fill_style)?;
                self.write_points(points.into_iter())?;
            }

            Cmd::FillRects { fill_style, rects } => {
                self.writer
                    .write_u8(CmdId::FillRects.with_style_id(fill_style.id()))?;
                self.write_count(rects.len())?;
                self.write_style(fill_style)?;
                self.write_rects(rects.into_iter())?;
            }

            Cmd::FillPath {
                fill_style,
                segments,
            } => {
                self.writer
                    .write_u8(CmdId::FillPath.with_style_id(fill_style.id()))?;
                self.write_count(segments.len())?;
                self.write_style(fill_style)?;
                self.write_segments(segments)?;
            }

            Cmd::DrawLines {
                line_style,
                width,
                lines,
            } => {
                self.writer
                    .write_u8(CmdId::DrawLines.with_style_id(line_style.id()))?;
                self.write_count(lines.len())?;
                self.write_style(line_style)?;
                self.write_unit(width)?;
                self.write_lines(lines.into_iter())?;
            }

            Cmd::DrawLoop {
                line_style,
                width,
                points,
            } => {
                self.writer
                    .write_u8(CmdId::DrawLoop.with_style_id(line_style.id()))?;
                self.write_count(points.len())?;
                self.write_style(line_style)?;
                self.write_unit(width)?;
                self.write_points(points.into_iter())?;
            }

            Cmd::DrawStrip {
                line_style,
                width,
                points,
            } => {
                self.writer
                    .write_u8(CmdId::DrawStrip.with_style_id(line_style.id()))?;
                self.write_count(points.len())?;
                self.write_style(line_style)?;
                self.write_unit(width)?;
                self.write_points(points.into_iter())?;
            }

            Cmd::DrawPath {
                line_style,
                width,
                segments,
            } => {
                self.writer
                    .write_u8(CmdId::DrawPath.with_style_id(line_style.id()))?;
                self.write_count(segments.len())?;
                self.write_style(line_style)?;
                self.write_unit(width)?;
                self.write_segments(segments)?;
            }

            Cmd::OutlineFillPoly {
                fill_style,
                line_style,
                line_width,
                points,
            } => {
                self.writer
                    .write_u8(CmdId::OutlineFillPoly.with_style_id(fill_style.id()))?;
                self.write_styled_count(points.len(), line_style.id())?;
                self.write_style(fill_style)?;
                self.write_style(line_style)?;
                self.write_unit(line_width)?;
                self.write_points(points.into_iter())?;
            }

            Cmd::OutlineFillRects {
                fill_style,
                line_style,
                line_width,
                rects,
            } => {
                self.writer
                    .write_u8(CmdId::OutlineFillRects.with_style_id(fill_style.id()))?;
                self.write_styled_count(rects.len(), line_style.id())?;
                self.write_style(fill_style)?;
                self.write_style(line_style)?;
                self.write_unit(line_width)?;
                self.write_rects(rects.into_iter())?;
            }

            Cmd::OutlineFillPath {
                fill_style,
                line_style,
                line_width,
                segments,
            } => {
                self.writer
                    .write_u8(CmdId::OutlineFillPath.with_style_id(fill_style.id()))?;
                self.write_styled_count(segments.len(), line_style.id())?;
                self.write_style(fill_style)?;
                self.write_style(line_style)?;
                self.write_unit(line_width)?;
                self.write_segments(segments)?;
            }
        }

        Ok(())
    }

    pub fn finish(mut self) -> Result<W> {
        self.writer.write_u8(0)?;
        Ok(self.writer)
    }
}

/// A convenience trait for extracting bitfields.
trait Uint:
    BitAnd<Output = Self> + Sized + Shl<u8, Output = Self> + Shr<u8, Output = Self> + Sub<Output = Self>
{
    const ONE: Self;
    const BITS: u32;

    fn bits(self, ofs: u8, width: u8) -> Self {
        assert!((ofs as u32) < Self::BITS);
        assert!((ofs as u32 + width as u32) <= Self::BITS);
        self.shr(ofs) & (Self::ONE.shl(width) - Self::ONE)
    }
}

impl Uint for u8 {
    const ONE: Self = 1;
    const BITS: u32 = u8::BITS;
}

impl Uint for u16 {
    const ONE: Self = 1;
    const BITS: u32 = u16::BITS;
}

impl Uint for u32 {
    const ONE: Self = 1;
    const BITS: u32 = u32::BITS;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extract_bits() {
        let value: u32 = 0xDEADBEEF;

        assert_eq!(value.bits(0, 16), 0xBEEF);
        assert_eq!(value.bits(8, 16), 0xADBE);
        assert_eq!(value.bits(16, 16), 0xDEAD);
        assert_eq!(value.bits(1, 31), 0x6F56DF77);
    }

    #[test]
    fn roundtrip_var_u32() {
        let values = [
            0,
            (1 << 7) - 1,
            1 << 7,
            (1 << 14) - 1,
            1 << 14,
            (1 << 21) - 1,
            1 << 21,
            (1 << 28) - 1,
            1 << 28,
            u32::MAX,
        ];

        let mut buf = [0u8; 5];
        for value in values {
            (&mut buf[..]).write_var_u32(value).unwrap();
            let read = (&buf[..]).read_var_u32().unwrap();
            assert_eq!(read, value);
        }
    }
}
