use std::{
    io::{self, Read, Write},
    iter,
    ops::{BitAnd, Shl, Shr, Sub},
};

use byteorder::{ReadBytesExt, LE};

const MAGIC: [u8; 2] = [0x72, 0x56];
const VERSION: u8 = 1;

#[derive(Debug)]
pub enum TinyVgError {
    Io(io::Error),
    InvalidData,
    Unsupported,
}

impl From<io::Error> for TinyVgError {
    fn from(e: io::Error) -> Self {
        TinyVgError::Io(e)
    }
}

// VarUInt encoding/decoding ======================================================================

trait ReadVarU32Ext: Read {
    fn read_var_u32(&mut self) -> io::Result<u32> {
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
        if b & 0xF0 != 0x80 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Invalid 5th byte in VarUInt encoding",
            ));
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

// Colors =========================================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ColorEncoding {
    Rgba8888 = 0,
    Rgb565 = 1,
    RgbaF32 = 2,
    Custom = 3,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rgba8888 {
    pub red: u8,
    pub green: u8,
    pub blue: u8,
    pub alpha: u8,
}

impl Rgba8888 {
    fn read_from<R: Read>(mut reader: R) -> io::Result<Rgba8888> {
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
}

impl From<Rgb565> for Rgba8888 {
    fn from(c: Rgb565) -> Self {
        let red = c.bytes[0].bits(0, 5);
        let green = c.bytes[1].bits(0, 3) << 3 | c.bytes[0].bits(5, 3);
        let blue = c.bytes[1].bits(3, 5);

        Rgba8888 {
            red,
            green,
            blue,
            alpha: 1,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rgb565 {
    bytes: [u8; 2],
}

impl Rgb565 {
    fn read_from<R: Read>(mut reader: R) -> io::Result<Rgb565> {
        let mut bytes = [0u8; 2];
        reader.read_exact(&mut bytes)?;

        Ok(Rgb565 { bytes })
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct RgbaF32 {
    red: f32,
    green: f32,
    blue: f32,
    alpha: f32,
}

impl RgbaF32 {
    fn read_from<R: Read>(mut reader: R) -> io::Result<RgbaF32> {
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
}

impl TryFrom<u8> for ColorEncoding {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<ColorEncoding, TinyVgError> {
        use ColorEncoding::*;
        match value {
            0 => Ok(Rgba8888),
            1 => Ok(Rgb565),
            2 => Ok(RgbaF32),
            3 => Ok(Custom),
            _ => Err(TinyVgError::InvalidData),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ColorTable {
    Rgba8888(Vec<Rgba8888>),
    Rgb565(Vec<Rgb565>),
    RgbaF32(Vec<RgbaF32>),
}

// Coordinates ====================================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoordinateRange {
    Default = 0,
    Reduced = 1,
    Enhanced = 2,
}

impl CoordinateRange {
    fn read_default<R: Read>(reader: &mut R) -> io::Result<i32> {
        reader.read_i16::<LE>().map(i16::into)
    }

    fn read_reduced<R: Read>(reader: &mut R) -> io::Result<i32> {
        reader.read_i8().map(i8::into)
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
}

impl TryFrom<u8> for CoordinateRange {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<CoordinateRange, TinyVgError> {
        use CoordinateRange::*;
        match value {
            0 => Ok(Default),
            1 => Ok(Reduced),
            2 => Ok(Enhanced),
            _ => Err(TinyVgError::InvalidData),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum StyleId {
    FlatColor = 0,
    LinearGradient = 1,
    RadialGradient = 2,
}

impl TryFrom<u8> for StyleId {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(StyleId::FlatColor),
            1 => Ok(StyleId::LinearGradient),
            2 => Ok(StyleId::RadialGradient),
            _ => Err(TinyVgError::InvalidData),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Style {
    FlatColor {
        color: u32,
    },
    LinearGradient {
        start: Point,
        end: Point,
        start_color: u32,
        end_color: u32,
    },
    RadialGradient {
        start: Point,
        end: Point,
        start_color: u32,
        end_color: u32,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Point {
    x: f32,
    y: f32,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Rect {
    x: f32,
    y: f32,
    width: f32,
    height: f32,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ArcSweep {
    Cw = 0,
    Ccw = 1,
}

impl TryFrom<u8> for ArcSweep {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(ArcSweep::Cw),
            1 => Ok(ArcSweep::Ccw),
            _ => Err(TinyVgError::InvalidData),
        }
    }
}

// Paths ==========================================================================================

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PathSegmentId {
    Line = 0,
    HorizontalLine = 1,
    VerticalLine = 2,
    CubicBezier = 3,
    ArcCircle = 4,
    ArcEllipse = 5,
    Close = 6,
    QuadraticBezier = 7,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SegmentKind {
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
pub struct Segment {
    kind: SegmentKind,
    line_width: Option<f32>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Path {
    start: Point,
    segments: Vec<Segment>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Line {
    start: Point,
    end: Point,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CmdId {
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

impl TryFrom<u8> for CmdId {
    type Error = TinyVgError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
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
            _ => return Err(TinyVgError::InvalidData),
        };

        Ok(cmd)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Cmd {
    EndOfDocument,
    FillPoly {
        fill_style: Style,
        polygon: Vec<Point>,
    },
    FillRects {
        fill_style: Style,
        rects: Vec<Rect>,
    },
    FillPath {
        fill_style: Style,
        path: Path,
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
        path: Path,
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
        path: Path,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TinyVgHeader {
    scale: u8,
    encoding: ColorEncoding,
    range: CoordinateRange,
    width: u32,
    height: u32,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TinyVg {
    header: TinyVgHeader,
    table: ColorTable,
    cmds: Vec<Cmd>,
}

/// A TinyVG data stream reader.
struct TinyVgReader<R: Read> {
    header: TinyVgHeader,
    read_unit_fn: fn(&mut R) -> io::Result<i32>,
    table: ColorTable,
    reader: R,
}

impl<R: Read> TinyVgReader<R> {
    fn read_style(&mut self, id: StyleId) -> Result<Style, TinyVgError> {
        let style = match id {
            StyleId::FlatColor => Style::FlatColor {
                color: self.reader.read_var_u32()?,
            },
            StyleId::LinearGradient => Style::LinearGradient {
                start: self.read_point()?,
                end: self.read_point()?,
                start_color: self.reader.read_var_u32()?,
                end_color: self.reader.read_var_u32()?,
            },
            StyleId::RadialGradient => Style::RadialGradient {
                start: self.read_point()?,
                end: self.read_point()?,
                start_color: self.reader.read_var_u32()?,
                end_color: self.reader.read_var_u32()?,
            },
        };

        Ok(style)
    }

    fn read_unit(&mut self) -> io::Result<f32> {
        let num = (self.read_unit_fn)(&mut self.reader)?;
        Ok(num as f32 / (1 << self.header.scale) as f32)
    }

    fn read_point(&mut self) -> Result<Point, TinyVgError> {
        let x = self.read_unit()?;
        let y = self.read_unit()?;

        Ok(Point { x, y })
    }

    fn read_points(&mut self, point_count: u32) -> Result<Vec<Point>, TinyVgError> {
        iter::repeat_with(|| self.read_point())
            .take(point_count as usize)
            .collect::<Result<Vec<_>, _>>()
    }

    fn read_line(&mut self) -> Result<Line, TinyVgError> {
        let start = self.read_point()?;
        let end = self.read_point()?;

        Ok(Line { start, end })
    }

    fn read_lines(&mut self, line_count: u32) -> Result<Vec<Line>, TinyVgError> {
        iter::repeat_with(|| self.read_line())
            .take(line_count as usize)
            .collect::<Result<Vec<_>, _>>()
    }

    fn read_rect(&mut self) -> Result<Rect, TinyVgError> {
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

    fn read_rects(&mut self, rect_count: u32) -> Result<Vec<Rect>, TinyVgError> {
        iter::repeat_with(|| self.read_rect())
            .take(rect_count as usize)
            .collect::<Result<Vec<_>, _>>()
    }

    fn read_segment(&mut self) -> Result<Segment, TinyVgError> {
        let tag = self.reader.read_u8()?;

        let instr = tag.bits(0, 3);
        let has_line_width = tag.bits(4, 1) == 1;

        let kind = match instr {
            0 => SegmentKind::Line {
                to: self.read_point()?,
            },
            1 => SegmentKind::HorizontalLine {
                to_x: self.read_unit()?,
            },
            2 => SegmentKind::VerticalLine {
                to_y: self.read_unit()?,
            },
            3 => SegmentKind::CubicBezier {
                control_0: self.read_point()?,
                control_1: self.read_point()?,
                to: self.read_point()?,
            },
            4 => {
                let flags = self.reader.read_u8()?;
                let large_arc = flags.bits(0, 1) == 1;
                let sweep = ArcSweep::try_from(flags.bits(1, 1))?;
                let radius = self.read_unit()?;
                let to = self.read_point()?;

                SegmentKind::ArcCircle {
                    large_arc,
                    sweep,
                    radius,
                    to,
                }
            }
            5 => {
                let flags = self.reader.read_u8()?;
                let large_arc = flags.bits(0, 1) == 1;
                let sweep = ArcSweep::try_from(flags.bits(1, 1))?;
                let radius_x = self.read_unit()?;
                let radius_y = self.read_unit()?;
                let rotation_deg = self.read_unit()?;
                let to = self.read_point()?;

                SegmentKind::ArcEllipse {
                    large_arc,
                    sweep,
                    radius_x,
                    radius_y,
                    rotation_deg,
                    to,
                }
            }
            6 => SegmentKind::Close,
            7 => SegmentKind::QuadraticBezier {
                control: self.read_point()?,
                to: self.read_point()?,
            },
            _ => return Err(TinyVgError::InvalidData),
        };

        let line_width = has_line_width.then(|| self.read_unit()).transpose()?;

        Ok(Segment { kind, line_width })
    }

    fn read_path(&mut self, segment_count: u32) -> Result<Path, TinyVgError> {
        let start = self.read_point()?;
        let segments = iter::repeat_with(|| self.read_segment())
            .take(segment_count as usize)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Path { start, segments })
    }

    fn read_cmd(&mut self) -> Result<Cmd, TinyVgError> {
        let tag = self.reader.read_u8()?;
        let id = CmdId::try_from(tag.bits(0, 6))?;
        let prim_style = StyleId::try_from(tag.bits(6, 2))?;

        let cmd = match id {
            CmdId::EndOfDocument => Cmd::EndOfDocument,

            CmdId::FillPoly => {
                let point_count = self.reader.read_var_u32()? + 1;
                Cmd::FillPoly {
                    fill_style: self.read_style(prim_style)?,
                    polygon: self.read_points(point_count)?,
                }
            }

            CmdId::FillRects => {
                let rect_count = self.reader.read_var_u32()? + 1;

                Cmd::FillRects {
                    fill_style: self.read_style(prim_style)?,
                    rects: self.read_rects(rect_count)?,
                }
            }

            CmdId::FillPath => {
                let segment_count = self.reader.read_var_u32()? + 1;

                Cmd::FillPath {
                    fill_style: self.read_style(prim_style)?,
                    path: self.read_path(segment_count)?,
                }
            }

            CmdId::DrawLines => {
                let line_count = self.reader.read_var_u32()? + 1;

                Cmd::DrawLines {
                    line_style: self.read_style(prim_style)?,
                    width: self.read_unit()?,
                    lines: self.read_lines(line_count)?,
                }
            }

            CmdId::DrawLoop => {
                let point_count = self.reader.read_var_u32()? + 1;
                Cmd::DrawLoop {
                    line_style: self.read_style(prim_style)?,
                    width: self.read_unit()?,
                    points: self.read_points(point_count)?,
                }
            }

            CmdId::DrawStrip => {
                let point_count = self.reader.read_var_u32()? + 1;

                Cmd::DrawStrip {
                    line_style: self.read_style(prim_style)?,
                    width: self.read_unit()?,
                    points: self.read_points(point_count)?,
                }
            }

            CmdId::DrawPath => {
                let segment_count = self.reader.read_var_u32()? + 1;

                Cmd::DrawPath {
                    line_style: self.read_style(prim_style)?,
                    width: self.read_unit()?,
                    path: self.read_path(segment_count)?,
                }
            }

            CmdId::OutlineFillPoly => {
                let head = self.reader.read_u8()?;
                let point_count: u32 = (head.bits(0, 6) + 1).into();
                let line_style_id = StyleId::try_from(head.bits(6, 2))?;

                Cmd::OutlineFillPoly {
                    fill_style: self.read_style(prim_style)?,
                    line_style: self.read_style(line_style_id)?,
                    line_width: self.read_unit()?,
                    points: self.read_points(point_count)?,
                }
            }

            CmdId::OutlineFillRects => {
                let head = self.reader.read_u8()?;
                let rect_count: u32 = (head.bits(0, 6) + 1).into();
                let line_style_id = StyleId::try_from(head.bits(6, 2))?;

                Cmd::OutlineFillRects {
                    fill_style: self.read_style(prim_style)?,
                    line_style: self.read_style(line_style_id)?,
                    line_width: self.read_unit()?,
                    rects: self.read_rects(rect_count)?,
                }
            }

            CmdId::OutlineFillPath => {
                let head = self.reader.read_u8()?;
                let segment_count: u32 = (head.bits(0, 6) + 1).into();
                let line_style_id = StyleId::try_from(head.bits(6, 2))?;

                Cmd::OutlineFillPath {
                    fill_style: self.read_style(prim_style)?,
                    line_style: self.read_style(line_style_id)?,
                    line_width: self.read_unit()?,
                    path: self.read_path(segment_count)?,
                }
            }
        };

        Ok(cmd)
    }
}

pub fn parse<R: Read>(mut reader: R) -> Result<TinyVg, TinyVgError> {
    let magic = {
        let mut m = [0u8; 2];
        reader.read_exact(&mut m)?;
        m
    };

    if magic != MAGIC {
        return Err(TinyVgError::InvalidData);
    }

    let version = reader.read_u8()?;

    if version != VERSION {
        return Err(TinyVgError::InvalidData);
    }

    let scale_enc_range = reader.read_u8()?;
    let scale = scale_enc_range.bits(0, 4);
    let encoding = scale_enc_range.bits(4, 2).try_into()?;
    let range: CoordinateRange = scale_enc_range.bits(6, 2).try_into()?;

    // Select the appropriate read function for the coordinate range.
    let read_unit_fn = range.read_fn::<R>();

    let width: u32 = read_unit_fn(&mut reader)?
        .try_into()
        .map_err(|_| TinyVgError::InvalidData)?;
    let height = read_unit_fn(&mut reader)?
        .try_into()
        .map_err(|_| TinyVgError::InvalidData)?;

    let header = TinyVgHeader {
        scale,
        encoding,
        range,
        width,
        height,
    };

    let color_count = reader.read_var_u32()?;
    let table = match encoding {
        ColorEncoding::Rgba8888 => {
            let values = iter::repeat_with(|| Rgba8888::read_from(&mut reader))
                .take(color_count as usize)
                .collect::<Result<Vec<_>, _>>()?;

            ColorTable::Rgba8888(values)
        }

        ColorEncoding::Rgb565 => {
            let values = iter::repeat_with(|| Rgb565::read_from(&mut reader))
                .take(color_count as usize)
                .collect::<Result<Vec<_>, _>>()?;

            ColorTable::Rgb565(values)
        }

        ColorEncoding::RgbaF32 => {
            let values = iter::repeat_with(|| RgbaF32::read_from(&mut reader))
                .take(color_count as usize)
                .collect::<Result<Vec<_>, _>>()?;

            ColorTable::RgbaF32(values)
        }

        ColorEncoding::Custom => return Err(TinyVgError::Unsupported),
    };

    let mut tvg_reader = TinyVgReader {
        header,
        table,
        read_unit_fn,
        reader,
    };

    let mut cmds = Vec::new();
    loop {
        let cmd = tvg_reader.read_cmd()?;

        if cmd == Cmd::EndOfDocument {
            break;
        }

        cmds.push(cmd);
    }

    Ok(TinyVg {
        header: tvg_reader.header,
        table: tvg_reader.table,
        cmds,
    })
}

/// A convenience trait for extracting bitfields.
trait Uint:
    BitAnd<Output = Self> + Sized + Shl<u8, Output = Self> + Shr<u8, Output = Self> + Sub<Output = Self>
{
    const ONE: Self;

    fn bits(self, ofs: u8, width: u8) -> Self {
        self.shr(ofs) & (Self::ONE.shl(width) - Self::ONE)
    }
}

impl Uint for u8 {
    const ONE: Self = 1;
}

impl Uint for u16 {
    const ONE: Self = 1;
}

impl Uint for u32 {
    const ONE: Self = 1;
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
}
