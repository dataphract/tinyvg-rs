use cgmath::{InnerSpace, Point2};
use piet_common::{
    kurbo::{self, BezPath},
    Color, Device, FixedLinearGradient, FixedRadialGradient, GradientStop, LineCap, LineJoin,
    PaintBrush, RenderContext, StrokeStyle,
};
use tinyvg::{ArcSweep, RgbaF32};

const STROKE_STYLE: StrokeStyle = StrokeStyle::new()
    .line_join(LineJoin::Round)
    .line_cap(LineCap::Round);

trait RgbaF32Ext {
    fn to_color(self) -> Color;
}

impl RgbaF32Ext for RgbaF32 {
    fn to_color(self) -> Color {
        Color::rgba(
            self.red().into(),
            self.green().into(),
            self.blue().into(),
            self.alpha().into(),
        )
    }
}

trait PointExt {
    fn to_kurbo(self) -> kurbo::Point;
}

impl PointExt for tinyvg::Point {
    fn to_kurbo(self) -> kurbo::Point {
        kurbo::Point {
            x: self.x.into(),
            y: self.y.into(),
        }
    }
}

trait RectExt {
    fn to_kurbo(self) -> kurbo::Rect;
}

impl RectExt for tinyvg::Rect {
    fn to_kurbo(self) -> kurbo::Rect {
        kurbo::Rect {
            x0: self.x.into(),
            y0: self.y.into(),
            x1: (self.x + self.width).into(),
            y1: (self.y + self.height).into(),
        }
    }
}

fn style_to_paint(style: tinyvg::Style, colors: &[tinyvg::RgbaF32]) -> PaintBrush {
    use tinyvg::Style;

    match style {
        Style::FlatColor { color } => colors[color as usize].to_color().into(),
        Style::LinearGradient {
            start,
            end,
            start_color,
            end_color,
        } => FixedLinearGradient {
            start: start.to_kurbo(),
            end: end.to_kurbo(),
            stops: vec![
                GradientStop {
                    pos: 0.0,
                    color: colors[start_color as usize].to_color(),
                },
                GradientStop {
                    pos: 1.0,
                    color: colors[end_color as usize].to_color(),
                },
            ],
        }
        .into(),
        Style::RadialGradient {
            start,
            end,
            start_color,
            end_color,
        } => FixedRadialGradient {
            center: start.to_kurbo(),
            origin_offset: kurbo::Vec2::ZERO,
            radius: ((end.x - start.x).powi(2) + (end.y - start.y).powi(2))
                .sqrt()
                .into(),
            stops: vec![
                GradientStop {
                    pos: 0.0,
                    color: colors[start_color as usize].to_color(),
                },
                GradientStop {
                    pos: 1.0,
                    color: colors[end_color as usize].to_color(),
                },
            ],
        }
        .into(),
    }
}

pub fn strip_path(
    mut points: impl Iterator<Item = tinyvg::Result<tinyvg::Point>>,
) -> tinyvg::Result<BezPath> {
    let mut path = BezPath::new();

    let first = points.next().unwrap()?;
    path.move_to(first.to_kurbo());

    for point in points {
        path.line_to(point?.to_kurbo());
    }

    Ok(path)
}

pub fn poly_path(
    mut points: impl Iterator<Item = tinyvg::Result<tinyvg::Point>>,
) -> tinyvg::Result<BezPath> {
    let mut path = BezPath::new();

    let first = points.next().unwrap()?;
    path.move_to(first.to_kurbo());

    for point in points {
        path.line_to(point?.to_kurbo());
    }

    path.close_path();
    Ok(path)
}

pub fn lines_path(
    lines: impl Iterator<Item = tinyvg::Result<tinyvg::Line>>,
) -> tinyvg::Result<BezPath> {
    let mut path = BezPath::new();

    for line in lines {
        let tinyvg::Line { start, end } = line?;
        path.move_to(start.to_kurbo());
        path.line_to(end.to_kurbo());
    }

    Ok(path)
}

#[allow(clippy::too_many_arguments)]
fn elliptic_to(
    path: &mut BezPath,
    pos: &mut kurbo::Point,
    to: tinyvg::Point,
    large_arc: bool,
    sweep: ArcSweep,
    radius_x: f32,
    radius_y: f32,
    angle: f32,
) -> tinyvg::Result<()> {
    if angle != 0.0 {
        todo!("elliptic arcs with a rotation not handled yet :(");
    }

    let alpha_1 = (-pos.x as f32 + to.x) / (2.0 * radius_x);
    let alpha_2 = (pos.y as f32 - to.y) / (2.0 * radius_y);
    let alpha_ratio = alpha_1 / alpha_2;

    let beta_1 = alpha_ratio.atan();
    let beta_2 = (alpha_2 * (1.0 + alpha_ratio.powi(2)).sqrt()).asin();

    let theta_1 = beta_1 + beta_2;
    let theta_2 = beta_1 - beta_2;

    let x_ofs = radius_x * theta_1.cos();
    let y_ofs = radius_y * theta_1.sin();
    let center = match (large_arc, sweep) {
        (true, ArcSweep::Cw) | (false, ArcSweep::Ccw) => Point2 {
            x: pos.x as f32 - x_ofs,
            y: pos.y as f32 - y_ofs,
        },
        (true, ArcSweep::Ccw) | (false, ArcSweep::Cw) => Point2 {
            x: pos.x as f32 + x_ofs,
            y: pos.y as f32 + y_ofs,
        },
    };

    let arc_angle = theta_2 - theta_1;
    let k = (4.0 / 3.0) * (arc_angle / 4.0).tan();
    let control_0 = kurbo::Point {
        x: (center.x + radius_x * theta_1.cos() + k * radius_y * theta_1.sin()).into(),
        y: (center.y + radius_y * theta_1.sin() + k * radius_x * theta_1.cos()).into(),
    };
    let control_1 = kurbo::Point {
        x: (center.x + radius_x * theta_2.cos() + k * radius_y * theta_2.sin()).into(),
        y: (center.y + radius_y * theta_2.sin() + k * radius_x * theta_2.cos()).into(),
    };

    path.curve_to(control_0, control_1, to.to_kurbo());
    *pos = to.to_kurbo();

    Ok(())
}

fn arc_to(
    path: &mut BezPath,
    pos: &mut kurbo::Point,
    to: tinyvg::Point,
    large_arc: bool,
    sweep: ArcSweep,
    radius: f32,
) -> tinyvg::Result<()> {
    // Invert y-coordinates to account for coordinate system
    let start: Point2<f32> = Point2 {
        x: pos.x as f32,
        y: -pos.y as f32,
    };
    let end = Point2 {
        x: to.x as f32,
        y: -to.y as f32,
    };

    let chord_halfvec = (end - start) / 2.0;
    let chord_halfmag = chord_halfvec.magnitude();

    println!("chord_halfmag: {}", chord_halfmag);

    // TODO: reject distances close to zero as well
    if chord_halfmag == 0.0 {
        // TODO: proper error
        panic!("too close to zero");
    }

    // TODO: use an epsilon
    if chord_halfmag > radius {
        // TODO: proper error
        panic!("impossible arc");
    } else if chord_halfmag == radius {
        todo!("special case, only one arc for each sweep");
    }

    let chord_angle = (chord_halfvec.x / chord_halfmag).acos();
    println!("chord_angle = {}°", chord_angle.to_degrees());
    // There are two possible center points. Where Θ is the angle
    // between the chord and the radius which ends at the start
    // point:
    //
    // cosΘ = chord_halfmag / radius
    // Θ = arccos(chord_halfmag / radius)
    let off_angle = (chord_halfmag / radius).acos();
    println!("off_angle = ±{}°", off_angle.to_degrees());

    // Calculate angle from start to center.
    let refl_start_angle = match (large_arc, sweep) {
        (true, ArcSweep::Ccw) | (false, ArcSweep::Cw) => -(chord_angle + off_angle),
        (true, ArcSweep::Cw) | (false, ArcSweep::Ccw) => -(chord_angle - off_angle),
    };

    // Reflect that angle.
    let start_angle = std::f32::consts::PI - refl_start_angle;
    println!("start_angle = {}°", start_angle.to_degrees());

    let center = Point2 {
        x: start.x - radius * (-start_angle).cos(),
        y: start.y - radius * (-start_angle).sin(),
    };

    println!("center: {:?}", center);

    let to_end = end - center;
    let end_angle = to_end.y.atan2(to_end.x);
    println!("end_angle: {}°", end_angle.to_degrees());
    let arc_angle = end_angle - start_angle;
    println!("arc_angle: {}°", arc_angle.to_degrees());

    // Generate control points to approximate a circular arc using
    // Bezier curve black magic. The control points approximate an
    // arc with the given radius beginning at Θ = 0, so they need to
    // be rotated and then translated into place.
    let k = (4.0 / 3.0) * (arc_angle / 4.0).tan();
    println!("k = {}", k);
    let sc = start_angle.cos();
    let ss = start_angle.sin();
    let ec = end_angle.cos();
    let es = end_angle.sin();
    let control_0 = tinyvg::Point {
        x: center.x + radius * (sc + k * ss),
        y: -(center.y + radius * (ss + k * sc)),
    };
    let control_1 = tinyvg::Point {
        x: center.x + radius * (ec + k * es),
        y: -(center.y + radius * (es + k * ec)),
    };

    println!("c0: {:?}", control_0);
    println!("c1: {:?}", control_1);
    println!("end: {:?}", to);

    *pos = to.to_kurbo();
    path.curve_to(control_0.to_kurbo(), control_1.to_kurbo(), *pos);

    Ok(())
}

pub fn segment_path(segment: tinyvg::Segment) -> tinyvg::Result<BezPath> {
    use tinyvg::{PathInstr, PathInstrKind};

    let mut path = BezPath::new();

    // Keep track of the last point to allow horizontal and vertical lines.
    let mut pos = segment.start.to_kurbo();
    path.move_to(pos);

    for PathInstr {
        kind,
        line_width: _,
    } in segment.instrs
    {
        // TODO: handle line width. This will require splitting stroked paths into multiple paths.)
        match kind {
            PathInstrKind::Line { to } => {
                pos = to.to_kurbo();
                path.line_to(pos);
            }
            PathInstrKind::HorizontalLine { to_x } => {
                pos.x = to_x.into();
                path.line_to(pos);
            }
            PathInstrKind::VerticalLine { to_y } => {
                pos.y = to_y.into();
                path.line_to(pos);
            }
            PathInstrKind::CubicBezier {
                control_0,
                control_1,
                to,
            } => {
                pos = to.to_kurbo();
                path.curve_to(control_0.to_kurbo(), control_1.to_kurbo(), pos);
            }
            PathInstrKind::ArcCircle {
                large_arc,
                sweep,
                radius,
                to,
            } => {
                // TODO
                arc_to(&mut path, &mut pos, to, large_arc, sweep, radius)?;
            }

            PathInstrKind::ArcEllipse {
                large_arc,
                sweep,
                radius_x,
                radius_y,
                rotation_deg,
                to,
            } => {
                elliptic_to(
                    &mut path,
                    &mut pos,
                    to,
                    large_arc,
                    sweep,
                    radius_x,
                    radius_y,
                    rotation_deg.to_radians(),
                )
                .unwrap();
            }

            PathInstrKind::Close => {
                path.close_path();
            }

            PathInstrKind::QuadraticBezier { control, to } => {
                pos = to.to_kurbo();
                path.quad_to(control.to_kurbo(), pos);
            }
        }
    }

    Ok(path)
}

pub fn main() -> tinyvg::Result<()> {
    use std::fs::File;

    use tinyvg::{CmdReader, TinyVgReader};

    let mut r = TinyVgReader::new(File::open("example-files/files/everything-32.tvg")?);

    let header = r.read_header()?;
    let colors: Vec<RgbaF32> = r
        .read_color_table()?
        .to_rgba_f32()
        .collect::<tinyvg::Result<_>>()?;

    let mut dev = Device::new().unwrap();
    let mut target = dev
        .bitmap_target(header.width as usize, header.height as usize, 1.0)
        .unwrap();
    let mut cx = target.render_context();

    let mut cmds = r.read_commands()?;
    while let Some(cmd) = cmds.read_cmd()? {
        match cmd {
            CmdReader::FillPoly { fill_style, points } => {
                let paint = style_to_paint(fill_style, &colors);
                let path = poly_path(points)?;

                let _ = cx.fill(&path, &paint);
            }

            CmdReader::FillRects { fill_style, rects } => {
                let paint = style_to_paint(fill_style, &colors);

                for rect in rects {
                    cx.fill(rect?.to_kurbo(), &paint);
                }
            }

            CmdReader::FillPath {
                fill_style,
                segments,
            } => {
                let paint = style_to_paint(fill_style, &colors);
                for segment in segments {
                    cx.fill(&segment_path(segment?)?, &paint);
                }
            }

            CmdReader::DrawLines {
                line_style,
                width,
                lines,
            } => {
                let paint = style_to_paint(line_style, &colors);
                let path = lines_path(lines)?;
                cx.stroke_styled(&path, &paint, width.into(), &STROKE_STYLE);
            }

            CmdReader::DrawLoop {
                line_style,
                width,
                points,
            } => {
                let paint = style_to_paint(line_style, &colors);
                let path = poly_path(points)?;
                cx.stroke_styled(&path, &paint, width.into(), &STROKE_STYLE);
            }

            CmdReader::DrawStrip {
                line_style,
                width,
                points,
            } => {
                let paint = style_to_paint(line_style, &colors);
                let path = strip_path(points)?;
                cx.stroke_styled(&path, &paint, width.into(), &STROKE_STYLE);
            }

            CmdReader::DrawPath {
                line_style,
                width,
                segments,
            } => {
                let paint = style_to_paint(line_style, &colors);

                for segment in segments {
                    let path = segment_path(segment?)?;
                    cx.stroke_styled(&path, &paint, width.into(), &STROKE_STYLE);
                }
            }

            CmdReader::OutlineFillPoly {
                fill_style,
                line_style,
                line_width,
                points,
            } => {
                let fill_paint = style_to_paint(fill_style, &colors);
                let line_paint = style_to_paint(line_style, &colors);
                let path = poly_path(points)?;

                cx.fill(&path, &fill_paint);
                cx.stroke_styled(&path, &line_paint, line_width.into(), &STROKE_STYLE);
            }

            CmdReader::OutlineFillRects {
                fill_style,
                line_style,
                line_width,
                rects,
            } => {
                let fill_paint = style_to_paint(fill_style, &colors);
                let line_paint = style_to_paint(line_style, &colors);

                for rect in rects {
                    let rect = rect?.to_kurbo();
                    cx.fill(rect, &fill_paint);
                    cx.stroke_styled(&rect, &line_paint, line_width.into(), &STROKE_STYLE);
                }
            }

            CmdReader::OutlineFillPath {
                fill_style,
                line_style,
                line_width,
                segments,
            } => {
                let fill_paint = style_to_paint(fill_style, &colors);
                let line_paint = style_to_paint(line_style, &colors);

                for segment in segments {
                    let path = segment_path(segment?)?;
                    cx.fill(&path, &fill_paint);
                    cx.stroke_styled(&path, &line_paint, line_width.into(), &STROKE_STYLE);
                }
            }
        }
    }

    drop(cx);
    target.save_to_file("out.png").unwrap();

    Ok(())
}
