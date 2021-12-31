use std::fs::File;

use tinyvg::{
    ArcSweep, Cmd, ColorEncodingTag, CoordinateRange, PathInstr, PathInstrKind, Point, Rect,
    Rgba8888, Segment, Style, TinyVgHeader, TinyVgWriter,
};

pub fn main() -> tinyvg::Result<()> {
    let w = TinyVgWriter::new(File::create("shapes.tvg")?);
    let header = TinyVgHeader {
        scale: 0,
        encoding: ColorEncodingTag::Rgba8888,
        range: CoordinateRange::Default,
        width: 360,
        height: 120,
        color_count: 3,
    };

    let table_writer = w.write_header(header)?;
    let mut cmd_writer = table_writer.write_color_table(
        [
            Rgba8888 {
                red: 192,
                green: 0,
                blue: 0,
                alpha: 255,
            },
            Rgba8888 {
                red: 0,
                green: 192,
                blue: 0,
                alpha: 255,
            },
            Rgba8888 {
                red: 0,
                green: 0,
                blue: 192,
                alpha: 255,
            },
        ]
        .into_iter(),
    )?;

    cmd_writer.write_command(Cmd::FillRects {
        fill_style: Style::FlatColor { color: 0 },
        rects: vec![Rect {
            x: 10.0,
            y: 10.0,
            width: 100.0,
            height: 100.0,
        }],
    })?;

    cmd_writer.write_command(Cmd::FillPath {
        fill_style: Style::FlatColor { color: 1 },
        segments: vec![Segment {
            start: Point { x: 130.0, y: 60.0 },
            instrs: vec![PathInstr {
                kind: PathInstrKind::ArcCircle {
                    large_arc: true,
                    sweep: ArcSweep::Cw,
                    radius: 50.0,
                    to: Point { x: 180.0, y: 10.0 },
                },
                line_width: None,
            }],
        }],
    })?;

    cmd_writer.write_command(Cmd::FillPoly {
        fill_style: Style::FlatColor { color: 2 },
        points: vec![
            Point { x: 190.0, y: 110.0 },
            Point { x: 210.0, y: 10.0 },
            Point { x: 230.0, y: 110.0 },
        ],
    })?;

    cmd_writer.finish()?;

    Ok(())
}
