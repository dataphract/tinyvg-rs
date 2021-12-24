use pretty_assertions::assert_eq;

#[test]
pub fn roundtrip() {
    let data = include_bytes!("../example-files/files/everything-32.tvg");
    let tvg = tinyvg::parse(data.as_slice()).expect("error parsing TinyVG data");

    let mut v = Vec::new();
    let w = tinyvg::TinyVgWriter::new(&mut v);
    let table_writer = w.write_header(*tvg.header()).unwrap();
    let mut cmd_writer = match tvg.color_table() {
        tinyvg::ColorTable::Rgba8888(r) => {
            table_writer.write_color_table(r.iter().cloned()).unwrap()
        }
        tinyvg::ColorTable::Rgb565(r) => table_writer.write_color_table(r.iter().cloned()).unwrap(),
        tinyvg::ColorTable::RgbaF32(r) => {
            table_writer.write_color_table(r.iter().cloned()).unwrap()
        }
    };

    for cmd in tvg.cmds().iter().cloned() {
        cmd_writer.write_command(cmd).unwrap();
    }

    cmd_writer.finish().unwrap();

    let tvg2 = tinyvg::parse(&*v).expect("fdsa");
    assert_eq!(tvg, tvg2);
}
