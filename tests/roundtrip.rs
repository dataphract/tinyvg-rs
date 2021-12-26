use pretty_assertions::assert_eq;
use tinyvg::{ColorTableEncoding, Rgba8888, TinyVgError, TinyVgReader, TinyVgWriter};

#[test]
pub fn roundtrip() -> Result<(), TinyVgError> {
    let data = include_bytes!("../example-files/files/everything-32.tvg");

    let mut tvg = TinyVgReader::new(data.as_slice());
    let header = tvg.read_header()?;

    let table: Vec<Rgba8888> = match tvg.read_color_table()? {
        ColorTableEncoding::Rgba8888(r) => r.collect::<Result<Vec<_>, _>>()?,
        _ => panic!("unexpected color encoding"),
    };

    let commands = {
        let mut r = tvg.read_commands()?;
        let mut c = Vec::new();
        while let Some(cmd) = r.read_cmd()? {
            c.push(cmd);
        }
        c
    };

    let mut v = Vec::new();
    let w = TinyVgWriter::new(&mut v);
    let table_writer = w.write_header(header)?;
    let mut cmd_writer = table_writer.write_color_table(table.iter().cloned())?;

    for cmd in commands.iter().cloned() {
        cmd_writer.write_command(cmd)?;
    }

    cmd_writer.finish()?;

    let mut tvg2 = TinyVgReader::new(data.as_slice());
    let header2 = tvg2.read_header()?;
    let table2: Vec<Rgba8888> = match tvg2.read_color_table()? {
        ColorTableEncoding::Rgba8888(r) => r.collect::<Result<Vec<_>, _>>()?,
        _ => panic!("unexpected color encoding"),
    };
    let commands2 = {
        let mut r = tvg2.read_commands()?;
        let mut c = Vec::new();
        while let Some(cmd) = r.read_cmd()? {
            c.push(cmd);
        }
        c
    };

    assert_eq!(header, header2);
    assert_eq!(table, table2);
    assert_eq!(commands, commands2);

    Ok(())
}
