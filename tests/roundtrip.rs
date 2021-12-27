use std::{
    ffi::OsStr,
    fs::{self, File},
    io::{self, Read},
    path::{Path, PathBuf},
};

use pretty_assertions::assert_eq;
use tinyvg::{Cmd, ColorTableEncoding, Rgba8888, TinyVgError, TinyVgReader, TinyVgWriter};

fn example_files() -> io::Result<impl Iterator<Item = io::Result<PathBuf>>> {
    let path = format!("{}/example-files/files", env!("CARGO_MANIFEST_DIR"));
    let dir = match fs::read_dir(&path) {
        Ok(d) => d,
        Err(e) => match e.kind() {
            io::ErrorKind::NotFound => panic!(concat!(
                "example files directory not found, ",
                "run `git submodules update --init` to populate",
            )),
            _ => return Err(e),
        },
    };

    Ok(dir.filter_map(|res| {
        match res.map(|ent| {
            if !ent.file_type()?.is_file() {
                return Ok(None);
            }

            let path = ent.path();

            if path.extension().map(OsStr::to_str).flatten() != Some("tvg") {
                return Ok(None);
            }

            Ok(Some(path))
        }) {
            Ok(Ok(o)) => Ok(o),
            Ok(Err(e)) | Err(e) => Err(e),
        }
        .transpose()
    }))
}

fn roundtrip<P: AsRef<Path>>(path: P) -> Result<(), TinyVgError> {
    let path = path.as_ref();

    let data = {
        let mut v = Vec::new();
        File::open(path)?.read_to_end(&mut v)?;
        v
    };

    let mut tvg = TinyVgReader::new(data.as_slice());
    let header = tvg.read_header()?;

    let table: Vec<Rgba8888> = match tvg.read_color_table()? {
        ColorTableEncoding::Rgba8888(r) => r.collect::<Result<Vec<_>, _>>()?,
        _ => panic!("unexpected color encoding"),
    };

    let commands = {
        let mut r = tvg.read_commands()?;
        let mut c: Vec<Cmd> = Vec::new();
        while let Some(cmd) = r.read_cmd()? {
            c.push(cmd.try_into()?);
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
        let mut c: Vec<Cmd> = Vec::new();
        while let Some(cmd) = r.read_cmd()? {
            c.push(cmd.try_into()?);
        }
        c
    };

    assert_eq!(header, header2);
    assert_eq!(table, table2);
    assert_eq!(commands, commands2);

    Ok(())
}

#[test]
pub fn roundtrip_all() -> Result<(), TinyVgError> {
    for file in example_files()? {
        let path = file?;
        if let Err(e) = roundtrip(&path) {
            panic!("failed: {:?}: {:?}", path, e);
        }
    }

    Ok(())
}
