#![no_main]
use libfuzzer_sys::fuzz_target;

use std::convert::TryInto;

use tinyvg::{Cmd, TinyVgReader};

fn run_fuzz(data: &[u8]) -> tinyvg::Result<()> {
    let mut r = TinyVgReader::new(data);
    let _ = r.read_header();

    let table = r.read_color_table()?.to_rgba_f32();

    for res in table {
        let _ = res?;
    }

    let mut cmds = r.read_commands()?;

    while let Some(cmd) = cmds.read_cmd()? {
        let _: Cmd = cmd.try_into()?;
    }

    Ok(())
}

fuzz_target!(|data: &[u8]| {
    // fuzzed code goes here
    let _ = run_fuzz(data);
});
