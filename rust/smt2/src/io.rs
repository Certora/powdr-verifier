//! Load/dump SMT-LIB scripts from files and readers.

use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;

use crate::script::Script;

pub fn load_reader<R: Read>(mut reader: R) -> Result<Script, String> {
    let mut input = String::new();
    reader
        .read_to_string(&mut input)
        .map_err(|e| e.to_string())?;
    Script::parse(&input)
}

pub fn load_path(path: impl AsRef<Path>) -> Result<Script, String> {
    let input = fs::read_to_string(path.as_ref()).map_err(|e| e.to_string())?;
    Script::parse(&input)
}

pub fn dump_string(script: &Script) -> String {
    let mut out = Vec::new();
    dump_writer(script, &mut out).expect("writing to vec");
    String::from_utf8(out).expect("utf8")
}

pub fn dump_writer<W: Write>(script: &Script, writer: &mut W) -> io::Result<()> {
    for (i, cmd) in script.commands.iter().enumerate() {
        if i > 0 {
            writer.write_all(b"\n")?;
        }
        writer.write_all(cmd.raw.as_bytes())?;
    }
    writer.write_all(b"\n")?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::Command;

    #[test]
    fn round_trip() {
        let script = Script::from_commands(vec![
            Command::new("(declare-fun x () Int)"),
            Command::new("(assert (= x 0))"),
        ]);
        let s = dump_string(&script);
        let back = Script::parse(&s).unwrap();
        assert_eq!(back.commands.len(), 2);
    }
}
