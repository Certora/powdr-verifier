use std::env;
use std::fs::File;
use std::io::{self, Read, Write, stdin, stdout};
use std::process;

use simplify_z3::{simplify_reader, write_stats};

fn main() {
    if let Err(e) = run() {
        eprintln!("simplify-z3: {e}");
        process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut input_path: Option<String> = None;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-i" | "--input" => {
                i += 1;
                input_path = Some(args.get(i).ok_or("missing value for -i")?.clone());
            }
            _ if args[i].starts_with('-') => {
                return Err(format!("unknown option: {}", args[i]));
            }
            _ => break,
        }
        i += 1;
    }
    let tactic_args: Vec<String> = args[i..].to_vec();

    let (output, stats) = if let Some(path) = input_path {
        let file = File::open(&path).map_err(|e| format!("open {path}: {e}"))?;
        simplify_reader(file, &tactic_args)?
    } else {
        let mut input = String::new();
        stdin()
            .read_to_string(&mut input)
            .map_err(|e| e.to_string())?;
        simplify_reader(io::Cursor::new(input), &tactic_args)?
    };

    write_stats(&mut io::stderr(), &stats).map_err(|e| e.to_string())?;
    stdout()
        .write_all(output.as_bytes())
        .map_err(|e| e.to_string())?;
    Ok(())
}
