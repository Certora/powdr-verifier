use std::env;
use std::io::{self, Read, Write, stdin, stdout};
use std::process;

use smt2::{dump_string, load_path, load_reader, pretty_print_script};
use simplifier::{run_pipeline, write_step_stats};

fn main() {
    if let Err(e) = run() {
        eprintln!("simplifier: {e}");
        process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut timeout: Option<f64> = None;
    let mut pretty = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--timeout" => {
                i += 1;
                let v = args.get(i).ok_or("missing value for --timeout")?;
                timeout = Some(v.parse().map_err(|_| "invalid --timeout")?);
                i += 1;
            }
            "--pretty" => {
                pretty = true;
                i += 1;
            }
            opt if opt.starts_with("--") => return Err(format!("unknown option: {opt}")),
            _ => break,
        }
    }
    let _ = timeout;

    let positional: Vec<String> = args[i..].to_vec();
    if positional.len() != 3 {
        return Err(
            "usage: simplifier [--timeout SEC] [--pretty] <input> <tactic> <output>".into(),
        );
    }
    let input = &positional[0];
    let tactic_pipeline = &positional[1];
    let output = &positional[2];

    let script = if input == "-" {
        let mut buf = String::new();
        stdin()
            .read_to_string(&mut buf)
            .map_err(|e| e.to_string())?;
        load_reader(io::Cursor::new(buf))?
    } else {
        load_path(input)?
    };

    let tactics: Vec<String> = tactic_pipeline.split(':').map(|s| s.to_string()).collect();
    let (out_script, steps) = run_pipeline(&script, &tactics)?;
    let out_script = if pretty {
        pretty_print_script(&out_script)?
    } else {
        out_script
    };

    let out_str = dump_string(&out_script);
    if output == "-" {
        stdout()
            .write_all(out_str.as_bytes())
            .map_err(|e| e.to_string())?;
    } else {
        std::fs::write(output, out_str.as_bytes()).map_err(|e| e.to_string())?;
    }

    let mut stderr = io::stderr();
    for step in &steps {
        write_step_stats(&mut stderr, step).map_err(|e| e.to_string())?;
    }
    Ok(())
}
