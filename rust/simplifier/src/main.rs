use std::env;
use std::io::{self, Read, Write, stdin, stdout};
use std::path::PathBuf;
use std::process;

use smt2::{dump_string, load_path, load_reader, pretty_print_script};
use simplifier::budget::Budget;
use simplifier::{run_pipeline, write_step_stats, DumpStepsConfig};

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
    let mut dump_steps = false;
    let mut dump_step_offset = 0usize;
    let mut dump_steps_output: Option<PathBuf> = None;

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
            "--dump-steps" => {
                dump_steps = true;
                i += 1;
            }
            "--dump-step-offset" => {
                i += 1;
                let v = args
                    .get(i)
                    .ok_or("missing value for --dump-step-offset")?;
                dump_step_offset = v.parse().map_err(|_| "invalid --dump-step-offset")?;
                i += 1;
            }
            "--dump-steps-output" => {
                i += 1;
                let v = args
                    .get(i)
                    .ok_or("missing value for --dump-steps-output")?;
                dump_steps_output = Some(PathBuf::from(v));
                i += 1;
            }
            opt if opt.starts_with("--") => return Err(format!("unknown option: {opt}")),
            _ => break,
        }
    }
    let budget = match timeout {
        Some(secs) => Budget::from_timeout_secs(secs),
        None => Budget::unlimited(),
    };

    let positional: Vec<String> = args[i..].to_vec();
    if positional.len() != 3 {
        return Err(
            "usage: simplifier [--timeout SEC] [--pretty] [--dump-steps] [--dump-step-offset N] [--dump-steps-output PATH] <input> <tactic> <output>".into(),
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
    let dump_cfg = if dump_steps {
        let dump_output = dump_steps_output
            .or_else(|| {
                if output == "-" {
                    None
                } else {
                    Some(PathBuf::from(output))
                }
            })
            .ok_or("--dump-steps requires a file output path")?;
        Some(DumpStepsConfig {
            output: dump_output,
            pretty,
            step_offset: dump_step_offset,
        })
    } else {
        None
    };
    let (out_script, steps) = run_pipeline(&script, &tactics, budget, dump_cfg.as_ref())?;
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
