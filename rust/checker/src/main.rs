use std::env;
use std::path::PathBuf;
use std::process;

use checker::{dump_action, run_check, CheckOptions};

fn main() {
    if let Err(e) = run() {
        eprintln!("checker: {e}");
        process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut dump_model: Option<PathBuf> = None;
    let mut solve_chunked = true;
    let mut timeout: Option<f64> = None;
    let mut positional = Vec::new();

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--dump-model" => {
                i += 1;
                let v = args.get(i).ok_or("missing value for --dump-model")?;
                dump_model = Some(PathBuf::from(v));
                i += 1;
            }
            "--timeout" => {
                i += 1;
                let v = args.get(i).ok_or("missing value for --timeout")?;
                timeout = Some(v.parse().map_err(|_| "invalid --timeout")?);
                i += 1;
            }
            "--solve-chunked" => {
                solve_chunked = true;
                i += 1;
            }
            "--no-solve-chunked" => {
                solve_chunked = false;
                i += 1;
            }
            opt if opt.starts_with("--") => return Err(format!("unknown option: {opt}")),
            _ => {
                positional.push(args[i].clone());
                i += 1;
            }
        }
    }

    if positional.len() != 1 {
        return Err(
            "usage: checker [--dump-model PATH] [--solve-chunked | --no-solve-chunked] [--timeout SEC] <input.smt2>".into(),
        );
    }

    let action = run_check(&CheckOptions {
        input: PathBuf::from(&positional[0]),
        dump_model,
        solve_chunked,
        timeout,
    })?;

    println!("{}", dump_action(&action));
    Ok(())
}
