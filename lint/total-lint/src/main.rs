use std::collections::BTreeSet;
use std::process::ExitCode;

use total_lint::analysis::Class;
use total_lint::artifact::{Artifact, Loaded};
use total_lint::baseline;
use total_lint::render::{self, View};
use total_lint::report::{JUSTIFY_MARKER, Options, Outcome, resolve_dir};

fn usage() -> String {
    let classes = Class::ALL.map(|c| c.name()).join(", ");
    format!(
        "usage: total-lint <artifact.json> [options]

Classifies every opcode of a compiled Noir program or contract (nargo
compile output) by whether it can fail and who controls the failure, and
lists every place Brillig (unconstrained) code can abort.

Provenance and justification:
  --lib-src DIR       library source directory whose hint-class constraints
                      and abort sites are whitelisted; repeatable. Relative
                      paths resolve against the current directory and must
                      exist; files match by absolute path prefix. No
                      directory is whitelisted by default
  --allow-src DIR     also honour justification markers in files under DIR;
                      repeatable (by default only the entry package's own
                      source directory, outside any library tree, counts).
                      For an #[aztec] contract that default is aztec-nr's
                      macro directory: pass the contract's src here
  --allow-entry-ranges
                      justify the compiler's range checks on typed entry
                      parameters (u8, bool, [u8; N] ...): the caller's ABI
                      encoding rejects out-of-range values before the
                      circuit runs
Gating:
  --baseline FILE     accept the unjustified items listed in FILE (written
                      by --write-baseline); only items beyond it fail
  --write-baseline FILE
                      write every unjustified item to FILE and exit 0
  --max-unjustified N fail only when more than N items fail (default 0)
Selection and output:
  --function NAME     lint only this function of a contract artifact;
                      repeatable (default: every constrained function)
  --class NAME        list only items of this class; repeatable (default:
                      every class but definition and neutralised)
  --verbose           one line per opcode instead of one per source line
                      and class, and the Brillig and ACIR call lists
  --explain           say why each item can fail (implies --verbose), list
                      the compiler hint patterns treated as hint-compiler,
                      and say what the lint cannot decide
  --json              machine-readable output
  --summary           counts only
  --brillig-ops       report instead every Brillig opcode co-noir's MPC VM
                      (co-snarks co-brillig) cannot execute: integer And,
                      Or, Xor, Shl, Shr, ConditionalMov and every black box
                      but ToRadix, per unconstrained function with its
                      source location; exit 1 if any is reachable

Classes: {classes}.
Cannot fail on their own: definition, neutralised (predicate is the
constant 0, or statically true), implied (fails only if an earlier opcode
fails). Informational: backend-defined (holds at witness generation, but
the proving backend may fail on some inputs, e.g. ECDSA with an off-curve
key). Whitelisted: hint-compiler (a constraint on the compiler's own
inversion, integer-quotient or radix hints in a pattern that holds for
every input; --explain lists the patterns), hint-library (touches a hint
witness and its source is under --lib-src). Reported: input-falsifiable
(depends only on inputs, including typed entry-parameter range checks),
library-input-falsifiable (the same, with library source), hint-unreviewed
(touches a hint witness outside the library), hint-pinned (equates a
hint-derived witness to a constant, as an asserted comparison or flag
does; in the library too), unsolvable.

Brillig abort sites (kinds trap, division, curve-op, oracle, radix) count
outside the library. A note-width site, a call to aztec-nr v6's PXE
oracle aztec_prv_notifyCreatedNote with a packed note wider than
MAX_NOTE_PACKED_LEN (8), counts in the library too: the PXE then refuses
every later read of that storage slot in the transaction.

A reported item or abort site is justified by a // comment
  {JUSTIFY_MARKER} <reason>
after code on its line (that line only), or in the comment block directly
above its statement (that statement only), in a frame of its call stack
whose file is in the entry package's source directory (not a library
tree) or under an --allow-src directory. Dependencies cannot justify
items. The report counts what each marker justified.

Exit status: 0 when no reported item and no reported abort site remains
unjustified (beyond the baseline and
--max-unjustified), 1 otherwise, 2 on usage or decode errors. With
--brillig-ops: 0 when no reachable unsupported op remains, 1 otherwise."
    )
}

#[derive(Default)]
struct Args {
    path: Option<String>,
    lib_src: Vec<String>,
    allow_src: Vec<String>,
    allow_entry_ranges: bool,
    functions: Vec<String>,
    baseline: Option<String>,
    write_baseline: Option<String>,
    max_unjustified: usize,
    view: View,
    json: bool,
    ops: bool,
}

enum Parsed {
    Run(Box<Args>),
    Help,
}

fn parse(argv: impl IntoIterator<Item = String>) -> Result<Parsed, String> {
    let mut a = Args::default();
    let mut classes = BTreeSet::new();
    let mut it = argv.into_iter();
    while let Some(arg) = it.next() {
        let mut value = |flag: &str| it.next().ok_or_else(|| format!("{flag} needs a value"));
        match arg.as_str() {
            "--lib-src" => a.lib_src.push(value("--lib-src")?),
            "--allow-src" => a.allow_src.push(value("--allow-src")?),
            "--function" => a.functions.push(value("--function")?),
            "--baseline" => a.baseline = Some(value("--baseline")?),
            "--write-baseline" => a.write_baseline = Some(value("--write-baseline")?),
            "--max-unjustified" => {
                let v = value("--max-unjustified")?;
                a.max_unjustified = v
                    .parse()
                    .map_err(|_| format!("--max-unjustified {v:?}: not a count"))?;
            }
            "--class" => {
                let v = value("--class")?;
                classes.insert(Class::from_name(&v).ok_or_else(|| format!("unknown class {v:?}"))?);
            }
            "--allow-entry-ranges" => a.allow_entry_ranges = true,
            "--verbose" => a.view.verbose = true,
            "--explain" => {
                a.view.explain = true;
                a.view.verbose = true;
            }
            "--json" => a.json = true,
            "--summary" => a.view.summary = true,
            "--brillig-ops" => a.ops = true,
            "-h" | "--help" => return Ok(Parsed::Help),
            s if s.starts_with('-') => return Err(format!("unknown option {s}")),
            s => {
                if a.path.replace(s.to_string()).is_some() {
                    return Err("only one artifact path".into());
                }
            }
        }
    }
    if a.path.is_none() {
        return Err("no artifact path".into());
    }
    if !classes.is_empty() {
        a.view.classes = Some(classes);
    }
    Ok(Parsed::Run(Box::new(a)))
}

/// The functions to lint, and a header line for a contract.
fn select(loaded: Loaded, names: &[String]) -> Result<(Vec<Artifact>, Option<String>), String> {
    match loaded {
        Loaded::Program(a) => {
            if !names.is_empty() {
                return Err("--function applies to contract artifacts".into());
            }
            Ok((vec![a], None))
        }
        Loaded::Contract {
            name,
            functions,
            unconstrained,
            ..
        } => {
            for n in names {
                if unconstrained.contains(n) {
                    return Err(format!(
                        "function {n} is unconstrained: it has no ACIR to lint"
                    ));
                }
                if !functions.iter().any(|f| &f.name == n) {
                    return Err(format!("contract {name} has no function {n}"));
                }
            }
            let chosen: Vec<Artifact> = functions
                .into_iter()
                .filter(|f| names.is_empty() || names.contains(&f.name))
                .collect();
            let header = format!(
                "contract {name}: {} constrained function(s) linted; unconstrained, not linted: {}",
                chosen.len(),
                if unconstrained.is_empty() {
                    "none".to_string()
                } else {
                    unconstrained.join(", ")
                }
            );
            Ok((chosen, Some(header)))
        }
    }
}

fn options(args: &Args) -> Result<Options, String> {
    let resolve = |flag: &str, dirs: &[String]| -> Result<Vec<String>, String> {
        dirs.iter().map(|d| resolve_dir(flag, d)).collect()
    };
    Ok(Options {
        lib_dirs: resolve("--lib-src", &args.lib_src)?,
        allow_dirs: resolve("--allow-src", &args.allow_src)?,
        allow_entry_ranges: args.allow_entry_ranges,
    })
}

fn run(args: &Args) -> Result<i32, String> {
    let path = args.path.as_deref().unwrap_or_default();
    let opts = options(args)?;
    let loaded = Loaded::from_path(path)?;
    let mut warnings: Vec<String> = loaded.version_warning().into_iter().collect();
    let (artifacts, header) = select(loaded, &args.functions)?;
    let mut outcomes: Vec<Outcome> = artifacts
        .iter()
        .map(|a| Outcome::run_with(a, opts.clone()))
        .collect();
    for o in &outcomes {
        for w in &o.warnings {
            if !warnings.contains(w) {
                warnings.push(w.clone());
            }
        }
    }
    if let Some(file) = &args.baseline {
        let base = baseline::base_dir(file)?;
        let mut remaining = baseline::read(file)?;
        for o in &mut outcomes {
            o.apply_baseline(&mut remaining, &base);
        }
        let stale: usize = remaining.values().sum();
        if stale > 0 {
            warnings.push(format!(
                "{stale} item(s) in baseline {file} no longer occur; rewrite it with --write-baseline"
            ));
        }
    }
    for w in &warnings {
        eprintln!("total-lint: warning: {w}");
    }
    if !opts.lib_dirs.is_empty() {
        eprintln!(
            "total-lint: library directories whitelisted: {}",
            opts.lib_dirs.join(", ")
        );
    }

    if args.ops {
        return Ok(render_ops(args, &outcomes, path, header.as_deref()));
    }
    if args.json {
        let v = render::render_json(&outcomes, &args.view, args.max_unjustified, &warnings);
        println!("{}", serde_json::to_string_pretty(&v).expect("json"));
    } else {
        println!("artifact: {path}");
        if let Some(h) = &header {
            println!("{h}");
        }
        print!(
            "{}",
            render::render_human(
                &outcomes,
                &args.view,
                args.max_unjustified,
                header.is_some()
            )
        );
    }
    if let Some(file) = &args.write_baseline {
        let file_data = baseline::build(&outcomes, &baseline::base_dir(file)?);
        baseline::write(file, &file_data)?;
        let n: usize = file_data.entries.iter().map(|e| e.count).sum();
        eprintln!("total-lint: wrote {n} accepted item(s) to {file}");
        return Ok(0);
    }
    Ok(render::exit_code(&outcomes, args.max_unjustified))
}

fn render_ops(args: &Args, outcomes: &[Outcome], path: &str, header: Option<&str>) -> i32 {
    if args.json {
        let v: Vec<_> = outcomes.iter().map(|o| o.render_mpc_ops_json()).collect();
        println!("{}", serde_json::to_string_pretty(&v).expect("json"));
    } else {
        println!("artifact: {path}");
        if let Some(h) = header {
            println!("{h}");
        }
        for o in outcomes {
            if header.is_some() {
                println!("\n=== function {}", o.artifact.name);
            }
            print!("{}", o.render_mpc_ops_human(args.view.summary));
        }
    }
    outcomes
        .iter()
        .map(|o| o.mpc_ops_exit_code())
        .max()
        .unwrap_or(0)
}

fn main() -> ExitCode {
    let args = match parse(std::env::args().skip(1)) {
        Ok(Parsed::Help) => {
            println!("{}", usage());
            return ExitCode::SUCCESS;
        }
        Ok(Parsed::Run(a)) => a,
        Err(e) => {
            eprintln!("total-lint: {e}\n\n{}", usage());
            return ExitCode::from(2);
        }
    };
    match run(&args) {
        Ok(code) => ExitCode::from(code as u8),
        Err(e) => {
            eprintln!("total-lint: {e}");
            ExitCode::from(2)
        }
    }
}
