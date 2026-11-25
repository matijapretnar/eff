#!/usr/bin/env python3
"""Compare the code that Eff generates with native OCaml.

The programs are those of effect-handlers-bench (the submodule
effect-handlers-bench). For each benchmark and input size, the script

1. builds every variant with one OCaml compiler (the opam switch --switch),
2. runs each variant once with a time limit and checks that its output equals
   the output of the baseline native-pure, and
3. measures the variants that pass with hyperfine.

It writes summary.csv to the output directory, with one row for each
benchmark, size and variant. A variant that fails, gives a wrong result, or
exceeds the time limit at some size is not run at larger sizes. Nor is a
variant whose time, grown as the baseline's, would exceed the limit.

Variants:
  native-<v>          misc/benchmarks/native/<benchmark>_<v>.ml
  ocaml5              the suite's OCaml 5 implementation
  eff-plain           Eff compiled to plain OCaml
  eff-plain-noopt     the same, with --no-opts
  eff-handlers        Eff compiled to OCaml 5 handlers
  eff-handlers-noopt  the same, with --no-opts
"""

import argparse
import csv
import json
import os
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent

# Input sizes for the graphs. Each list has 8 increasing sizes, which double
# or, where the work grows exponentially, grow by a constant. The profile
# quick uses the 5 smallest, at about an eighth of the largest.
SIZES = {
    "countdown": [2_000_000 * 2**i for i in range(8)],
    "fibonacci_recursive": [28, 30, 32, 34, 36, 38, 40, 42],
    "generator": [18, 19, 20, 21, 22, 23, 24, 25],
    "handler_sieve": [2_500, 5_000, 7_500, 10_000, 15_000, 20_000, 30_000, 40_000],
    "iterator": [1_250_000 * 2**i for i in range(8)],
    "nqueens": [5, 6, 7, 8, 9, 10, 11, 12],
    "parsing_dollars": [1_250, 2_500, 5_000, 7_500, 10_000, 15_000, 20_000, 30_000],
    "product_early": [3_125 * 2**i for i in range(8)],
    "resume_nontail": [625 * 2**i for i in range(8)],
    "tree_explore": [9, 10, 11, 12, 13, 14, 15, 16],
    "triples": [50, 75, 100, 150, 200, 300, 400, 600],
}

BASELINE = "native-pure"

# quick shows the trends in about a minute: the single timed run of the
# check, at the 5 smallest sizes, with a limit of 1 s. full is for the final
# graphs: all sizes, measured by hyperfine with repetitions, which takes
# hours. Options on the command line override these values.
PROFILES = {
    "quick": {"sizes": 5, "timeout": 1, "check_only": True},
    "full": {"timeout": 120, "warmup": 1, "check_only": False},
}

EFF_VARIANTS = {
    "eff-plain": ["--compile-plain-ocaml"],
    "eff-plain-noopt": ["--no-opts", "--compile-plain-ocaml"],
    "eff-handlers": ["--compile-ocaml-handlers"],
    "eff-handlers-noopt": ["--no-opts", "--compile-ocaml-handlers"],
}

# Changes to the suite's Eff programs until upstream has them: a user effect
# may not have the name of a built-in effect.
EFF_RENAMES = {"parsing_dollars": [("Read", "ReadChar")]}


def log(msg):
    print(msg, file=sys.stderr, flush=True)


def native_variants(benchmark):
    return sorted(
        "native-" + f.stem[len(benchmark) + 1 :]
        for f in (HERE / "native").glob(benchmark + "_*.ml")
        if f.stem[len(benchmark) + 1 :].isidentifier()
    )


def ocamlopt(files, switch, d, effects=False):
    """Compiles [files] in [d] to [d]/main, with OCaml 5 effects and multicont
    if [effects]. Returns an error, or None. It skips the compilation if the
    command and the files are the same as for the existing executable."""
    cmd = ["opam", "exec", "--switch=" + switch, "--", "ocamlfind", "ocamlopt"]
    cmd += ["-O3", "-w", "-a"]
    if effects:
        cmd += ["-package", "multicont", "-linkpkg"]
    cmd += ["-o", "main"] + files
    stamp = "\0".join(cmd + [(d / f).read_text() for f in files])
    if (d / "main").exists() and (d / "stamp").exists():
        if (d / "stamp").read_text() == stamp:
            return None
    (d / "main").unlink(missing_ok=True)
    result = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
    if result.returncode != 0:
        return "ocamlopt: " + result.stderr.strip()
    (d / "stamp").write_text(stamp)
    return None


def rename_effects(benchmark, source):
    for old, new in EFF_RENAMES.get(benchmark, []):
        source = source.replace(f"({old} ", f"({new} ").replace(
            f"effect {old} ", f"effect {new} "
        )
    return source


def build(benchmark, variant, args, build_dir):
    """Builds one variant and returns its executable, or None with a log."""
    d = build_dir / benchmark / variant
    d.mkdir(parents=True, exist_ok=True)
    suite = args.suite / "benchmarks"
    if variant.startswith("native-"):
        src = HERE / "native" / f"{benchmark}_{variant[len('native-'):]}.ml"
        shutil.copy(src, d / "main.ml")
        error = ocamlopt(["main.ml"], args.switch, d)
    elif variant == "ocaml5":
        src = suite / "ocaml" / benchmark / "main.ml"
        if not src.exists():
            return None, "no OCaml 5 implementation in the suite"
        shutil.copy(src, d / "main.ml")
        error = ocamlopt(["main.ml"], args.switch, d, effects=True)
    else:
        eff_dir = suite / "eff" / benchmark
        source = rename_effects(benchmark, (eff_dir / "main.eff").read_text())
        (d / "main.eff").write_text(source)
        shutil.copy(eff_dir / "wrapper.ml", d / "wrapper.ml")
        flags = ["--no-stdlib"] + EFF_VARIANTS[variant]
        with open(d / "generated.ml", "w") as out:
            gen = subprocess.run(
                [str(args.eff)] + flags + ["main.eff"],
                cwd=d,
                stdout=out,
                stderr=subprocess.PIPE,
                text=True,
            )
        if gen.returncode != 0:
            return None, "eff: " + gen.stderr.strip()
        files = ["generated.ml", "wrapper.ml"]
        plain = "--compile-plain-ocaml" in flags
        if plain:
            shutil.copy(REPO / "ocamlHeader" / "ocamlHeader.ml", d)
            files = ["ocamlHeader.ml"] + files
        error = ocamlopt(files, args.switch, d, effects=not plain)
    if error:
        return None, error
    return d / "main", None


def run_once(exe, size, timeout):
    """Runs [exe] once and returns its status, output and time in seconds."""
    start = time.monotonic()
    try:
        r = subprocess.run(
            [str(exe), str(size)], capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return "timeout", None, None
    elapsed = time.monotonic() - start
    if r.returncode != 0:
        lines = r.stderr.strip().splitlines()
        return "failed", lines[-1] if lines else f"exit code {r.returncode}", None
    return "ok", r.stdout.strip(), elapsed


def hyperfine(benchmark, size, exes, args, json_dir):
    out = json_dir / f"{benchmark}-{size}.json"
    cmd = ["hyperfine", "-N", "--style", "basic"]
    cmd += ["--warmup", str(args.warmup)]
    # Without a fixed number of runs, hyperfine makes at least 10 runs and
    # runs for at least 3 seconds.
    if args.runs:
        cmd += ["--runs", str(args.runs)]
    cmd += ["--export-json", str(out)]
    for variant, exe in exes.items():
        cmd += ["-n", variant, f"{exe} {size}"]
    subprocess.run(cmd, check=True, stdout=sys.stderr)
    return {r["name"]: measurement(r) for r in json.loads(out.read_text())["results"]}


def measurement(result):
    """The wall-clock times, instructions and peak memory of one variant, in
    the format of hyperfine 2. Instructions vary much less between runs than
    times."""
    summary = result["summary"]
    m = {k: summary["time_wall_clock"][k] for k in ("mean", "stddev", "min", "max")}
    m["instructions"] = summary.get("instructions", {}).get("mean", "")
    m["peak_rss"] = summary.get("memory_peak_resident", {}).get("max", "")
    return m


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--eff", type=Path, default=REPO / "eff.exe")
    p.add_argument("--switch", default="eff-bench")
    p.add_argument("--suite", type=Path, default=HERE / "effect-handlers-bench")
    p.add_argument("--out", type=Path, default=HERE / "_results")
    p.add_argument("--only", help="comma-separated benchmarks")
    p.add_argument("--variants", help="comma-separated variants")
    p.add_argument("--profile", choices=PROFILES, default="quick")
    p.add_argument("--timeout", type=float, help="seconds per check run")
    p.add_argument("--warmup", type=int, help="hyperfine warm-up runs")
    p.add_argument("--runs", type=int, help="hyperfine runs per variant")
    p.add_argument("--sizes", type=int, help="number of smallest sizes to use")
    p.add_argument(
        "--check-only",
        action=argparse.BooleanOptionalAction,
        help="measure with the single run of the check, without hyperfine",
    )
    args = p.parse_args()
    for key, value in PROFILES[args.profile].items():
        if getattr(args, key) is None:
            setattr(args, key, value)
    args.eff = args.eff.resolve()
    args.suite = args.suite.resolve()

    benchmarks = args.only.split(",") if args.only else list(SIZES)
    build_dir = args.out / "build"
    json_dir = args.out / "json"
    json_dir.mkdir(parents=True, exist_ok=True)
    rows = []

    def variants_of(benchmark):
        variants = native_variants(benchmark) + ["ocaml5"] + list(EFF_VARIANTS)
        if args.variants:
            wanted = args.variants.split(",")
            variants = [v for v in variants if v in wanted or v == BASELINE]
        return variants

    def build_and_start(job):
        # The first start of a new executable is slow on macOS, so each one
        # runs once here, where its time does not count.
        benchmark, variant = job
        exe, error = build(benchmark, variant, args, build_dir)
        if exe:
            run_once(exe, SIZES[benchmark][0], args.timeout)
        return exe, error

    # The builds are independent, so they run in parallel. The measurements
    # below run one after another, so that they do not disturb each other.
    jobs = [(b, v) for b in benchmarks for v in variants_of(b)]
    with ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
        built = dict(zip(jobs, pool.map(build_and_start, jobs)))
    log(f"built {len(jobs)} executables")

    for benchmark in benchmarks:
        exes = {}
        for variant in variants_of(benchmark):
            exe, error = built[benchmark, variant]
            if exe:
                exes[variant] = exe
            else:
                log(f"{benchmark} {variant}: build failed: {error.splitlines()[0]}")
                rows.append([benchmark, "", variant, "build-failed"] + [""] * 7)
        if BASELINE not in exes:
            log(f"{benchmark}: no baseline, skipped")
            continue

        sizes = SIZES[benchmark][: args.sizes]
        last = {}  # the time of each variant at the previous size
        for size in sizes:
            status, expected, base = run_once(exes[BASELINE], size, args.timeout)
            if status != "ok":
                log(f"{benchmark} {size}: baseline {status}, larger sizes skipped")
                break
            # A variant probably grows as the baseline does. If its estimate
            # exceeds the limit, it is skipped without waiting for it.
            growth = base / last[BASELINE] if BASELINE in last else 1
            passing = {BASELINE: (exes[BASELINE], base)}
            for variant, exe in list(exes.items()):
                if variant == BASELINE:
                    continue
                if variant in last and last[variant] * growth > args.timeout:
                    status, output = "skipped", "estimated over the limit"
                else:
                    status, output, elapsed = run_once(exe, size, args.timeout)
                    if status == "ok" and output != expected:
                        status = "wrong"
                if status == "ok":
                    passing[variant] = (exe, elapsed)
                else:
                    log(f"{benchmark} {size} {variant}: {status} {output or ''}")
                    rows.append([benchmark, size, variant, status] + [""] * 7)
                    del exes[variant]
            last = {v: t for v, (_, t) in passing.items()}
            if args.check_only:
                # The time of the single run of the check, without statistics
                base = passing[BASELINE][1]
                for variant, (_, elapsed) in passing.items():
                    rows.append(
                        [benchmark, size, variant, "checked", f"{elapsed:.6f}"]
                        + [""] * 3
                        + [f"{elapsed / base:.3f}", "", ""]
                    )
                continue
            exes_passing = {v: exe for v, (exe, _) in passing.items()}
            results = hyperfine(benchmark, size, exes_passing, args, json_dir)
            base = results[BASELINE]["mean"]
            for variant in exes_passing:
                r = results[variant]
                rows.append(
                    [benchmark, size, variant, "ok"]
                    + [
                        "" if r[k] is None else f"{r[k]:.6f}"
                        for k in ("mean", "stddev", "min", "max")
                    ]
                    + [f"{r['mean'] / base:.3f}", r["instructions"], r["peak_rss"]]
                )

    with open(args.out / "summary.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(
            ["benchmark", "size", "variant", "status"]
            + ["mean_s", "stddev_s", "min_s", "max_s", "ratio"]
            + ["instructions", "peak_rss_bytes"]
        )
        w.writerows(rows)
    log(f"wrote {args.out / 'summary.csv'}")


if __name__ == "__main__":
    main()
