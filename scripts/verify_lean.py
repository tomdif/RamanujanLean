#!/usr/bin/env python3
"""Build public targets and reject unexpected axiom dependencies in their audits."""
import argparse
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="also build and audit the root library")
    parser.add_argument("--output-dir", type=Path, default=Path("/tmp/ramanujan-lean-verification"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    audits = ["forty11", "bosonic_fock", "four_prime_converse"]
    if args.full:
        audits.append("celebrated_targets")
    targets = []
    for name in audits:
        source = (root / "scripts/audit" / f"{name}.lean").read_text()
        for target in re.findall(r"^import (RamanujanTau(?:\.\w+)*)$", source, re.M):
            if target not in targets:
                targets.append(target)
    if args.full:
        targets = ["RamanujanTau"]
    with (output / "build.log").open("w") as log:
        # The audit's dependency order avoids compiling all identity certificates
        # concurrently on hosted runners with limited memory.
        for target in targets:
            print(f"Building {target}", flush=True)
            log.write(f"Building {target}\n")
            log.flush()
            # Keep diagnostics visible even if the runner terminates the job
            # before its failure-report step can read the saved log.
            with subprocess.Popen(["lake", "build", target], cwd=root, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  bufsize=1) as process:
                for line in process.stdout:
                    log.write(line)
                    log.flush()
                    print(line, end="", flush=True)
                returncode = process.wait()
            if returncode:
                raise SystemExit(f"Build failed ({target}); see {output / 'build.log'}")
    print(f"Build passed ({len(targets)} requested targets); log: {output / 'build.log'}", flush=True)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name in audits:
        source = (root / "scripts/audit" / f"{name}.lean").read_text()
        expected = len(re.findall(r"^#print axioms ", source, re.M))
        print(f"Auditing {name}", flush=True)
        result = subprocess.run(["lake", "env", "lean", f"scripts/audit/{name}.lean"],
                                cwd=root, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        path = output / f"{name}.axioms.txt"
        path.write_text(result.stdout)
        reports = re.findall(r"depends on axioms: \[([^]]*)\]", result.stdout)
        reports += [""] * len(re.findall(r"does not depend on any axioms", result.stdout))
        unexpected = {a.strip() for report in reports for a in report.split(",") if a.strip()} - allowed
        if result.returncode or not reports or len(reports) != expected or unexpected:
            raise SystemExit(f"Audit failed ({name}, unexpected axioms: {sorted(unexpected)}); see {path}")
        print(f"{name}: {len(reports)} declarations, standard axioms only; {path}", flush=True)


if __name__ == "__main__":
    main()
