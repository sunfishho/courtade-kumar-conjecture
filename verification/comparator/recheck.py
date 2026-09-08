"""Reproduce the documented local-object Comparator check with Lean 4.28.

Install this as verification/comparator/recheck.py alongside the preserved
checker, project, controls, and fixtures. This is not the stock Linux sandbox.
"""
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import json
import os
import subprocess
import time


MARKERS = [
    "Comparator statement and primitive comparison passed",
    "Comparator permitted-axiom check passed",
    "Replay starts with zero imported declarations",
    "Lean default kernel accepts the solution",
    "CK graph includes all 42 batches and 9457 kernel chunks",
    "Your solution is okay!",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--controls-only", action="store_true")
    parser.add_argument("--checker", type=Path,
                        help="Use an already-built checker instead of building the preserved source")
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = base / ".lake" / "check-runs" / stamp
    output.mkdir(parents=True)
    records = []

    def run(name, command, cwd, expected=0, markers=()):
        command = [str(p) for p in command]
        start = time.monotonic()
        logfile = output / (name + ".log")
        print("Running " + name, flush=True)
        with logfile.open("w") as log:
            process = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True)
            try:
                for line in process.stdout:
                    log.write(line)
                    log.flush()
                    print(line, end="", flush=True)
                code = process.wait()
            except BaseException:
                process.kill()
                process.wait()
                raise
        text = logfile.read_text()
        record = dict(name=name, command=command, exit_code=code,
                      expected_exit_code=expected, seconds=time.monotonic() - start,
                      passed=code == expected and all(m in text for m in markers))
        records.append(record)
        (output / "result.json").write_text(json.dumps(records, indent=2) + "\n")
        if not record["passed"]:
            raise SystemExit("Check failed; see " + str(logfile))

    if args.checker:
        checker = args.checker.resolve()
    else:
        run("build_checker", ["lake", "build", "comparator"], base / "tools/comparator")
        checker = base / "tools/comparator/.lake/build/bin/comparator"
    if not checker.is_file():
        raise SystemExit("Checker binary not found: " + str(checker))

    controls = base / "controls"
    modules = ["ControlChallenge", "ControlGood", "ControlBadAxiom", "ControlBadStatement"]
    run("build_controls", ["lake", "build", *modules], controls)
    cases = [
        ("ControlGood", 0, ["Your solution is okay!"]),
        ("ControlBadAxiom", 1, ["Illegal axiom detected: 'forbiddenControl'"]),
        ("ControlBadStatement", 1, ["Challenge and solution theorem statement do not match"]),
    ]
    for name, expected, markers in cases:
        run(name, ["lake", "env", checker, "--local-objects", controls / (name + ".json")],
            controls, expected, markers)

    fixtures = []
    for name in ["ControlChallenge.ndjson", "ControlBadTerm.ndjson"]:
        dest = output / name
        with gzip.open(controls / (name + ".gz"), "rb") as source:
            dest.write_bytes(source.read())
        fixtures.append(dest)
    run("ControlBadTerm", ["lake", "env", checker, "--exports", controls / "ControlGood.json", *fixtures],
        controls, 1, ["Comparator statement and primitive comparison passed",
                      "Comparator permitted-axiom check passed",
                      "Lean default kernel rejects the solution"])

    if not args.controls_only:
        project = base / "project"
        run("build_challenge_solution", ["lake", "build", "CKChallenge", "CKSolution"], project)
        run("courtade_kumar", ["lake", "env", checker, "--local-objects", project / "config.json"],
            project, 0, MARKERS)
    receipt = dict(accepted=True, controls_only=args.controls_only,
                   checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),
                   stock_linux_cli_isolation=False, checks=records)
    (output / "result.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("Passed " + ("controls only" if args.controls_only else "controls and CK replay"))
    print(output / "result.json")


if __name__ == "__main__":
    main()
