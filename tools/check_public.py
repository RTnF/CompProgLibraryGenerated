"""Run every registered public component's checks, locally and in CI."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from public import ROOT, assemble, registry, repo_file


FLAGS = ["-std=c++17", "-O2", "-Wall", "-Wextra", "-pedantic"]


def run(command, **kwargs):
    subprocess.run(command, cwd=ROOT, check=True, **kwargs)


def check_compiler():
    version = subprocess.check_output(["g++", "-dumpfullversion"], text=True).strip()
    if version != "13.3.0":
        raise RuntimeError(f"expected GCC 13.3.0, found {version}")


def check_local_results_untracked():
    tracked = subprocess.check_output(
        ["git", "ls-files", "--", "benchmarks/local/"], cwd=ROOT, text=True,
    ).strip()
    if tracked:
        raise RuntimeError(f"local benchmark results are tracked by Git: {tracked}")


def check_cpp(entries):
    with tempfile.TemporaryDirectory(prefix="public-check-") as directory:
        scratch = Path(directory)
        run(["g++", *FLAGS, str(repo_file("a.cpp")), "-o", str(scratch / "template")])
        run([str(scratch / "template")], input=b"")
        for name, data in entries.items():
            for index, test in enumerate(data["tests"]):
                binary = scratch / f"{name}-test-{index}"
                run(["g++", *FLAGS, str(repo_file(test)), "-o", str(binary)])
                run([str(binary)])
            for index, case in enumerate(data.get("io_cases", [])):
                binary = scratch / f"{name}-io-{index}"
                run(["g++", *FLAGS, str(repo_file(case["source"])), "-o", str(binary)])
                result = subprocess.run(
                    [str(binary)], cwd=ROOT,
                    input=repo_file(case["input"]).read_bytes(),
                    capture_output=True, check=True,
                )
                expected = repo_file(case["expected"]).read_bytes()
                if result.stdout != expected:
                    raise RuntimeError(f"I/O case {index} failed for {name}: {result.stdout!r} != {expected!r}")
            pasted = scratch / f"{name}-pasted.cpp"
            pasted.write_text(assemble(name, entries))
            run(["g++", *FLAGS, "-fsyntax-only", str(pasted)])
            print(f"C++ tests and paste check passed: {name}")


def check_bridge(entries):
    for name, data in entries.items():
        run([sys.executable, str(repo_file(data["bridge"]))])
        print(f"C++ AST and Lean model match: {name}")


def check_lean():
    local_lake = ROOT / ".tools/elan/bin/lake"
    if local_lake.is_file():
        os.environ["ELAN_HOME"] = str(ROOT / ".tools/elan")
    lake = str(local_lake) if local_lake.is_file() else shutil.which("lake")
    if lake is None:
        raise RuntimeError("lake is required for Lean proof checks")
    run([lake, "build"])
    run([lake, "env", "leanchecker", "Proofs"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("all", "cpp", "bridge"), default="all")
    args = parser.parse_args()
    entries = registry()
    check_local_results_untracked()
    check_compiler()
    if args.mode in ("all", "cpp"):
        check_cpp(entries)
    if args.mode in ("all", "bridge"):
        check_bridge(entries)
    if args.mode == "all":
        check_lean()
    print(f"public checks passed for {len(entries)} component(s): {args.mode}")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
