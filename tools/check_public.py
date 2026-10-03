"""Run every registered public component's checks, locally and in CI."""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from public import ROOT, TEMPLATE, include_check, registry, repo_file
from offline import disable_network


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
        for names, label in [([], "template"), (list(entries), "all-components")]:
            source = scratch / f"{label}.cpp"
            source.write_text(include_check(names, entries))
            binary = scratch / label
            run(["g++", *FLAGS, "-I", str(ROOT), str(source), "-o", str(binary)])
            run([str(binary)])
        for name, data in entries.items():
            for index, test in enumerate(data["tests"]):
                require_template_first(test)
                binary = scratch / f"{name}-test-{index}"
                run(["g++", *FLAGS, str(repo_file(test)), "-o", str(binary)])
                run([str(binary)])
            for index, case in enumerate(data.get("io_cases", [])):
                require_template_first(case["source"])
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
            included = scratch / f"{name}-included.cpp"
            included.write_text(include_check([name], entries))
            run(["g++", *FLAGS, "-I", str(ROOT), "-fsyntax-only", str(included)])
            print(f"C++ tests and template-first include check passed: {name}")


def require_template_first(test):
    includes = [line.strip() for line in repo_file(test).read_text().splitlines()
                if line.lstrip().startswith("#include")]
    expected = f'#include "../{TEMPLATE}"'
    if not includes or includes[0] != expected:
        raise RuntimeError(f"test must include the library template first: {test}")


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
    disable_network()
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
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
