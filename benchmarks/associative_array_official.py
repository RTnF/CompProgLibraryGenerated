"""Replay and time every official Associative Array testcase.

Generate the cases first with `python3 generate.py -p associative_array` in a
checkout of yosupo06/library-checker-problems. The upstream generator checks
its own hash.json; this script checks the hashes again before benchmarking.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "tests/associative_array_checker.cpp"
FLAGS = ["-std=c++17", "-O2", "-Wall", "-Wextra", "-pedantic"]


def digest(path: Path) -> str:
    checksum = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            checksum.update(chunk)
    return checksum.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    checkout = args.checkout.resolve()
    problem = checkout / "data_structure/associative_array"
    hashes = json.loads((problem / "hash.json").read_text())
    cases = sorted((problem / "in").glob("*.in"))
    actual_names = {path.name for path in cases}
    actual_names.update(path.name for path in (problem / "out").glob("*.out"))
    if actual_names != set(hashes):
        raise RuntimeError("generated case names differ from official hash.json")
    for name, expected in hashes.items():
        location = problem / ("in" if name.endswith(".in") else "out") / name
        if digest(location) != expected:
            raise RuntimeError(f"official checksum mismatch: {name}")

    commit = subprocess.check_output(
        ["git", "-c", f"safe.directory={checkout}", "-C", str(checkout),
         "rev-parse", "HEAD"], text=True).strip()
    print(f"official_commit\t{commit}")
    print(f"verified_cases\t{len(cases)}")
    print("case\tqueries\tinput_bytes\tinput_sha256\telapsed_s\tmax_rss_kib")
    with tempfile.TemporaryDirectory(prefix="associative-array-official-") as temp:
        directory = Path(temp)
        binary = directory / "checker"
        subprocess.run(["g++", *FLAGS, str(SOURCE), "-o", str(binary)], check=True)
        output = directory / "answer.out"
        timing = directory / "time.txt"
        for case in cases:
            expected = hashes[case.with_suffix(".out").name]
            queries = int(case.open().readline())
            times = []
            memory = []
            for _ in range(args.repeats):
                with case.open("rb") as input_file, output.open("wb") as output_file:
                    subprocess.run(
                        ["/usr/bin/time", "-f", "%e %M", "-o", str(timing),
                         str(binary)], stdin=input_file, stdout=output_file,
                        check=True,
                    )
                if digest(output) != expected:
                    raise RuntimeError(f"wrong answer: {case.name}")
                seconds, kib = timing.read_text().split()
                times.append(seconds)
                memory.append(kib)
            print(f"{case.stem}\t{queries}\t{case.stat().st_size}\t{hashes[case.name]}"
                  f"\t{','.join(times)}\t{','.join(memory)}", flush=True)


if __name__ == "__main__":
    main()
