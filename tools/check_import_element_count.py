"""Reproduce imported template defects and test the unproved run-count repair."""

from pathlib import Path
import os
import subprocess
import tempfile

from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent


def run_cpp_test(source, label):
    includes = ["-I", str(ROOT), "-I", str(ROOT / "experiments/library/cpp")]
    with tempfile.TemporaryDirectory(prefix="import-test-") as directory:
        for sanitizer in (False, True):
            binary = Path(directory) / "test"
            flags = FLAGS if not sanitizer else ["-std=c++17", "-O1", "-g", "-Wall", "-Wextra",
                "-pedantic", "-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
            subprocess.run(["g++", *flags, *includes, str(ROOT / source), "-o", str(binary)],
                           cwd=ROOT, check=True)
            environment = os.environ.copy()
            if sanitizer:
                # LeakSanitizer cannot run under this workspace's ptrace wrapper.
                # Address/undefined-behavior checks remain active and fail hard.
                environment["ASAN_OPTIONS"] = "detect_leaks=0:halt_on_error=1"
                environment["UBSAN_OPTIONS"] = "halt_on_error=1:print_stacktrace=1"
            subprocess.run([str(binary)], cwd=ROOT, env=environment, check=True)
            print(f"{label} passed (sanitizer={sanitizer})", flush=True)


def main():
    disable_network()
    check_compiler()
    includes = ["-I", str(ROOT), "-I", str(ROOT / "experiments/library/cpp")]
    reproduction = subprocess.run(
        ["g++", *FLAGS, *includes, "-fsyntax-only", "-fmax-errors=1",
         str(ROOT / "tests/imports/element_count.repro.cpp")],
        capture_output=True, text=True, cwd=ROOT)
    if (reproduction.returncode == 0 or "T = std::vector<int>" not in reproduction.stderr
            or "conversion from" not in reproduction.stderr):
        raise RuntimeError("original element_count type defect was not reproduced")
    print("original element_count template type defect reproduced")
    matrix = subprocess.run(
        ["g++", *FLAGS, *includes, "-fsyntax-only", "-fmax-errors=1",
         str(ROOT / "tests/imports/square_matrix.repro.cpp")],
        capture_output=True, text=True, cwd=ROOT)
    if matrix.returncode != 0:
        raise RuntimeError("fixed original SquareMatrix comparison did not compile: " + matrix.stderr)
    print("fixed original SquareMatrix comparison compiles")
    run_cpp_test("tests/imports/element_count.cpp",
                 "element_count repair and original char_count exhaustive tests")


if __name__ == "__main__":
    main()
