"""Check original and candidate matrix repairs, without claiming a Lean proof."""

import subprocess
import sys

from check_import_element_count import ROOT, run_cpp_test
from check_public import FLAGS, check_compiler
from offline import disable_network

sys.path.insert(0, str(ROOT / "verifier"))
from clang_ast import clang_command


def main():
    disable_network()
    check_compiler()
    includes = ["-I", str(ROOT), "-I", str(ROOT / "experiments/library/cpp")]
    unary = subprocess.run(
        ["g++", *FLAGS, *includes, "-Werror=unused-value", "-fsyntax-only",
         str(ROOT / "tests/imports/square_matrix_unary.repro.cpp")],
        capture_output=True, text=True, cwd=ROOT)
    if unary.returncode != 0:
        raise RuntimeError("fixed unary matrix negation did not compile: " + unary.stderr)
    run_cpp_test("tests/imports/square_matrix_unary.repro.cpp", "fixed original unary matrix negation")
    run_cpp_test("tests/imports/square_matrix_power.repro.cpp", "fixed original discarded-square overflow")
    run_cpp_test("tests/imports/square_matrix_source.cpp", "original SquareMatrix API and arithmetic regression")
    candidate = ROOT / "experiments/verification/number/square_matrix.hpp"
    subprocess.run(clang_command() + [str(candidate)], cwd=ROOT, check=True)
    run_cpp_test("tests/imports/square_matrix.cpp", "SquareMatrix repair exhaustive tests")


if __name__ == "__main__":
    main()
