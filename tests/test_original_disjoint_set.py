"""Exercise the library3 DisjointSet against the same oracle as its public port."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class OriginalDisjointSetTests(unittest.TestCase):
    def test_original_disjoint_set(self):
        with tempfile.TemporaryDirectory(prefix="original-disjoint-set-") as directory:
            binary = Path(directory) / "disjoint_set"
            subprocess.run([
                "g++", "-std=c++23", "-O1", "-g", "-Wall", "-Wextra", "-pedantic",
                "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                "-fno-omit-frame-pointer", "-no-pie",
                "-I", str(ROOT / "experiments/library3/cpp"),
                str(ROOT / "tests/imports/disjoint_set.cpp"), "-o", str(binary),
            ], check=True, timeout=60)
            environment = dict(os.environ, ASAN_OPTIONS="detect_leaks=0:halt_on_error=1",
                               UBSAN_OPTIONS="halt_on_error=1")
            subprocess.run([str(binary)], check=True, env=environment, timeout=30)


if __name__ == "__main__":
    unittest.main()
