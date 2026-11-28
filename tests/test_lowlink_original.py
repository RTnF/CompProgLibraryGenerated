"""Check both ListGraph lowlink implementations against edge-occurrence removal."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class OriginalLowlinkTests(unittest.TestCase):
    def test_multigraph(self):
        for public in (False, True):
            with self.subTest(public=public):
                self.check_multigraph(public)

    def check_multigraph(self, public):
        with tempfile.TemporaryDirectory(prefix="lowlink-original-") as directory:
            binary = Path(directory) / "lowlink_multigraph"
            defines = ["-DVERIFY_PUBLIC_LOWLINK"] if public else []
            subprocess.run([
                "g++", "-std=c++23", "-O1", "-g", "-Wall", "-Wextra", "-pedantic",
                "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                "-fno-omit-frame-pointer", "-no-pie", *defines,
                "-I", str(ROOT / "experiments/library/cpp"),
                str(ROOT / "tests/imports/lowlink_multigraph.cpp"),
                "-o", str(binary),
            ], check=True, timeout=60)
            environment = dict(os.environ, ASAN_OPTIONS="detect_leaks=0:halt_on_error=1",
                               UBSAN_OPTIONS="halt_on_error=1")
            subprocess.run([str(binary)], check=True, env=environment, timeout=30)


if __name__ == "__main__":
    unittest.main()
