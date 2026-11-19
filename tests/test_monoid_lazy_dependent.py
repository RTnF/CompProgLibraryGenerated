"""Compare dependent monoid operations with the generated model."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from offline import disable_network
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()


class MonoidLazyDependentTests(unittest.TestCase):
    def test_dependent_operations(self):
        env = {**LAKE_ENV,
               "ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1"}
        with tempfile.TemporaryDirectory() as directory:
            binary = Path(directory) / "native"
            subprocess.run(["g++", "-std=c++17", "-O1", "-fsanitize=address,undefined",
                            "-fno-sanitize-recover=all", "-I", str(ROOT / "experiments/library/cpp"),
                            str(ROOT / "tests/imports/monoid_lazy_dependent.cpp"), "-o", str(binary)],
                           cwd=ROOT, env=env, check=True, timeout=60)
            native = subprocess.check_output([binary], cwd=ROOT, env=env, text=True, timeout=30)
            lean = subprocess.check_output(
                [LAKE, "env", "lean", "--run",
                 ROOT / "tests/lean/monoid_lazy_dependent.lean"],
                cwd=ROOT, env=env, text=True, timeout=60)
        self.assertEqual(native.splitlines(), ["51", "9007199254740992", "7", "24", "22"])
        self.assertEqual(lean, native)


if __name__ == "__main__":
    disable_network()
    unittest.main()
