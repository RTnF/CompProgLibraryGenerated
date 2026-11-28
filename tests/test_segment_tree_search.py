"""The binary searches of SegmentTree (function-object arguments) against the generated Lean model."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from offline import disable_network
from lean_env import lean_environment
LAKE, LAKE_ENV = lean_environment()


class SegmentTreeSearchTests(unittest.TestCase):
    def test_searches_match_the_model(self):
        env = {**LAKE_ENV, "ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1"}
        with tempfile.TemporaryDirectory() as directory:
            binary = Path(directory) / "native"
            subprocess.run(["g++", "-std=c++23", "-O1", "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                            str(ROOT / "tests/imports/segment_tree_search.cpp"), "-o", str(binary)],
                           cwd=ROOT, env=env, check=True, timeout=120)
            native = subprocess.check_output([binary], cwd=ROOT, env=env, text=True, timeout=60)
            lean = subprocess.check_output([LAKE, "env", "lean", "--run", ROOT / "tests/lean/segment_tree_search.lean"],
                                           cwd=ROOT, env=env, text=True, timeout=600)
        self.assertEqual(len(native.splitlines()), 4000)
        self.assertEqual(lean, native)


if __name__ == "__main__":
    disable_network()
    unittest.main()
