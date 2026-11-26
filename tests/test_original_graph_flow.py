"""Exercise the imported FlowGraph's residual-edge and distance boundary cases."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class OriginalGraphFlowTests(unittest.TestCase):
    def test_residual_and_cost_boundaries(self):
        with tempfile.TemporaryDirectory(prefix="graph-flow-original-") as directory:
            binary = Path(directory) / "graph_flow_source"
            subprocess.run([
                "g++", "-std=c++17", "-O1", "-g", "-Wall", "-Wextra", "-pedantic",
                "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                "-fno-omit-frame-pointer", "-no-pie",
                "-I", str(ROOT / "experiments/library/cpp"),
                str(ROOT / "tests/imports/graph_flow_source.cpp"),
                "-o", str(binary),
            ], check=True, timeout=60)
            environment = dict(os.environ, ASAN_OPTIONS="detect_leaks=0:halt_on_error=1",
                               UBSAN_OPTIONS="halt_on_error=1")
            subprocess.run([str(binary)], check=True, env=environment, timeout=30)


if __name__ == "__main__":
    unittest.main()
