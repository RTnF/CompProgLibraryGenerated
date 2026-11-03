"""C++ arithmetic and control-flow changes invalidate generated-state proofs."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
from state_ir import lower_source, emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network


class FloorSumStateTests(unittest.TestCase):
    def test_source_changes_invalidate_state_proofs(self):
        original = (ROOT / "experiments/library/cpp/number_theory/floor_sum.hpp").read_text()
        proof = (ROOT / "Proofs/FloorSumState.lean").read_text()
        arithmetic = (ROOT / "Proofs/FloorSumArithmetic.lean").read_text()
        reduction = (ROOT / "Proofs/FloorSumReduction.lean").read_text()
        normalization = (ROOT / "Proofs/FloorSumNormalization.lean").read_text()
        a_normalization = (ROOT / "Proofs/FloorSumANormalization.lean").read_text()
        reciprocity = (ROOT / "Proofs/FloorSumReciprocity.lean").read_text()
        round_proof = (ROOT / "Proofs/FloorSumRound.lean").read_text()
        call_proof = (ROOT / "Proofs/FloorSumCall.lean").read_text()
        work_frame = (ROOT / "Proofs/FloorSumWorkFrame.lean").read_text()
        invoke_proof = (ROOT / "Proofs/FloorSumInvoke.lean").read_text()
        self.assertTrue(proof.startswith("import Proofs.Generated.FloorSumUnsigned\n"))
        lake, env = lean_environment()
        with tempfile.TemporaryDirectory(prefix="floor-sum-state-") as directory:
            scratch = Path(directory)
            source, combined = scratch / "source.cpp", scratch / "combined.lean"
            for before, after in [("a >= m", "a >= m"),
                                  ("a >= m", "a > m"), ("b >= m", "b > m"),
                                  ("a * n + b", "a * n - b"),
                                  ("y_max < m", "y_max <= m"),
                                  ("break;", "ans += 1;"),
                                  ("while (true)", "while (false)"),
                                  ("y_max / m", "y_max % m"),
                                  ("y_max % m", "y_max / m"),
                                  ("swap(m, a)", "swap(n, a)"),
                                  ("n * (b / m)", "n + (b / m)"),
                                  ("n * (b / m)", "n * (b % m)"),
                                  ("b %= m", "b /= m"),
                                  ("n - 1", "n + 1"),
                                  ("n * (n - 1) / 2", "n * (n - 1) / 3"),
                                  ("n * (n - 1) / 2 * (a / m)", "n * (n - 1) * (a / m) / 2"),
                                  ("a %= m", "a /= m"),
                                  ("ull ans = 0;", "ull ans = 1;"),
                                  ("return ans;", "return n;"),
                                  ("return ans;", "return ans + 1;")]:
                with self.subTest(mutation=after):
                    self.assertIn(before, original)
                    source.write_text(original.replace(before, after))
                    generated = emit_lean(lower_source(source, "floor_sum_unsigned",
                        [ROOT / "experiments/library/cpp"]), "Proofs.FloorSumUnsignedInstance")
                    combined.write_text("import Proofs.CppWorkFrame\nimport Proofs.CppBaseFrame\n" + generated + arithmetic.split("\n", 1)[1] +
                        proof.split("\n", 2)[2] + reduction.split("\n", 1)[1] +
                        normalization.split("\n", 1)[1] + a_normalization.split("\n", 1)[1] +
                        reciprocity.split("\n", 1)[1] + round_proof.split("\n", 3)[3] +
                        call_proof.split("\n", 1)[1] + work_frame.split("\n", 3)[3] + invoke_proof.split("\n", 1)[1])
                    result = subprocess.run([lake, "env", "lean", str(combined)], cwd=ROOT,
                        env=env, capture_output=True, text=True)
                    if before == after:
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("type mismatch", (result.stdout + result.stderr).lower())


if __name__ == "__main__":
    disable_network()
    lake, env = lean_environment()
    subprocess.run([lake, "build", "Proofs.FloorSumInvoke"],
                   cwd=ROOT, env=env, check=True)
    unittest.main()
