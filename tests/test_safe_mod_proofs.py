"""Source operator changes must invalidate safe_mod's universal proof."""

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


class SafeModProofTests(unittest.TestCase):
    def test_operator_changes_invalidate_universal_proof(self):
        candidate = (ROOT / "library/safe_mod.hpp").read_text()
        proof = (ROOT / "Proofs/SafeModProofs.lean").read_text()
        frame = (ROOT / "Proofs/SafeModFrame.lean").read_text()
        invoke = (ROOT / "Proofs/SafeModInvoke.lean").read_text()
        self.assertTrue(proof.startswith("import Proofs.Generated.SafeMod\n"))
        lake, env = lean_environment()
        with tempfile.TemporaryDirectory(prefix="safe-mod-proof-") as directory:
            scratch = Path(directory)
            source, combined = scratch / "source.cpp", scratch / "mutation.lean"
            for before, after in [("x %= m", "x %= m"), ("x %= m", "x /= m"), ("x += m", "x -= m")]:
                with self.subTest(mutation=after):
                    self.assertIn(before, candidate)
                    source.write_text(candidate.replace(before, after))
                    generated = emit_lean(lower_source(source), "Proofs.SafeModInstance")
                    combined.write_text("import Proofs.CppBaseFrame\n" + generated + proof.split("\n", 1)[1] +
                        frame.split("\n", 2)[2] + invoke.split("\n", 1)[1])
                    result = subprocess.run([lake, "env", "lean", str(combined)], cwd=ROOT,
                                            env=env, capture_output=True, text=True)
                    if before == after:
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("unsolved goals", result.stdout + result.stderr)


if __name__ == "__main__":
    disable_network()
    lake, env = lean_environment()
    subprocess.run([lake, "build", "Proofs.SafeModInvoke"], cwd=ROOT, env=env, check=True)
    unittest.main()
