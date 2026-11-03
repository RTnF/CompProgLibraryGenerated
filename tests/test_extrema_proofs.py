"""A C++ boundary mutation must invalidate the universal generated-model proof."""

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


class ExtremaProofTests(unittest.TestCase):
    def test_boundary_change_invalidates_the_universal_proof(self):
        with tempfile.TemporaryDirectory(prefix="extrema-proof-mutation-") as directory:
            scratch = Path(directory)
            candidate = (ROOT / "experiments/verification/template/update_extrema.hpp").read_text()
            self.assertIn("if (a < b)", candidate)
            source = scratch / "mutation.cpp"
            declarations = (ROOT / "tests/imports/update_extrema_instantiations.cpp").read_text().splitlines()[2:]
            source.write_text(candidate.replace("if (a < b)", "if (a <= b)") + "\n" +
                              "\n".join(declarations) + "\n")
            generated = emit_lean(lower_source(source), "Proofs.ExtremaInstances")
            proof = (ROOT / "Proofs/ExtremaProofs.lean").read_text()
            self.assertTrue(proof.startswith("import Proofs.ExtremaInstances\n"))
            combined = scratch / "mutation.lean"
            combined.write_text(generated + proof.split("\n", 1)[1])
            lake, env = lean_environment()
            result = subprocess.run([lake, "env", "lean", str(combined)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unsolved goals", result.stdout + result.stderr)


if __name__ == "__main__":
    disable_network()
    lake, env = lean_environment()
    subprocess.run([lake, "build", "Proofs.ExtremaProofs"], cwd=ROOT, env=env, check=True)
    unittest.main()
