"""Universal Lean proof of the nested-vector `doubling` call: registration, axioms and linkage."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools'))
from test_scalar_ir import lean_environment

MODULES = ['DoublingNested', 'DoublingPrologue', 'DoublingInvoke', 'DoublingConstruct',
           'DoublingProgram', 'DoublingCall']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


class DoublingProofTests(unittest.TestCase):
    def lean(self, text, succeeds=True):
        with tempfile.TemporaryDirectory(prefix='doubling-proof-') as directory:
            path = Path(directory) / 'checks.lean'
            path.write_text(text)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(path)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, succeeds, result.stdout + result.stderr)
        return result.stdout

    def test_modules_are_registered_and_sorry_free(self):
        index = (ROOT / 'Proofs.lean').read_text()
        support = (ROOT / 'verifier/support.toml').read_text()
        component = (ROOT / 'library/array/doubling.toml').read_text()
        for module in MODULES:
            self.assertIn(f'import Proofs.{module}\n', index)
            if module == 'DoublingCall':
                self.assertIn('proof = "Proofs/DoublingCall.lean"', component)
            else:
                self.assertIn(f'"Proofs/{module}.lean"', support)
            source = (ROOT / f'Proofs/{module}.lean').read_text()
            self.assertNotIn('sorry', source)
            self.assertNotIn('admit', source)
            self.assertNotIn('\naxiom ', source)

    def test_theorem_uses_only_standard_axioms(self):
        output = self.lean('import Proofs.DoublingCall\n'
                           '#print axioms Proofs.DoublingCall.doubling_correct\n')
        listed = output.split('[', 1)[1].split(']', 1)[0]
        self.assertEqual({name.strip() for name in listed.split(',')}, ALLOWED_AXIOMS)

    def test_reference_table_and_body_linkage(self):
        prelude = ('import Proofs.DoublingCall\n'
                   'open Proofs.DoublingNested Proofs.DoublingPrologue\n')
        self.lean(prelude +
                  '#guard tableRow [1,2,0] 0 == [1,2,0]\n'
                  '#guard tableRow [1,2,0] 1 == [2,0,1]\n'
                  '#guard tableRow [1,2,0] 2 == [1,2,0]\n'
                  '#guard tableRow [0] 3 == [0]\n'
                  'example : Proofs.DoublingNestedInstance.doubling.body = bodyCmd := rfl\n')
        # a body that differs from the generated one must not be accepted
        self.lean(prelude +
                  'open Proofs.CppNestedProgram in\n'
                  'example : Proofs.DoublingNestedInstance.doubling.body =\n'
                  '    Command.sequence (.primitive .skip) bodyCmd := rfl\n', succeeds=False)

    def test_hypotheses_are_satisfiable_and_theorem_applies(self):
        # A concrete caller satisfies every hypothesis, so the theorem is not vacuous.
        self.lean(WITNESS)


WITNESS = r'''import Proofs.DoublingCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppVectorOwnership Proofs.DoublingNested Proofs.DoublingCall Proofs.DoublingPrologue Proofs.CppMixedInvoke

def vb : Proofs.CppVector.Buffer Value := ⟨0,[1,2,0].map Value.integer,4,64,0⟩
def callerState : NState :=
  let state : Proofs.CppNestedVectorStore.State := ⟨⟨[some ⟨atom,none,some 0,[]⟩]⟩,⟨[some vb],0,0,0⟩⟩
  { scalars := ⟨[⟨u64,5⟩],[⟨0,false⟩],0,0,0⟩,
    frame := ⟨state,[false],[⟨0,atom,false,.root 0⟩]⟩,
    slots := [Location.vector 0,Location.scalar 0],scope := 0,peak := 0 }

theorem witness : CallerOK callerState 0 0 0 0 false false vb := by
  refine ⟨by rfl,by rfl,by rfl,by rfl,by rfl,by rfl,by rfl,by decide,?_,by decide⟩
  intro owner c h
  rcases owner with _ | owner
  · have : callerState.frame.state.forest.rootOwner 0 = some 0 := by
      rw [rootOwner_eq]; decide
    simp only [Forest.context,this,Bind.bind,Option.bind] at h
    simp [callerState,Forest.lookup] at h
    simp [callerState]
    omega
  · have : callerState.frame.state.forest.rootOwner (owner+1) = none := by
      rw [rootOwner_eq]
      simp [callerState,Forest.lookup]
    simp [Forest.context,this] at h

example : ∃ Sinit fuel res, Proofs.CppNestedCall.prepare callerState
      Proofs.DoublingNestedInstance.doubling.parameters
      [.vectorReference 0,.value (.variable u64 1)] = some Sinit ∧
    Proofs.DoublingNestedInstance.doubling.callFuel fuel callerState [.vectorReference 0,.value (.variable u64 1)] =
      .finished (res,.vector callerState.frame.state.storage.objects.length (.vector atom)) ∧
    DoublingPost callerState Sinit res (NExpr.variable u64 1).nodes [1,2,0] 0 vb 5 :=
  doubling_correct callerState witness [1,2,0] rfl (by decide) (by decide) (.variable u64 1) 5 rfl rfl (by rfl)
    (by decide) (by decide)
'''


if __name__ == '__main__':
    unittest.main()
