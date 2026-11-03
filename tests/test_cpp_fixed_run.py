"""Fixed-owner value preservation through real nested control-flow execution."""
from pathlib import Path
import subprocess
import tempfile
import unittest
import re
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from test_cpp_fixed_write import CHECKS as FIXTURE
from test_cpp_no_resize import CHECKS as SCALAR_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CONTEXTS = re.sub(r'(?<![.\w])state\b', 'focused', SCALAR_CHECKS[SCALAR_CHECKS.index(' theorem contexts'):SCALAR_CHECKS.index(' def inner')].replace('theorem contexts','theorem focusedContexts'))
CHECKS = r'''
 def fixedBody : Command := .sequence
   (.primitive (.declare i32 true (.binary i32 .sub rowRead rowRead)))
   (.sequence
     (.whileLoop (.binary ⟨1,false,true⟩ .lt (.variable i32 5) (.literal i32 3))
       (.scope (.sequence (.primitive (.declare i32 false rowRead))
         (.sequence (.primitive (.write (.local 0) i32 (.literal i32 1)
           (.binary i32 .add (.literal i32 100) (.variable i32 5))))
           (.primitive (.assign 5 i32 (.binary i32 .add (.variable i32 5) (.literal i32 1))))))))
     (.branch (.literal i32 0) (.primitive (.check (.literal i32 0))) (.primitive (.ret rowRead))))
 def fixedResult : NStep := match Proofs.CppNestedProgram.runFuel 128 fixedBody focused with
   | .finished step => step | _ => ⟨focused,none,false⟩
 theorem fixedEffects : Proofs.CppFixedRun.Effects focused fixedResult 4 :=
   Proofs.CppFixedRun.run_values 128 fixedBody focused fixedResult 4 (by decide +kernel) target focusedContexts (by decide +kernel)
 #guard fixedResult.returned == some (.scalar 102)
 #guard fixedResult.state.scope == focused.scope
 #guard fixedResult.state.frame.bindings == focused.frame.bindings
 #guard fixedResult.state.slots == focused.slots++[.scalar focused.scalars.bindings.length]
 #guard fixedResult.state.scalars.memory.length == focused.scalars.memory.length+1
 #guard (fixedResult.state.frame.state.storage.lookup 4).map (fun b => b.items) == some [.integer 17,.integer 102]
 #guard (List.range 7).all (fun owner => owner == 4 || fixedResult.state.frame.state.storage.lookup owner == focused.frame.state.storage.lookup owner)
 example := fixedEffects.other 2 (by decide)
 example := fixedEffects.base.headers.live
 example := fixedEffects.target
 def fixedEarly : Command := .sequence
   (.scope (.branch (.literal i32 1) (.primitive (.ret rowRead)) (.primitive (.check (.literal i32 0)))))
   (.primitive (.check (.literal i32 0)))
 def fixedEarlyResult : NStep := match Proofs.CppNestedProgram.runFuel 32 fixedEarly focused with
   | .finished step => step | _ => ⟨focused,none,false⟩
 example := Proofs.CppFixedRun.run_values 32 fixedEarly focused fixedEarlyResult 4
   (by decide +kernel) target focusedContexts (by decide +kernel)
 #guard fixedEarlyResult.returned == some (.scalar (-3))
 #guard fixedEarlyResult.state.slots == focused.slots
 #guard fixedEarlyResult.state.frame.bindings == focused.frame.bindings
 def fixedBroken : Command := .whileLoop (.binary ⟨1,false,true⟩ .eq rowRead (.literal i32 (-3)))
   (.scope (.sequence (.primitive (.write (.local 0) i32 (.literal i32 1) (.literal i32 88))) .breakLoop))
 def fixedBrokenResult : NStep := match Proofs.CppNestedProgram.runFuel 32 fixedBroken focused with
   | .finished step => step | _ => ⟨focused,none,true⟩
 example := Proofs.CppFixedRun.run_values 32 fixedBroken focused fixedBrokenResult 4
   (by decide +kernel) target focusedContexts (by decide +kernel)
 #guard !fixedBrokenResult.breaking && fixedBrokenResult.returned.isNone
 #guard saved.bind fixedBrokenResult.state.frame.read == some 88
 example := Proofs.CppFixedRun.run_values 8 (.whileLoop (.literal i32 0) (.primitive (.check (.literal i32 0)))) focused
   ⟨(focused.charge 1 1).charge 1 0,none,false⟩ 4 rfl target focusedContexts (by decide +kernel)
 #guard Proofs.CppFixedRun.Allowed Proofs.UnionFindCandidateInstance.UnionFind_root.body
 #guard Proofs.CppFixedRun.Allowed Proofs.UnionFindCandidateInstance.UnionFind_same.body
 #guard Proofs.CppFixedRun.Allowed Proofs.UnionFindCandidateInstance.UnionFind_size.body
 #guard Proofs.CppFixedRun.Allowed Proofs.UnionFindCandidateInstance.UnionFind_unite.body
 #guard Proofs.CppFixedRun.Allowed Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body
 #guard !(Proofs.CppFixedRun.Allowed (.primitive (.write (.local 1) i32 pos rhs)))
 #guard !(Proofs.CppFixedRun.Allowed (.primitive (.write (.row (.local 0) atom idx) i32 pos rhs)))
 #guard !(Proofs.CppFixedRun.Allowed (.primitive (.reserve (.local 0) i32 pos)))
 example (fuel : Nat) (command : Command) (s : NState) (out : NStep) (root : Nat)
   (allowed : Proofs.CppFixedRun.Allowed command = true) (target : Target s root)
   (ctx : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
   (ran : Proofs.CppNestedProgram.runFuel fuel command s = .finished out) :=
   Proofs.CppFixedRun.run_values fuel command s out root allowed target ctx ran
'''

class FixedRunTests(unittest.TestCase):
    def test_nested_control_fixed_owner_values(self):
        with tempfile.TemporaryDirectory(prefix='cpp-fixed-run-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppFixedRun\nimport Proofs.Generated.UnionFindCandidate\n'
                             +'\n'.join(fixture_checks())+FIXTURE+CONTEXTS+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
