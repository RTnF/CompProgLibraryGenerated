"""Scalar/write effects and scope exit before composition across control flow."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.CppNoResizeStmt Proofs.CppNoResizeScope Proofs.CppBufferHeaders Proofs.CppEvalFrame
 def action : NStmt := .declare i32 true rowRead
 def declared : NStep := (action.run state).getD ⟨state,none,false⟩
 theorem declaredEffects : Effects state declared := primitive action state declared rfl (by decide +kernel)
 example := Proofs.CppScalarFrame.scalar_frame action state declared rfl (by decide +kernel)
 def returned : NStep := ((NStmt.ret rowRead).run state).getD ⟨state,none,false⟩
 example := primitive (.ret rowRead) state returned rfl (by decide +kernel)
 #guard returned.returned == some (.scalar (-3))
 #guard declared.state.scope == state.scope
 #guard declared.state.scalars.memory.length == state.scalars.memory.length+1
 #guard declared.state.frame.state == state.frame.state
 def assignment : NStmt := .assign 3 i32 (.literal i32 0)
 def assigned : NStep := (assignment.run state).getD ⟨state,none,false⟩
 example := primitive assignment state assigned rfl (by decide +kernel)
 #guard assigned.state.frame.state == state.frame.state
 def checked : NStep := ((NStmt.check rowSize).run state).getD ⟨state,none,false⟩
 example := primitive (.check rowSize) state checked rfl (by decide +kernel)
 #guard ((NStmt.check (.literal i32 0)).run state).isNone
 def write : NStmt := .write (.row (.local 0) atom idx) i32 pos (.literal i32 42)
 def written : NStep := (write.run state).getD ⟨state,none,false⟩
 theorem writtenEffects : Effects state written := primitive write state written rfl (by decide +kernel)
 #guard written.state.scope == state.scope
 example : written.state.frame.state.liveSpace = state.frame.state.liveSpace := writtenEffects.headers.live
 theorem contexts : ∀ owner scope, state.frame.state.forest.context owner = some scope → scope ≤ state.scope := by
   intro owner scope found
   have inside : owner < state.frame.state.forest.objects.length := by
     by_cases inside : owner < state.frame.state.forest.objects.length
     · exact inside
     have missing := Proofs.CppVectorOwnership.lookup_past_end state.frame.state.forest owner (by omega)
     have root : state.frame.state.forest.rootOwner owner = none := by
       rw [Proofs.CppVectorOwnership.Forest.rootOwner]; simp [missing]
     simp [Proofs.CppVectorOwnership.Forest.context,root] at found
   have length : state.frame.state.forest.objects.length = 7 := by decide +kernel
   rw [length] at inside
   have bounds : (List.range 7).all (fun owner => (state.frame.state.forest.context owner).all
       (fun k => decide (k ≤ state.scope))) = true := by decide +kernel
   have bound := List.all_eq_true.mp bounds owner (List.mem_range.mpr inside)
   simpa [found] using bound
 def inner : NState := {declared.state with scope := state.scope+1}
 def left := (state.leave inner none).getD state
 example := leave_effect state inner left none declaredEffects.headers declaredEffects.flags trivial contexts (by decide +kernel)
 #guard left.scope == state.scope
 #guard left.frame.bindings == state.frame.bindings
 #guard left.scalars.memory == state.scalars.memory
 #guard (List.range 7).all (fun owner => left.frame.state.storage.lookup owner == state.frame.state.storage.lookup owner)
 def scalarLeft := (state.leave inner (some (.scalar 17))).getD state
 example := leave_effect state inner scalarLeft (some (.scalar 17)) declaredEffects.headers declaredEffects.flags
   trivial contexts (by decide +kernel)
 #guard Proofs.CppNoResizeScope.Allowed Proofs.UnionFindCandidateInstance.UnionFind_root.body
 #guard Proofs.CppNoResizeScope.Allowed Proofs.UnionFindCandidateInstance.UnionFind_same.body
 #guard Proofs.CppNoResizeScope.Allowed Proofs.UnionFindCandidateInstance.UnionFind_size.body
 #guard Proofs.CppNoResizeScope.Allowed Proofs.UnionFindCandidateInstance.UnionFind_unite.body
 #guard Proofs.CppNoResizeScope.Allowed Proofs.UnionFindCandidateInstance.UnionFind_num_groups.body
 example : Proofs.CppNoResizeScope.Allowed Proofs.UnionFindCandidateInstance.UnionFind_unite.body = true := by decide +kernel
 #guard !(Proofs.CppNoResizeScope.Allowed (.primitive (.reserve (.local 0) i32 (.literal i32 5))))
 #guard !(Proofs.CppNoResizeScope.Allowed (.primitive (.dedupVec (.local 0) i32)))
 #guard !(Proofs.CppNoResizeScope.Allowed (.primitive (.sortVec (.local 0) i32)))
 #guard !(Proofs.CppNoResizeScope.Allowed (.primitive (.declareVector i32 true)))
 #guard !(Proofs.CppNoResizeScope.Allowed (.primitive (.retVector 0)))
 example (stmt : NStmt) (s : NState) (out : NStep)
   (allowed : Proofs.CppNoResizeStmt.Allowed stmt = true) (ran : stmt.run s = some out) := primitive stmt s out allowed ran
 example (outer inner out : NState) (ret : Option Ret) (headers : SameHeaders outer.frame.state inner.frame.state)
   (flags : inner.frame.rootWritable = outer.frame.rootWritable) (value : ScalarResult ret)
   (ctx : ∀ owner scope, outer.frame.state.forest.context owner = some scope → scope ≤ outer.scope)
   (ran : outer.leave inner ret = some out) := leave_effect outer inner out ret headers flags value ctx ran
'''

class NoResizeTests(unittest.TestCase):
    def test_scalar_write_scope_and_generated_body_classification(self):
        with tempfile.TemporaryDirectory(prefix='cpp-no-resize-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppNoResizeScope\nimport Proofs.Generated.UnionFindCandidate\n'
                             +'\n'.join(fixture_checks())+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
