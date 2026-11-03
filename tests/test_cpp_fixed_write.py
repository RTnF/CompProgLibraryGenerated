"""Expression binding prefixes and element writes confined to slot 0's owner."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.CppExprPrefix Proofs.CppFixedWrite
 def readonlyEntry : NState := ((rowRead.eval state).getD (state,0)).1
 def extraEntry : NState := {readonlyEntry with frame :=
   (readonlyEntry.frame.addBinding ⟨2,atom,false,.root 1⟩).1}
 def mutableRead : NExpr := .read i32 (.row (.local 0) atom idx) pos
 def mutableEntry : NState := ((mutableRead.eval extraEntry).getD (extraEntry,0)).1
 def focused : NState := {mutableEntry with slots := [.vector 5,.vector 1,.vector 2,.scalar 0,.scalar 1]}
 def rootBinding : Binding := focused.frame.bindings[5]?.getD ⟨4,atom,true,.root 0⟩
 theorem target : Target focused 4 := ⟨5,rootBinding,by decide +kernel,by decide +kernel,by decide +kernel⟩
 #guard focused.vectorSlot 0 == some 5
 #guard rootBinding.owner == 4
 def rhs : NExpr := .binary i32 .add (.read i32 (.local 2) (.literal i32 0)) rowRead
 def offset : NExpr := .binary i32 .add rowRead (.literal i32 4)
 def rhsOut := (rhs.eval focused).getD (focused,0)
 example := expression_prefix rhs focused rhsOut.1 rhsOut.2 (by decide +kernel)
 example := release_frame rhs focused rhsOut.1 rhsOut.2 (by decide +kernel)
 example := target_prefix focused rhsOut.1 4 target (expression_prefix rhs focused rhsOut.1 rhsOut.2 (by decide +kernel))
 #guard rhsOut.2 == 74
 #guard rhsOut.1.frame.bindings.length == focused.frame.bindings.length+1
 #guard (rhsOut.1.release focused).frame == focused.frame
 #guard rhsOut.1.slots == focused.slots
 def step : NStep := ((NStmt.write (.local 0) i32 offset rhs).run focused).getD ⟨focused,none,false⟩
 example := write_local focused step 4 i32 offset rhs target (by decide +kernel)
 #guard step.state.frame.bindings == focused.frame.bindings
 #guard step.state.slots == focused.slots
 #guard step.state.vectorSlot 0 == some 5
 #guard (step.state.frame.state.storage.lookup 4).map (fun b => b.items) == some [.integer 17,.integer 74]
 #guard (List.range 7).all (fun owner => owner == 4 ||
   step.state.frame.state.storage.lookup owner == focused.frame.state.storage.lookup owner)
 def saved := focused.frame.elementRef 3 i32 1
 #guard saved.bind focused.frame.read == some (-3)
 #guard saved.bind step.state.frame.read == some 74
 def declared : NStep := ((NStmt.declare i32 true rhs).run focused).getD ⟨focused,none,false⟩
 example := scalar_full_frame (.declare i32 true rhs) focused declared rfl (by decide +kernel)
 example := scalar_target (.declare i32 true rhs) focused declared 4 rfl target (by decide +kernel)
 #guard declared.state.frame == focused.frame
 #guard declared.state.slots.length == focused.slots.length+1
 #guard declared.state.vectorSlot 0 == some 5
 #guard ((NStmt.write (.local 0) i32 offset rhs).run {focused with slots := [.vector 3,.vector 1,.vector 2,.scalar 0,.scalar 1]}).isNone
 def rhsOutOfScope : NExpr := .logical true (.literal i32 0) (.read i32 (.local 2) (.literal i32 999))
 def short := (rhsOutOfScope.eval focused).getD (focused,0)
 example := release_frame rhsOutOfScope focused short.1 short.2 (by decide +kernel)
 #guard (short.1.release focused).frame == focused.frame
 example (e : NExpr) (s t : NState) (value : Int) (ran : e.eval s = some (t,value)) := release_frame e s t value ran
 example (s : NState) (out : NStep) (owner : Nat) (ty : Ty) (index value : NExpr)
   (target : Target s owner) (ran : (NStmt.write (.local 0) ty index value).run s = some out) :=
   write_local s out owner ty index value target ran
 example (stmt : NStmt) (s : NState) (out : NStep) (owner : Nat)
   (form : Proofs.CppScalarFrame.Scalar stmt = true) (target : Target s owner) (ran : stmt.run s = some out) :=
   scalar_target stmt s out owner form target ran
'''

class FixedWriteTests(unittest.TestCase):
    def test_expression_prefix_and_fixed_owner_primitive(self):
        with tempfile.TemporaryDirectory(prefix='cpp-fixed-write-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppFixedWrite\n'+'\n'.join(fixture_checks())+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
