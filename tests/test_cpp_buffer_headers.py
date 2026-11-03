"""General expression effects, nested aliases and element-only buffer writes."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CHECKS = '''
open Proofs.CppEvalFrame Proofs.CppBufferHeaders
 def evaluated (e : NExpr) := (e.eval state).getD (state,0)
 def expressions : List NExpr := [
   .literal i32 7,idx,.cast ⟨64,false,false⟩ idx,.targetCast ⟨8,false,false⟩ (.literal i32 (-1)),
   .unary i32 .neg idx,.binary i32 .add rowRead (.literal i32 3),
   .divrem i32 false rowRead (.literal i32 2),.divrem i32 true rowRead (.literal i32 2),
   .logical true (.literal i32 0) (.divrem i32 false (.literal i32 1) (.literal i32 0)),
   .logical false (.literal i32 1) (.read i32 (.local 2) (.literal i32 999)),
   .logical true (.literal i32 1) rowRead,.logical false (.literal i32 0) rowRead,
   rootSize,rowSize,rowRead]
 #guard expressions.all (fun e => (e.eval state).isSome)
 #guard expressions.all (fun e => (evaluated e).1.frame.state == state.frame.state &&
   (evaluated e).1.frame.rootWritable == state.frame.rootWritable)
 example := expression_frame rowRead state (evaluated rowRead).1 (evaluated rowRead).2 (by decide +kernel)
 example := expression_frame rowSize state (evaluated rowSize).1 (evaluated rowSize).2 (by decide +kernel)
 #guard (evaluated rowRead).1.frame.bindings.length == state.frame.bindings.length+1
 #guard (evaluated rowRead).2 == (-3)
 #guard (evaluated (.targetCast ⟨8,false,false⟩ (.literal i32 (-1)))).2 == 255
 def childPair := (Container.row (.local 1) atom idx).eval state
 def child := childPair.getD (state,0)
 example := container_frame (.row (.local 1) atom idx) state child.1 child.2 (by decide +kernel)
 #guard child.2 == state.frame.bindings.length
 def old : Proofs.CppVector.Buffer Value := (child.1.frame.state.storage.lookup 4).getD ⟨4,[],0,64,0⟩
 def next : Frame := child.1.frame.updated 4 old ⟨{old with items := old.items.set 1 (.integer 42)},(),1,old.capacity+2⟩
 theorem writtenHeaders : SameHeaders child.1.frame.state next.state :=
   write_headers child.1.frame 4 1 old (.integer 42) (by decide +kernel) (by decide +kernel)
 example : next.state.liveSpace = child.1.frame.state.liveSpace := writtenHeaders.live
 def saved := child.1.frame.elementRef child.2 i32 1
 #guard saved.isSome
 #guard saved.bind child.1.frame.read == some (-3)
 #guard saved.bind next.read == some 42
 #guard next.bindings == child.1.frame.bindings
 #guard next.rootWritable == child.1.frame.rootWritable
 #guard next.state.storage.lookup 2 == child.1.frame.state.storage.lookup 2
 #guard ((next.state.storage.lookup 4).map signature) == some (signature old)
 def second : Frame := next.updated 4 {old with items := old.items.set 1 (.integer 42)}
   ⟨{old with items := (old.items.set 1 (.integer 42)).set 0 (.integer 99)},(),1,old.capacity+2⟩
 theorem secondHeaders : SameHeaders next.state second.state :=
   write_headers next 4 0 _ (.integer 99) (by decide +kernel) (by decide +kernel)
 example := writtenHeaders.trans secondHeaders
 #guard saved.bind second.read == some 42
 def changedEpoch := child.1.frame.updated 4 old ⟨{old with epoch := old.epoch+1},(),1,old.capacity+2⟩
 example : ¬ SameHeaders child.1.frame.state changedEpoch.state := by
   intro same
   have found := same.buffers 4
   have different : (changedEpoch.state.storage.lookup 4).map signature ≠
       (child.1.frame.state.storage.lookup 4).map signature := by decide +kernel
   exact different found
 #guard (saved.bind changedEpoch.read).isNone
 def assignment : NStmt := .write (.row (.local 0) atom idx) i32 pos (.literal i32 42)
 def assigned : NState := match assignment.run child.1 with
   | some step => step.state
   | none => child.1
 example := Proofs.CppWriteHeaders.stmt_write child.1 assigned (.row (.local 0) atom idx) i32 pos
   (.literal i32 42) (by decide +kernel)
 #guard saved.bind assigned.frame.read == some 42
 #guard assigned.frame.bindings == child.1.frame.bindings
 #guard assigned.frame.rootWritable == child.1.frame.rootWritable
 #guard assigned.frame.state.storage.lookup 2 == child.1.frame.state.storage.lookup 2
 #guard ((NStmt.write (.row (.local 1) atom idx) i32 pos (.literal i32 42)).run state).isNone
 example (e : NExpr) (s t : NState) (v : Int) (ran : e.eval s = some (t,v)) := expression_frame e s t v ran
 example (c : Container) (s t : NState) (v : Nat) (ran : c.eval s = some (t,v)) := container_frame c s t v ran
 example (f : Frame) (owner index : Nat) (buffer : Proofs.CppVector.Buffer Value) (value : Value)
   (bound : owner < f.state.storage.objects.length) (found : f.state.storage.lookup owner = some buffer) :=
   write_headers f owner index buffer value bound found
'''

class BufferHeaderTests(unittest.TestCase):
    def test_all_expressions_and_nested_write_aliases(self):
        with tempfile.TemporaryDirectory(prefix='cpp-buffer-headers-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppWriteHeaders\n'+'\n'.join(fixture_checks())+CHECKS)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
