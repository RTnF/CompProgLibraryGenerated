"""Captured reference validity, including rejected reads, across real calls."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from test_cpp_no_resize import CHECKS as SCALAR_CHECKS
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_constructed_receiver import CHECKS as RECEIVER_CHECKS
from test_union_find_receiver_trace import CHECKS as TRACE_CHECKS
from test_union_find_rank_doubling import CHECKS as RANK_CHECKS
from test_cpp_call_metadata import METADATA
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
NESTED = '''
open Proofs.CppReferenceHeaders Proofs.CppCallFrame
 def entry : NState := ((rowRead.eval state).getD (state,0)).1
 def captured := (entry.frame.elementRef 3 i32 1).getD ⟨0,i32,false,⟨0,0,0⟩⟩
 def update : Proofs.CppNestedCall.NProgram :=
   ⟨[.nested i32 true,.scalar i32 false true,.scalar i32 false true],.scalar i32,
     .sequence (.primitive (.write (.row (.local 0) atom (.variable i32 1)) i32 (.variable i32 2) (.literal i32 42)))
       (.primitive (.ret (.read i32 (.row (.local 0) atom (.variable i32 1)) (.variable i32 2))))⟩
 def arguments : List Proofs.CppNestedCall.NArgument := [.vectorReference 0,.value idx,.value pos]
 def updated : NState := match update.callFuel 32 entry arguments with
   | .finished (out,_) => out
   | _ => state
 theorem entryContexts : ∀ owner scope, entry.frame.state.forest.context owner = some scope → scope ≤ entry.scope := by
   have frame := Proofs.CppEvalFrame.expression_frame rowRead state entry (-3) (by decide +kernel)
   have scopeEq := Proofs.CppEvalScope.expression_scope rowRead state entry (-3) (by decide +kernel)
   intro owner scope found
   rw [frame.1] at found
   rw [scopeEq]
   exact contexts owner scope found
 theorem effects : CallEffects entry updated := call_headers update 32 entry updated arguments (.scalar 42) i32
   rfl rfl entryContexts (by decide +kernel)
 example := read_kept entry updated captured (-3) effects (by decide +kernel) (by decide +kernel)
 example (reference : Reference) := read_isSome entry updated reference effects (by decide +kernel) (by decide +kernel)
 #guard entry.frame.read captured == some (-3)
 #guard updated.frame.read captured == some 42
 #guard entry.frame.grant captured == some false
 #guard updated.frame.grant captured == some false
 def rejected : List Reference := [
   {captured with address := {captured.address with epoch := captured.address.epoch+1}},
   {captured with address := {captured.address with owner := 2}},
   {captured with address := {captured.address with index := 999}},
   {captured with element := ⟨64,false,false⟩},
   {captured with writable := true},
   {captured with slot := 999}]
 #guard rejected.all (fun ref => (entry.frame.read ref).isNone && (updated.frame.read ref).isNone)
 #guard (captured::rejected).all (fun ref => (entry.frame.read ref).isSome == (updated.frame.read ref).isSome)
 #guard updated.frame.state.storage.lookup 2 == entry.frame.state.storage.lookup 2
 #guard updated.frame.state.storage.lookup 0 == entry.frame.state.storage.lookup 0
 def rowBuffer : Proofs.CppVector.Buffer Value := (entry.frame.state.storage.lookup 4).getD ⟨4,[],0,64,0⟩
 def malformed : NState := {entry with frame := (entry.frame.updated 4 rowBuffer ⟨{rowBuffer with items := rowBuffer.items.set 1 (.integer 2147483648)},(),1,rowBuffer.capacity+2⟩)}
 theorem malformedShape : CallEffects entry malformed :=
   ⟨Proofs.CppBufferHeaders.write_headers entry.frame 4 1 rowBuffer (.integer 2147483648)
     (by decide +kernel) (by decide +kernel),rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
 example := (effects_symm entry malformed malformedShape).trans effects
 #guard !malformed.frame.state.wellFormed
 #guard (malformed.frame.read captured).isNone
 #guard (updated.frame.read captured).isSome
 example (s t : NState) (r : Reference) (value : Int) (effects : CallEffects s t)
   (valid : t.frame.state.wellFormed = true) (read : s.frame.read r = some value) := read_kept s t r value effects valid read
 example (s t : NState) (r : Reference) (effects : CallEffects s t)
   (before : s.frame.state.wellFormed = true) (after : t.frame.state.wellFormed = true) := read_isSome s t r effects before after
'''
UNION_FIND = '''
open Proofs.CppReferenceHeaders Proofs.UfReceiverReferences
 def held : Reference := freshRef.getD ⟨0,i32,false,⟨0,0,0⟩⟩
 example := read_kept built final held (-1) finalEffects (by decide +kernel) (by decide +kernel)
 example (reference : Reference) := read_isSome built final reference finalEffects (by decide +kernel) (by decide +kernel)
 example := actual_calls_reads (List.replicate mixed.length 128) mixed built final (layoutOf populated)
   [4,0,2,0,2,0,0,1,4,1,0,1] (by decide +kernel) (by decide +kernel) builtContexts (by decide +kernel)
 example := calls_work_reads mixed built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong mixedAllowed
 #guard built.frame.read held == some (-1)
 #guard final.frame.read held == some 0
 #guard (final.frame.read {held with address := {held.address with epoch := 1}}).isNone
 #guard (built.frame.read {held with address := {held.address with epoch := 1}}).isNone
 #guard (final.frame.read {held with address := {held.address with index := 4}}).isNone
 #guard (built.frame.read {held with address := {held.address with index := 4}}).isNone
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (allowed : ∀ op ∈ ops, op.allowed ps.length) := calls_work_reads ops s layout ps count rank strong allowed
 example (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
   (ps vec : List Int) (count nextCount : Int) (rank nextRank : Nat → Nat)
   (before : Represents s layout ps count rank) (after : Represents out layout vec nextCount nextRank)
   (ran : call fuel s layout op = .finished (out,ret)) := call_reads fuel s out layout op ret
     ps vec count nextCount rank nextRank before after ran
'''

class ReferenceHeaderTests(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory(prefix='cpp-reference-headers-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text(source)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_nested_readonly_reference_and_rejections(self):
        self.check('import Proofs.CppReferenceHeaders\nimport Proofs.Generated.UnionFindCandidate\n'
                   +'\n'.join(fixture_checks())+SCALAR_CHECKS+NESTED)

    def test_union_find_calls_and_trace(self):
        self.check('import Proofs.UfReceiverReferences\n'+HEADER+CALLER_HEADER+STAGE_CHECKS
                   +RECEIVER_CHECKS+TRACE_CHECKS+RANK_CHECKS+METADATA+UNION_FIND)

if __name__ == '__main__':
    disable_network()
    unittest.main()
