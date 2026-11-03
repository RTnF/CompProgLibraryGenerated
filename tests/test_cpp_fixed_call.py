"""Actual prepare/finish and UF finite histories preserve other owners' values."""
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
open Proofs.CppFixedCall Proofs.CppPrepareTarget Proofs.CppFixedWrite
 def readBefore : NState := ((rowRead.eval state).getD (state,0)).1
 def writableCaller : NState := {readBefore with frame := {readBefore.frame with
   bindings := readBefore.frame.bindings.set 2 ⟨2,atom,true,.root 1⟩,
   rootWritable := readBefore.frame.rootWritable.set 2 true}}
 def extraCaller : NState := {writableCaller with frame := (writableCaller.frame.addBinding ⟨2,atom,true,.root 1⟩).1}
 def caller : NState := {extraCaller with slots := [.vector 0,.vector 1,.vector 4,.scalar 0,.scalar 1]}
 def receiverBinding : Binding := ⟨2,atom,true,.root 1⟩
 #guard caller.vectorSlot 2 == some 4
 #guard caller.frame.bindings[4]? == some receiverBinding
 theorem callerContexts : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope := by
   have forest : caller.frame.state.forest = state.frame.state.forest := by decide +kernel
   have scope : caller.scope = state.scope := by decide +kernel
   rw [forest,scope]
   exact contexts
 def flatProgram : Proofs.CppNestedCall.NProgram := ⟨[.vector i32 true,.scalar i32 false false],.scalar i32,
   .sequence (.scope (.primitive (.write (.local 0) i32 (.literal i32 0) (.variable i32 1))))
     (.primitive (.ret (.read i32 (.local 0) (.literal i32 0))))⟩
 def args : List Proofs.CppNestedCall.NArgument := [.vectorReference 2,.value rowRead]
 def prepared : NState := (Proofs.CppNestedCall.prepare caller flatProgram.parameters args).getD caller
 theorem preparedTarget : Target prepared 2 := prepare_target caller prepared i32 true [.scalar i32 false false] [.value rowRead] 2 4 receiverBinding
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
 #guard prepared.vectorSlot 0 == some 0
 #guard prepared.frame.bindings.length == 1
 #guard prepared.frame.bindings[0]?.map (fun b => b.owner) == some 2
 def called : NState := match flatProgram.callFuel 16 caller args with
   | .finished (out,_) => out | _ => caller
 theorem otherValues : ∀ owner, owner ≠ 2 → called.frame.state.storage.lookup owner = caller.frame.state.storage.lookup owner :=
   call_values flatProgram 16 caller called args (.scalar (-3)) i32 2 rfl rfl
     (fun init prep => prepare_target caller init i32 true [.scalar i32 false false] [.value rowRead] 2 4 receiverBinding
       (by decide +kernel) (by decide +kernel) prep) callerContexts (by decide +kernel)
 #guard flatProgram.callFuel 16 caller args == .finished (called,.scalar (-3))
 #guard (caller.frame.state.storage.lookup 2).map (fun b => b.items) == some [.integer 77]
 #guard (called.frame.state.storage.lookup 2).map (fun b => b.items) == some [.integer (-3)]
 #guard called.frame.bindings == caller.frame.bindings
 #guard called.slots == caller.slots && called.scope == caller.scope
 #guard called.scalars.memory == caller.scalars.memory
 #guard (List.range 7).all (fun owner => owner == 2 || called.frame.state.storage.lookup owner == caller.frame.state.storage.lookup owner)
 def captured := caller.frame.elementRef 3 i32 1
 #guard captured.bind caller.frame.read == some (-3)
 #guard captured.bind called.frame.read == some (-3)
 example := otherValues 4 (by decide)
 theorem calledEffects : Proofs.CppCallFrame.CallEffects caller called := Proofs.CppCallFrame.call_headers
   flatProgram 16 caller called args (.scalar (-3)) i32 rfl rfl callerContexts (by decide +kernel)
 example (reference : Reference) (different : reference.address.owner ≠ 2) :=
   read_other caller called 2 calledEffects (by decide +kernel) (by decide +kernel) otherValues reference different
 example (s init : NState) (ty : Ty) (wr : Bool) (ps : List Proofs.CppVectorBindings.Parameter)
   (args : List Proofs.CppNestedCall.NArgument) (slot index : Nat) (binding : Binding)
   (selected : s.vectorSlot slot = some index) (found : s.frame.bindings[index]? = some binding)
   (ran : Proofs.CppNestedCall.prepare s (.vector ty wr::ps) (.vectorReference slot::args) = some init) :=
   prepare_target s init ty wr ps args slot index binding selected found ran
'''
UF = '''
 theorem builtSelected : Proofs.UfReceiverValues.Selected built (layoutOf populated) :=
   Proofs.UfReceiverValues.represents_selected built (layoutOf populated) _ _ _ builtRep
 theorem finalValues : ∀ owner, owner ≠ (layoutOf populated).owner →
   final.frame.state.storage.lookup owner = built.frame.state.storage.lookup owner :=
   Proofs.UfReceiverValues.actual_calls (List.replicate mixed.length 128) mixed built (layoutOf populated)
     final [4,0,2,0,2,0,0,1,4,1,0,1] builtSelected builtContexts (by decide +kernel)
 #guard (List.range built.frame.state.storage.objects.length).all (fun owner => owner == (layoutOf populated).owner ||
   final.frame.state.storage.lookup owner == built.frame.state.storage.lookup owner)
 example := finalValues 0 (by decide +kernel)
 theorem finalValid : final.frame.state.wellFormed = true := by decide +kernel
 theorem builtValid : built.frame.state.wellFormed = true := by decide +kernel
 example := Proofs.UfReceiverValues.actual_calls_reads (List.replicate mixed.length 128) mixed built (layoutOf populated)
   final [4,0,2,0,2,0,0,1,4,1,0,1] builtSelected builtValid finalValid builtContexts (by decide +kernel)
 example := Proofs.UfReceiverValues.calls_work_reads mixed built (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) builtStrong mixedAllowed
 example := Proofs.UfReceiverValues.calls_work_values mixed built (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) builtStrong mixedAllowed
 example (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
   (selected : Proofs.UfReceiverValues.Selected s layout)
   (ctx : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
   (ran : call fuel s layout op = .finished (out,ret)) :=
   Proofs.UfReceiverValues.call_values fuel s out layout op ret selected ctx ran
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   Proofs.UfReceiverValues.calls_work_values ops s layout ps count rank strong allowed
'''

class FixedCallTests(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory(prefix='cpp-fixed-call-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text(source)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_prepare_nested_value_actual_call(self):
        self.check('import Proofs.CppPrepareTarget\nimport Proofs.CppFixedCall\nimport Proofs.Generated.UnionFindCandidate\n'
                   +'\n'.join(fixture_checks())+SCALAR_CHECKS+NESTED)

    def test_uf_actual_finite_history_and_work(self):
        self.check('import Proofs.UfReceiverValues\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS
                   +TRACE_CHECKS+RANK_CHECKS+METADATA+UF)

if __name__ == '__main__':
    disable_network()
    unittest.main()
