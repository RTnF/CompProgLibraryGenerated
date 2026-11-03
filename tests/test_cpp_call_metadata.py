"""Control-flow effects and generated UF call/finite-trace metadata."""
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
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
CONTROL = '''
open Proofs.CppNoResizeRun
 def flowBody : Command := .sequence (.primitive (.declare i32 true (.literal i32 0)))
   (.sequence
     (.scope (.whileLoop (.binary ⟨1,false,true⟩ .lt (.variable i32 5) (.literal i32 3))
       (.sequence (.primitive (.write (.row (.local 0) atom idx) i32 pos (.literal i32 11)))
         (.primitive (.assign 5 i32 (.binary i32 .add (.variable i32 5) (.literal i32 1)))))))
     (.branch (.literal i32 0) (.primitive (.ret (.literal i32 99))) (.primitive (.ret rowRead))))
 def result : NStep := match Proofs.CppNestedProgram.runFuel 128 flowBody state with
   | .finished out => out
   | _ => ⟨state,none,false⟩
 example := run_headers 128 flowBody state result (by decide +kernel) contexts (by decide +kernel)
 #guard result.returned == some (.scalar 11)
 #guard result.state.scope == state.scope
 #guard result.state.scalars.memory.length == state.scalars.memory.length+1
 #guard result.state.frame.state.liveSpace == state.frame.state.liveSpace
 def early : Command := .sequence
   (.scope (.branch (.literal i32 1) (.primitive (.ret rowRead)) (.primitive (.check (.literal i32 0)))))
   (.primitive (.check (.literal i32 0)))
 def earlyResult : NStep := match Proofs.CppNestedProgram.runFuel 32 early state with
   | .finished out => out
   | _ => ⟨state,none,false⟩
 example := run_headers 32 early state earlyResult (by decide +kernel) contexts (by decide +kernel)
 #guard earlyResult.returned == some (.scalar (-3))
 def broken : Command := .whileLoop (.literal i32 1) (.scope .breakLoop)
 def brokenResult : NStep := match Proofs.CppNestedProgram.runFuel 16 broken state with
   | .finished out => out
   | _ => ⟨state,none,true⟩
 example := run_headers 16 broken state brokenResult rfl contexts (by decide +kernel)
 #guard !brokenResult.breaking && brokenResult.returned.isNone
 example := run_headers 8 (.whileLoop (.literal i32 0) (.primitive (.check (.literal i32 0)))) state
   ⟨(state.charge 1 1).charge 1 0,none,false⟩ rfl contexts (by decide +kernel)
 example (fuel : Nat) (command : Command) (s : NState) (out : NStep)
   (allowed : Proofs.CppNoResizeScope.Allowed command = true)
   (ctx : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
   (ran : Proofs.CppNestedProgram.runFuel fuel command s = .finished out) := run_headers fuel command s out allowed ctx ran
 def nestedProgram : Proofs.CppNestedCall.NProgram := ⟨[.nested i32 false,.scalar i32 false true],.scalar i32,
   .primitive (.ret (.variable i32 1))⟩
 def nestedArgs : List Proofs.CppNestedCall.NArgument := [.vectorReference 1,.value rowRead]
 def nestedOut : NState := match nestedProgram.callFuel 8 state nestedArgs with
   | .finished (s,_) => s
   | _ => state
 example := Proofs.CppCallFrame.call_headers nestedProgram 8 state nestedOut nestedArgs (.scalar (-3)) i32
   rfl rfl contexts (by decide +kernel)
 #guard nestedOut.frame.state == state.frame.state
 #guard nestedOut.frame.bindings == state.frame.bindings
 #guard nestedOut.scalars.memory == state.scalars.memory
'''
METADATA = '''
open Proofs.UfReceiverMetadata Proofs.CppCallFrame Proofs.CppNestedEval
 theorem builtContexts : ∀ owner scope, built.frame.state.forest.context owner = some scope → scope ≤ built.scope := by
   obtain ⟨buf,cb,nb,inv⟩ := builtRep
   exact inv.ok.strict
 def final : NState := match executed with | .finished (out,_) => out | _ => empty
 theorem finalEffects : CallEffects built final := actual_calls (List.replicate mixed.length 128) mixed built
   (layoutOf populated) final [4,0,2,0,2,0,0,1,4,1,0,1] builtContexts (by decide +kernel)
 example := calls_work_effects mixed built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong mixedAllowed
 example := constructed_work_effects populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 4) 4 (by decide) rfl rfl rfl mixed mixedAllowed
 example := default_work_effects populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 example := finalEffects.headers.live
 example (reference : Reference) := finalEffects.grant reference
 #guard final.frame.state.forest == built.frame.state.forest
 #guard final.frame.rootWritable == built.frame.rootWritable
 #guard final.frame.bindings == built.frame.bindings
 #guard final.slots == built.slots && final.scope == built.scope
 #guard final.scalars.memory.length == built.scalars.memory.length
 #guard final.scalars.bindings == built.scalars.bindings
 #guard liveS final == liveS built
 #guard (List.range built.frame.state.storage.objects.length).all (fun owner =>
   (final.frame.state.storage.lookup owner).map Proofs.CppBufferHeaders.signature ==
     (built.frame.state.storage.lookup owner).map Proofs.CppBufferHeaders.signature)
 #guard saved.bind final.frame.read == some (-1)
 def freshRef := built.frame.elementRef populated.frame.bindings.length i32 3
 #guard freshRef.bind built.frame.read == some (-1)
 #guard freshRef.bind final.frame.read == some 0
 #guard freshRef.bind final.frame.grant == freshRef.bind built.frame.grant
 example (fuels : List Nat) (ops : List Operation) (s out : NState) (layout : Layout) (answers : List Int)
   (ctx : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
   (ran : runCalls fuels ops s layout = .finished (out,answers)) := actual_calls fuels ops s layout out answers ctx ran
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (allowed : ∀ op ∈ ops, op.allowed ps.length) := calls_work_effects ops s layout ps count rank strong allowed
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (strict : ∀ owner scope, c.frame.state.forest.context owner = some scope → scope ≤ c.scope)
   (base : c.scalars.baseMemory ≤ c.scalars.memory.length) (en : NExpr) (n : Nat) (endpoint : n = 2147483647)
   (scalar : en.scalarOnly = true) (ty : en.resultType = i32)
   (value : en.denote (Proofs.CppNestedEval.envOf c) = some (n : Int))
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed n) :=
   constructed_work_effects c h valid models lengths strict base en n (by omega) scalar ty value ops allowed
'''

class CallMetadataTests(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory(prefix='cpp-call-metadata-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text(source)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_control_flow(self):
        self.check('import Proofs.CppCallFrame\nimport Proofs.Generated.UnionFindCandidate\n'
                   +'\n'.join(fixture_checks())+SCALAR_CHECKS+CONTROL)

    def test_generated_calls_and_finite_trace(self):
        self.check('import Proofs.UfReceiverMetadata\n'+HEADER+CALLER_HEADER+STAGE_CHECKS
                   +RECEIVER_CHECKS+TRACE_CHECKS+RANK_CHECKS+METADATA)

if __name__ == '__main__':
    disable_network()
    unittest.main()
