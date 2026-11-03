"""Constructor-to-history resource envelopes and preserved constructor API."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_constructed_receiver import CHECKS as RECEIVER_CHECKS
from test_union_find_receiver_trace import CHECKS as TRACE_CHECKS
from test_union_find_rank_doubling import CHECKS as RANK_CHECKS
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
COMPONENTS = '''
open Proofs.UfConstructorSpace Proofs.CppNestedEval
 def ctorComponents (s : NState) (n : Nat) : Bool := match UnionFind_construct1.constructFuel 8 s
   [.value (.literal i32 n)] (Proofs.UfConstructionExport.vectorField true) (.integer i32)
   (Proofs.UfConstructionExport.fields true) with
   | .finished (out,_) => out.scalars.peak <= max s.scalars.peak (liveS s+s.frame.bindings.length+1+12) &&
     out.frame.state.storage.peak <= Proofs.UfConstructedPeak.storageEnvelope s n &&
     out.frame.state.storage.baseSpace == s.frame.state.storage.baseSpace &&
     out.frame.bindings.length == s.frame.bindings.length+1
   | _ => false
 #guard ctorComponents populated 0
 #guard ctorComponents populated 1
 #guard ctorComponents populated 17
 example := construct_sized_components populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 17) 17 (by decide) rfl rfl (by decide +kernel)
 example := construct_default_components populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel)
 def aliases : NState := {populated with
   frame := {populated.frame with bindings := populated.frame.bindings++[⟨0,.integer i32,false,.root 0⟩]}
   slots := populated.slots++[.vector populated.frame.bindings.length]}
 #guard ctorComponents aliases 17
 def based : NState := {populated with
   scalars := {populated.scalars with baseMemory := 2}
   frame := {populated.frame with state := {populated.frame.state with
     storage := {populated.frame.state.storage with baseSpace := 30}}}}
 #guard ctorComponents based 17
 def high : NState := {populated with peak := 100000000,scalars := {populated.scalars with peak := 700}}
 #guard ctorComponents high 17
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (strict : ∀ owner scope, c.frame.state.forest.context owner = some scope → scope ≤ c.scope)
   (base : c.scalars.baseMemory ≤ c.scalars.memory.length) (e : NExpr) (n : Nat) (endpoint : n = 2147483647)
   (scalar : e.scalarOnly = true) (ty : e.resultType = i32)
   (value : e.denote (envOf c) = some (n : Int)) := construct_sized_components c h valid models lengths strict base e n (by omega) scalar ty value
'''
TRACE = '''
open Proofs.CppNestedEval
 def final : NState := match executed with | .finished (out,_) => out | _ => empty
 theorem completeBounds : final.scalars.peak ≤ Proofs.UfConstructedPeak.scalarEnvelope populated 1 ∧
   final.frame.state.storage.peak ≤ Proofs.UfConstructedPeak.storageEnvelope populated 4 ∧
   final.peak ≤ Proofs.UfConstructedPeak.envelope populated 4 1 := by
   obtain ⟨receiver,fuels,out,vec,count,rank,answers,ctor,ran,strong,length,fl,al,work,scalarLive,vectorLive,metadata,scalarPeak,storagePeak,outerPeak⟩ :=
     Proofs.UfConstructedPeak.sized populated noHeap (by decide +kernel) (noModels populated)
       (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 4) 4 (by decide) rfl rfl (by decide +kernel) mixed mixedAllowed
   have ctorActual : UnionFind_construct1.constructFuel 8 populated [.value (.literal i32 4)]
     (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
       .finished (built,Proofs.CppConstructorFinish.reference populated 2) := by decide +kernel
   have receiverEq := congrArg Prod.fst (Proofs.CppLoop.Outcome.finished.inj (ctor.symm.trans ctorActual))
   change receiver = built at receiverEq
   subst receiver
   have same := Proofs.UfUniformScalarPeak.run_calls_unique mixed fuels (List.replicate mixed.length 128) built (layoutOf populated)
     (out,answers) (final,[4,0,2,0,2,0,0,1,4,1,0,1]) ran (by decide +kernel)
   have outEq := congrArg Prod.fst same
   change out = final at outEq
   subst out
   exact ⟨scalarPeak,storagePeak,outerPeak⟩
 example := Proofs.UfConstructedPeak.scalar_resident populated final 1 (by decide +kernel) completeBounds.1
 example := Proofs.UfConstructedPeak.storage_resident populated final 4 (by decide +kernel) completeBounds.2.1
 #guard liveS final == liveS populated+4
 #guard final.frame.state.liveSpace == populated.frame.state.liveSpace+5
 #guard final.scalars.peak <= Proofs.UfConstructedPeak.scalarEnvelope populated 1
 #guard final.frame.state.storage.peak <= Proofs.UfConstructedPeak.storageEnvelope populated 4
 #guard final.peak <= Proofs.UfConstructedPeak.envelope populated 4 1
 example := Proofs.UfConstructedPeak.default populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) defaults defaultsAllowed
 example := Proofs.UfConstructedPeak.sized populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.literal i32 0) 0 (by decide) rfl rfl (by decide +kernel) defaults defaultsAllowed
 example := Proofs.UfConstructedPeak.sized populated noHeap (by decide +kernel) (noModels populated)
   (by decide +kernel) populatedStrict (by decide +kernel) (.binary i32 .add (.literal i32 2) (.literal i32 2)) 4
   (by decide) rfl rfl (by decide +kernel) [] (by simp)
 example (c : NState) (h : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state h) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (strict : ∀ owner scope, c.frame.state.forest.context owner = some scope → scope ≤ c.scope)
   (base : c.scalars.baseMemory ≤ c.scalars.memory.length) (e : NExpr) (n : Nat) (endpoint : n = 2147483647)
   (scalar : e.scalarOnly = true) (ty : e.resultType = i32) (value : e.denote (envOf c) = some (n : Int))
   (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed n) :=
   Proofs.UfConstructedPeak.sized c h valid models lengths strict base e n (by omega) scalar ty value ops allowed
'''

class ConstructedPeakTests(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory(prefix='uf-constructed-peak-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text(source)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_constructor_components_and_abstract_endpoint(self):
        self.check('import Proofs.UfConstructedPeak\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS+COMPONENTS)

    def test_sized_default_to_finite_history_full_peak(self):
        self.check('import Proofs.UfConstructedPeak\n'+HEADER+CALLER_HEADER+STAGE_CHECKS+RECEIVER_CHECKS+TRACE_CHECKS+RANK_CHECKS+TRACE)

if __name__ == '__main__':
    disable_network()
    unittest.main()
