"""Copy-before-history component bounds retain historical peaks and resident baselines."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE
from test_union_find_constructed_receiver import CHECKS as RECEIVER
from test_union_find_receiver_trace import CHECKS as TRACE
from test_union_find_rank_doubling import CHECKS as RANK
from test_union_find_copy_receiver import CHECKS as COPY
from test_union_find_copy_preserve import CHECKS as PRESERVE
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent

CHECKS = r'''
open Proofs.UfCopyPeak Proofs.CppNestedEval Proofs.UfConstructedPeak
 example := actual_history_peak built duplicate afterCalls (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) (List.replicate mixed.length 128) mixed [4,0,2,0,2,0,0,1,4,1,0,1]
   builtStrong mixedAllowed (by decide +kernel) (by decide +kernel)
 example := copy_history built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) mixed builtStrong mixedAllowed
 example := copy_history built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) [] builtStrong (by simp)
 def high : NState := {built with
   peak := 100000000
   scalars := {built.scalars with peak := 7,baseMemory := 2}
   frame := {built.frame with state := {built.frame.state with storage := {built.frame.state.storage with peak := 9,baseSpace := 3}}}}
 theorem highStrong : Strong high (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) := by
   obtain ⟨buf,cb,nb,inv⟩ := builtStrong.1
   have ok : Proofs.UfFindCall.VOKWF high (layoutOf populated).vectorSlot (layoutOf populated).vectorBinding
       (layoutOf populated).owner (layoutOf populated).scope buf :=
     ⟨inv.ok.valid,inv.ok.slot,inv.ok.binding,inv.ok.vtag,inv.ok.vfound,inv.ok.lengths,inv.ok.flag,inv.ok.strict,by decide +kernel⟩
   exact ⟨⟨buf,cb,nb,ok,inv.items,inv.bufferValid,inv.limit,inv.owner,inv.math,inv.countCell,
     inv.writable,inv.nCell,inv.different⟩,builtStrong.2⟩
 def highCopy := (copyReceiver high (layoutOf populated)).getD (empty,layoutOf empty)
 def highAfter : NState := match runCalls (List.replicate mixed.length 128) mixed highCopy.1 highCopy.2 with
   | .finished (out,_) => out | _ => empty
 #guard highCopy.2 == layoutOf high
 example := actual_history_peak high highCopy.1 highAfter (layoutOf populated) (List.replicate 4 (-1)) 4
   (fun _ => 0) (List.replicate mixed.length 128) mixed [4,0,2,0,2,0,0,1,4,1,0,1]
   highStrong mixedAllowed (by decide +kernel) (by decide +kernel)
 #guard highAfter.peak == 100000000
 #guard highAfter.scalars.peak < 1000
 #guard highAfter.frame.state.storage.peak < 1000
 #guard highAfter.scalars.peak ≤ scalarEnvelope high 0
 #guard highAfter.frame.state.storage.peak ≤ storageEnvelope high 4
 #guard liveS highAfter == liveS high+4
 #guard highAfter.frame.state.liveSpace == high.frame.state.liveSpace+5
 #guard highAfter.scalars.baseMemory == 2
 #guard highAfter.frame.state.storage.baseSpace == 3
 example := scalar_resident high highAfter 0 (by decide +kernel) (by decide +kernel)
 example := storage_resident high highAfter 4 (by decide +kernel) (by decide +kernel)
 def twice := mixed++mixed
 theorem twiceAllowed : ∀ op ∈ twice, op.allowed 4 := by
   intro op member
   rcases List.mem_append.mp member with h|h <;> exact mixedAllowed op h
 def twiceAfter : NState := match runCalls (List.replicate twice.length 128) twice highCopy.1 highCopy.2 with
   | .finished (out,_) => out | _ => empty
 #guard twiceAfter.peak == highAfter.peak
 #guard twiceAfter.scalars.peak == highAfter.scalars.peak
 #guard twiceAfter.frame.state.storage.peak == highAfter.frame.state.storage.peak
 example := copy_history high (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) twice highStrong twiceAllowed
 example (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat) (ops : List Operation)
   (strong : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :=
   copy_history s layout ps count rank ops strong allowed
 example (s : NState) (buf : Proofs.CppVector.Buffer Value) (count n : Int)
   (base : s.scalars.baseMemory ≤ s.scalars.memory.length) := initial_components s buf count n base
 example : ∃ s, ∃ receiver fuels out answers,
   copyReceiver s (layoutOf populated) = some (receiver,layoutOf s) ∧
   runCalls fuels defaults receiver (layoutOf s) = .finished (out,answers) ∧
   out.peak ≤ envelope s 0 0 := by
   obtain ⟨s,_,strong⟩ := Proofs.UfBalancedReceiver.construct_default populated noHeap
     (by decide +kernel) (noModels populated) (by decide +kernel) populatedStrict (by decide +kernel)
   obtain ⟨r,fuels,out,vec,count,rank,answers,copied,ran,old,new,len,fl,al,work,liveS,liveV,effects,cells,reads,scalar,storage,peak⟩ :=
     copy_history s (layoutOf populated) [] 0 (fun _ => 0) defaults strong defaultsAllowed
   exact ⟨s,r,fuels,out,answers,copied,ran,peak⟩
'''

class CopyPeakTests(unittest.TestCase):
    def test_components_full_history_and_resident_bounds(self):
        source='import Proofs.UfCopyPeak\n'+HEADER+CALLER_HEADER+STAGE+RECEIVER+TRACE+RANK+COPY+PRESERVE+CHECKS
        with tempfile.TemporaryDirectory(prefix='uf-copy-peak-') as directory:
            proof=Path(directory)/'checks.lean';proof.write_text(source)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__ == '__main__':
    disable_network()
    unittest.main()
