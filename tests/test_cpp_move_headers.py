"""Move-construction header/allocation identity, grants and resource invariants."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from check_public import check_compiler
from offline import disable_network

CHECKS = r'''

open Proofs.CppMoveHeaders
open Proofs.CppVector Proofs.CppVectorCopyAssign
namespace HeaderMoveExamples
def allow (_ : Int) : Bool := true
def initial : Heap Int := ⟨[some ⟨some 0,1,true,8⟩,some ⟨some 1,0,true,8⟩],
  [some ⟨⟨0,[10,11],4,8,2⟩,fun _ => 7⟩,some ⟨⟨1,[99],1,8,0⟩,fun _ => 0⟩],[],0,0,0⟩
def first := (capture initial allow 0 1 true).getD (initial,0)
def second := (capture first.1 allow 0 0 false).getD (first.1,0)
def moved := (moveConstruct second.1 allow 0 0 false).getD (second.1,0)
#guard (capture initial allow 0 1 true).isSome
#guard first.2 == 0 && second.2 == 1 && moved.2 == 2
#guard moved.1.header 0 == some ⟨none,1,true,8⟩
#guard moved.1.header moved.2 == some ⟨some 0,0,false,8⟩
#guard moved.1.header 1 == initial.header 1
#guard moved.1.grants.map (·.writable) == [true,false]
#guard moved.1.grants == second.1.grants
#guard moved.1.allocations.length == initial.allocations.length
#guard Proofs.CppMoveHeaders.read moved.1 allow first.2 == some 11
#guard Proofs.CppMoveHeaders.read moved.1 allow second.2 == some 10
#guard (capture moved.1 allow 0 0 false).isNone
#guard (capture moved.1 allow moved.2 0 true).isNone
#guard (capture moved.1 allow moved.2 0 false).isSome
#guard (moveConstruct moved.1 allow moved.2 0 true).isNone
#guard (moveConstruct moved.1 allow 999 0 true).isNone
#guard (moved.1.allocation 0).map (fun t => (t.buffer.items,t.buffer.owner,t.buffer.epoch,t.generation 1)) == some ([10,11],0,2,7)
theorem actual : moveConstruct second.1 allow 0 0 false = some (moved.1,2) := by rfl
example (reference : Nat) : Proofs.CppMoveHeaders.read moved.1 allow reference = Proofs.CppMoveHeaders.read second.1 allow reference :=
  move_construct_read second.1 moved.1 allow 0 0 2 false actual reference
-- An empty vector has an object header and no fabricated allocation.
def empty : Heap Int := ⟨[some ⟨none,3,true,8⟩],[],[],0,0,0⟩
def emptyMoved := (moveConstruct empty allow 0 0 false).getD (empty,0)
#guard (moveConstruct empty allow 0 0 false).isSome
#guard emptyMoved.1.allocations.length == 0 && emptyMoved.1.headers.length == 2
#guard emptyMoved.1.header 0 == some ⟨none,3,true,8⟩
#guard emptyMoved.1.header 1 == some ⟨none,0,false,8⟩
-- Empty reserved storage remains an allocation but has no readable element.
def reserved : Heap Int := ⟨[some ⟨some 0,3,true,8⟩],[some ⟨⟨0,[],4,8,2⟩,fun _ => 7⟩],[],0,0,0⟩
#guard (moveConstruct reserved allow 0 0 true).isSome
#guard (capture reserved allow 0 0 false).isNone
#guard (moveConstruct {initial with headers := [some ⟨some 0,1,false,8⟩]} allow 0 0 true).isNone
#guard (moveConstruct {initial with headers := [some ⟨some 42,1,true,8⟩]} allow 0 0 true).isNone
#guard (moveConstruct {initial with headers := [some ⟨some 0,1,true,9⟩]} allow 0 0 true).isNone
#guard (moveConstruct ({initial with allocations := [some ⟨⟨9,[10,11],4,8,2⟩,fun _ => 7⟩]} : Heap Int) allow 0 0 true).isNone
#guard (moveConstruct ({initial with allocations := [some ⟨⟨0,[10,11],1,8,2⟩,fun _ => 7⟩]} : Heap Int) allow 0 0 true).isNone
theorem initialUnique : Unique initial := by
  intro i j hi hj owner iFound jFound iOwns jOwns
  have iBound := source_inside initial i hi iFound
  have jBound := source_inside initial j hj jFound
  change i < 2 at iBound
  change j < 2 at jBound
  have iCases : i = 0 ∨ i = 1 := by omega
  have jCases : j = 0 ∨ j = 1 := by omega
  rcases iCases with rfl | rfl <;> rcases jCases with rfl | rfl <;> simp_all [Heap.header,initial]
  all_goals
    subst hi
    subst hj
    simp_all
    omega
-- Capture changes only the ghost grant ledger; owning-header uniqueness remains.
theorem secondUnique : Unique second.1 := initialUnique
example : Unique moved.1 := move_construct_unique second.1 moved.1 allow 0 0 2 false secondUnique actual

#guard initial.liveSpace == 7 && first.1.liveSpace == 7 && second.1.liveSpace == 7
#guard moved.1.liveSpace == 8 && moved.1.work == 1 && moved.1.peak == 8
#guard emptyMoved.1.liveSpace == 2 && emptyMoved.1.allocations.length == 0
#guard (moveConstruct reserved allow 0 0 true).map (fun p => (p.1.liveSpace,p.1.work,p.1.peak)) == some (6,1,6)
example := move_construct_resources second.1 moved.1 allow 0 0 2 false actual
-- Historical peaks and a nonzero external baseline survive the transfer.
def high : Heap Int := {second.1 with baseSpace := 2,peak := 400,work := 100}
#guard (moveConstruct high allow 0 0 false).map (fun p => (p.1.work,p.1.liveSpace,p.1.peak,p.1.baseSpace)) == some (101,8,400,2)
def baseline : Heap Int := {second.1 with baseSpace := 3}
#guard (moveConstruct baseline allow 0 0 true).map (fun p => p.1.peak) == some 5
#guard ({second.1 with grants := (List.replicate 100 second.1.grants).flatten} : Heap Int).liveSpace == second.1.liveSpace

theorem initialCovered : OwnsAll initial := by
  intro owner tracked found
  have bound : owner < initial.allocations.length := by
    unfold Heap.allocation at found
    cases raw : initial.allocations[owner]? with
    | none => simp [raw] at found
    | some value => exact (List.getElem?_eq_some_iff.mp raw).1
  change owner < 2 at bound
  have choices : owner = 0 ∨ owner = 1 := by omega
  rcases choices with rfl | rfl
  · exact ⟨0,⟨some 0,1,true,8⟩,rfl,rfl⟩
  · exact ⟨1,⟨some 1,0,true,8⟩,rfl,rfl⟩
theorem secondCovered : OwnsAll second.1 := initialCovered
example : OwnsAll moved.1 := move_construct_ownsAll second.1 moved.1 allow 0 0 2 false secondCovered actual

#guard ((Proofs.CppMoveHeaders.write moved.1 allow first.2 25).bind (fun out => Proofs.CppMoveHeaders.read out allow first.2)) == some 25
#guard ((Proofs.CppMoveHeaders.write moved.1 allow first.2 25).bind (fun out => Proofs.CppMoveHeaders.read out allow second.2)) == some 10
#guard (Proofs.CppMoveHeaders.write moved.1 allow second.2 25).isNone
#guard (Proofs.CppMoveHeaders.write moved.1 allow 999 25).isNone
#guard (Proofs.CppMoveHeaders.write moved.1 allow first.2 25).map (fun out => out.header moved.2) == some (some ⟨some 0,0,false,8⟩)
def staleGeneration : Heap Int := {moved.1 with grants := [⟨⟨⟨0,2,1⟩,6⟩,true⟩]}
def staleEpoch : Heap Int := {moved.1 with grants := [⟨⟨⟨0,1,1⟩,7⟩,true⟩]}
#guard (Proofs.CppMoveHeaders.write staleGeneration allow 0 25).isNone
#guard (Proofs.CppMoveHeaders.write staleEpoch allow 0 25).isNone
example := move_construct_write second.1 moved.1 allow 0 0 2 false actual first.2 25
end HeaderMoveExamples
'''

NATIVE = r'''
#include <vector>
#include <cassert>
#include <type_traits>
#include <utility>
long long* escaped;
std::vector<long long> returning(){
  std::vector<long long> source{7,8};escaped=&source[1];
  return std::move(source);
}
int main(){
  std::vector<long long> source{10,11};source.reserve(4);
  long long* storage=source.data();auto capacity=source.capacity();
  long long& writable=source[1];const long long& readonly=source[0];auto& alias=source;
  const std::vector<long long> target(std::move(source));
  static_assert(std::is_same<decltype(target[0]),const long long&>::value);
  assert(&alias==&source && alias.empty() && source.capacity()==0);
  assert(target.data()==storage && target.capacity()==capacity && readonly==10 && writable==11);
  writable=25;assert(target[1]==25 && readonly==10);
  source.push_back(3);assert(source[0]==3 && target[1]==25);
  std::vector<long long> empty;
  const std::vector<long long> movedEmpty(std::move(empty));
  assert(empty.empty() && movedEmpty.empty() && movedEmpty.capacity()==0);
  std::vector<long long> reserved;reserved.reserve(4);
  auto saved=reserved.data();auto reservedCapacity=reserved.capacity();
  const std::vector<long long> movedReserved(std::move(reserved));
  assert(reserved.empty() && reserved.capacity()==0 && movedReserved.empty());
  assert(movedReserved.data()==saved && movedReserved.capacity()==reservedCapacity);
  auto out=returning();assert(out.size()==2 && out[1]==8 && *escaped==8);
  *escaped=19;assert(out[1]==19);
}
'''

class MoveHeaderTests(unittest.TestCase):
    def test_model_identity_permissions_ownership_and_resources(self):
        with tempfile.TemporaryDirectory(prefix='move-headers-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveHeaders\n'+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_native_const_destination_reference_and_scope(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='move-headers-native-') as directory:
            source=Path(directory)/'check.cpp';binary=Path(directory)/'check'
            source.write_text(NATIVE)
            subprocess.run(['g++','-std=c++17','-O1','-fno-elide-constructors',
                '-fsanitize=address,undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

if __name__=='__main__':
    disable_network()
    unittest.main()
