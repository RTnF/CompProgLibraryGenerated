"""Move assignment retires destination storage and preserves source references."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from check_public import check_compiler
from offline import disable_network

CHECKS = r'''

namespace AssignExamples
open Proofs.CppMoveHeaders Proofs.CppMoveAssign HeaderMoveExamples
-- Grant 2 points into the old destination allocation; grants 0/1 point to source.
def third := (capture second.1 allow 1 0 true).getD (second.1,0)
def out := (moveAssign third.1 allow 1 0).getD third.1
#guard third.2 == 2
#guard (moveAssign third.1 allow 1 0).isSome
#guard out.header 0 == some ⟨none,1,true,8⟩
#guard out.header 1 == some ⟨some 0,0,true,8⟩
#guard out.grants == third.1.grants
#guard Proofs.CppMoveHeaders.read out allow first.2 == some 11
#guard Proofs.CppMoveHeaders.read out allow second.2 == some 10
#guard (Proofs.CppMoveHeaders.read out allow third.2).isNone
#guard (Proofs.CppMoveHeaders.write out allow third.2 5).isNone
#guard ((Proofs.CppMoveHeaders.write out allow first.2 25).bind (fun s => Proofs.CppMoveHeaders.read s allow first.2)) == some 25
#guard (capture out allow 0 0 false).isNone
#guard (capture out allow 1 0 true).isSome
#guard out.allocations.length == third.1.allocations.length
#guard (out.allocation 1).isNone
#guard (out.allocation 0).map (fun t => (t.buffer.items,t.buffer.capacity,t.buffer.epoch,t.generation 1)) == some ([10,11],4,2,7)
theorem actual : moveAssign third.1 allow 1 0 = some out := by rfl
example := move_assign_runs third.1 allow 1 0 ⟨some 1,0,true,8⟩ ⟨some 0,1,true,8⟩
  (by rfl) (by rfl) rfl rfl (by decide +kernel) (by decide +kernel) rfl secondUnique
example : Proofs.CppMoveHeaders.read out allow third.2 = none :=
  assigned_target_retired third.1 1 0 1 ⟨some 1,0,true,8⟩ ⟨some 0,1,true,8⟩ allow third.2
    ⟨⟨⟨1,0,0⟩,0⟩,true⟩ rfl (by rfl) rfl
example : Proofs.CppMoveHeaders.read out allow first.2 = some 11 :=
  assigned_read_other third.1 1 0 ⟨some 1,0,true,8⟩ ⟨some 0,1,true,8⟩ allow first.2
    ⟨⟨⟨0,2,1⟩,7⟩,true⟩ (by rfl) (by intro owner found; cases Option.some.inj found; decide)
example : Proofs.CppMoveHeaders.read out allow first.2 = some 11 :=
  assigned_source_read third.1 1 0 ⟨some 1,0,true,8⟩ ⟨some 0,1,true,8⟩ allow first.2
    ⟨⟨⟨0,2,1⟩,7⟩,true⟩ secondUnique (by rfl) (by rfl) (by decide) (by rfl) rfl
-- Moving the allocation back must not revive references to retired allocation1.
def back := (moveAssign out allow 0 1).getD out
theorem backActual : moveAssign out allow 0 1 = some back := by rfl
#guard back.header 0 == some ⟨some 0,1,true,8⟩
#guard back.header 1 == some ⟨none,0,true,8⟩
#guard (Proofs.CppMoveHeaders.read back allow third.2).isNone
#guard Proofs.CppMoveHeaders.read back allow first.2 == some 11
def rebuilt := (moveConstruct back allow 0 0 true).getD (back,0)
theorem rebuiltActual : moveConstruct back allow 0 0 true = some (rebuilt.1,2) := by rfl
example : Moves allow out rebuilt.1 :=
  .assign out back rebuilt.1 0 1 backActual (.construct back rebuilt.1 rebuilt.1 0 0 2 true rebuiltActual (.refl _))
example : Proofs.CppMoveHeaders.read rebuilt.1 allow third.2 = none :=
  Moves.no_resurrection (.assign out back rebuilt.1 0 1 backActual (.construct back rebuilt.1 rebuilt.1 0 0 2 true rebuiltActual (.refl _))) third.2 (by rfl)
-- Fixed self-move retires the allocation and clears the same vector object.
def self := (moveAssign out allow 1 1).getD out
#guard (moveAssign out allow 1 1).isSome
#guard self.header 1 == some ⟨none,0,true,8⟩
#guard (Proofs.CppMoveHeaders.read self allow first.2).isNone
#guard (Proofs.CppMoveHeaders.read self allow third.2).isNone
#guard (self.allocation 0).isNone && (self.allocation 1).isNone
#guard self.grants == out.grants
#guard self.liveSpace == 2 && out.liveSpace == 6
#guard out.work == 2 && self.work == 5
#guard out.peak == 8 && self.peak == 8
#guard (moveAssign {third.1 with headers := [some ⟨some 0,1,true,8⟩,some ⟨some 1,0,false,8⟩]} allow 1 0).isNone
#guard (moveAssign {third.1 with headers := [some ⟨some 0,1,false,8⟩,some ⟨some 1,0,true,8⟩]} allow 1 0).isNone
#guard (moveAssign {third.1 with headers := [some ⟨some 0,1,true,8⟩,some ⟨some 1,0,true,9⟩]} allow 1 0).isNone
#guard (moveAssign {third.1 with headers := [some ⟨some 0,1,true,8⟩,some ⟨some 0,0,true,8⟩]} allow 1 0).isNone
#guard (moveAssign third.1 allow 99 0).isNone

example : Unique out := move_assign_unique third.1 out allow 1 0 secondUnique actual
example : OwnsAll out := move_assign_ownsAll third.1 out allow 1 0 secondCovered actual
example := assigned_target third.1 1 0 ⟨some 1,0,true,8⟩ ⟨some 0,1,true,8⟩ (by rfl)
example := assigned_source third.1 1 0 ⟨some 1,0,true,8⟩ ⟨some 0,1,true,8⟩ (by rfl) (by rfl)
example := move_assign_resources third.1 out allow 1 0 actual
theorem selfActual : moveAssign out allow 1 1 = some self := by rfl
example : Unique self := move_assign_unique out self allow 1 1 (move_assign_unique third.1 out allow 1 0 secondUnique actual) selfActual
example : OwnsAll self := move_assign_ownsAll out self allow 1 1 (move_assign_ownsAll third.1 out allow 1 0 secondCovered actual) selfActual
example := move_assign_resources out self allow 1 1 selfActual
#guard out.liveSpace+oldCapacity third.1 ⟨some 1,0,true,8⟩ == third.1.liveSpace
#guard self.liveSpace+oldCapacity out ⟨some 0,0,true,8⟩ == out.liveSpace
def high : Heap Int := {third.1 with baseSpace := 2,peak := 400,work := 100}
#guard (moveAssign high allow 1 0).map (fun s => (s.work,s.liveSpace,s.peak,s.baseSpace)) == some (102,6,400,2)
def baseline : Heap Int := {third.1 with baseSpace := 3}
#guard (moveAssign baseline allow 1 0).map (fun s => s.peak) == some 5
-- Another object owns the old source allocation after construction. Moving the
-- now-empty source object must not touch that allocation or its old references.
def outside := (moveAssign moved.1 allow 1 0).getD moved.1
#guard outside.header 2 == moved.1.header 2
#guard Proofs.CppMoveHeaders.read outside allow first.2 == some 11
#guard outside.liveSpace+1 == moved.1.liveSpace
#guard outside.peak == 9
example := assigned_other_header moved.1 1 0 2 ⟨some 1,0,true,8⟩ ⟨none,1,true,8⟩ (by decide) (by decide)
def empty2 := (moveConstruct empty allow 0 0 true).getD (empty,0)
#guard (moveAssign empty2.1 allow 1 0).isSome
#guard (moveAssign empty2.1 allow 1 0).map (fun s => (s.liveSpace,s.peak,s.allocations.length)) == some (2,3,0)
-- Reserved empty destination storage is released even though no elements are retired.
def reservedTarget : Heap Int := {third.1 with allocations := third.1.allocations.set 1 (some ⟨⟨1,[],8,8,0⟩,fun _ => 0⟩)}
#guard (moveAssign reservedTarget allow 1 0).map (fun s => (s.work,s.liveSpace,s.peak)) == some (1,6,15)
end AssignExamples
'''

NATIVE=r'''
#include <vector>
#include <cassert>
#include <utility>
int main(){
  for(int n : {0,1,2,17}){
    std::vector<long long> source(n),target(4,99);
    for(int i=0;i<n;++i)source[i]=10+i;
    auto& sourceObject=source;auto& targetObject=target;
    long long* saved=n?&source[0]:nullptr;auto storage=source.data();auto cap=source.capacity();
    auto* returned=&(target=std::move(source));
    assert(returned==&target && &targetObject==&target && &sourceObject==&source);
    assert(source.empty() && source.capacity()==0 && target.size()==static_cast<unsigned>(n));
    assert(target.data()==storage && target.capacity()==cap);
    if(n){assert(*saved==10);*saved=25;assert(target[0]==25);}
    source=std::move(target);
    assert(target.empty() && source.size()==static_cast<unsigned>(n));
    if(n)assert(*saved==25 && source.data()==saved);
    returned=&(source=std::move(source));
    assert(returned==&source && source.empty() && source.capacity()==0);
    // No read through saved: its allocation has ended during self move.
    std::vector<long long> fresh{77,78};source=std::move(fresh);
    assert(source.size()==2 && source[1]==78 && fresh.empty());
  }
  std::vector<int> emptySource,reservedTarget;reservedTarget.reserve(8);
  reservedTarget=std::move(emptySource);
  assert(reservedTarget.empty() && reservedTarget.capacity()==0 && emptySource.empty());
  std::vector<int> backing{3,4},victim{99};int* element=&backing[1];
  const std::vector<int> independent(std::move(backing));
  victim=std::move(backing);
  assert(victim.empty() && independent[1]==4 && *element==4);
  *element=9;assert(independent[1]==9);
}
'''

class MoveAssignmentTests(unittest.TestCase):
    def test_model_references_ownership_self_move_and_resources(self):
        with tempfile.TemporaryDirectory(prefix='move-assignment-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveAssign\n'+HEADER_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_native_reference_transfer_self_move_and_empty(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='move-assignment-native-') as directory:
            source=Path(directory)/'check.cpp';binary=Path(directory)/'check'
            source.write_text(NATIVE)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=address,undefined',
                '-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

if __name__=='__main__':
    disable_network()
    unittest.main()
