"""Owned return transfer, cleanup, invariant preservation and resource bounds."""
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
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from test_cpp_move_frame import CHECKS as FRAME_CHECKS
from test_cpp_move_write import CHECKS as WRITE_CHECKS
from test_cpp_move_context import CHECKS as CONTEXT_CHECKS
from test_cpp_move_destroy import CHECKS as DESTROY_CHECKS
from offline import disable_network
SOURCE=ROOT/'experiments/verification/data_structure/union_find.hpp'

CHECKS = r'''

namespace ReturnExamples
open Proofs.CppMoveReturn Proofs.CppMoveContext Proofs.CppMoveViews
open HeaderMoveExamples ViewExamples FrameExamples ContextExamples DestroyExamples

def returned := (returnOwned callerContext calleeOwned ty localVector.2 false).getD (callerContext,0)
#guard (returnOwned callerContext calleeOwned ty localVector.2 false).isSome
#guard returned.1.scope == callerContext.scope
#guard returned.2 == calleeOwned.objects.views.length
#guard returned.1.objects.heap.header 2 == none
#guard returned.1.objects.heap.header 3 == some ⟨some 0,2,false,8⟩
#guard Proofs.CppMoveHeaders.read returned.1.objects.heap ty.valid 0 == some 11
#guard (Proofs.CppMoveViews.resolve returned.1.objects returned.2).isSome
#guard (Proofs.CppMoveViews.capture returned.1.objects ty.valid returned.2 0 true).isNone
#guard ((Proofs.CppMoveHeaders.write returned.1.objects.heap ty.valid 0 42).bind
  (fun s => Proofs.CppMoveHeaders.read s ty.valid 0)) == some 42
#guard (project returned.1 ty).scalarCell 1 ty == some (⟨0,true⟩,⟨ty,9⟩)
#guard (returnOwned callerContext returned.1 ty returned.2 true).isNone

example := returnOwned_ready callerContext calleeOwned ty localVector.2 false
  ⟨2,true⟩ ⟨some 0,3,true,8⟩ (by decide +kernel) rfl
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) calleeOwnedUnique calleeOwnedReadable

theorem returnedRun : returnOwned callerContext calleeOwned ty localVector.2 false = some returned := by
  have live : (returnOwned callerContext calleeOwned ty localVector.2 false).isSome = true := by decide +kernel
  have nonempty : returnOwned callerContext calleeOwned ty localVector.2 false ≠ none := by
    intro missing
    simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (callerContext,0)).symm
example := returnOwned_target callerContext calleeOwned returned.1 ty localVector.2 returned.2 false returnedRun (by decide +kernel)

theorem calleeOwnedCovered : OwnsAll calleeOwned.objects.heap := by
  have beforeHeap : calleeChanged.objects.heap = transferred.heap :=
    (Proofs.CppMoveContext.prepareSaved_effects callerContext prepared arguments preparedRun).1
  apply Proofs.CppMoveViews.construct_ownsAll calleeChanged.objects localVector.1 allow 5 calleeChanged.scope localVector.2 true localVectorRun
  rw [beforeHeap]
  exact transferredCovered

theorem calleeOwnedValid : Proofs.CppMoveFrame.AllocationsValid calleeOwned.objects.heap ty := by
  have beforeHeap : calleeChanged.objects.heap = transferred.heap :=
    (Proofs.CppMoveContext.prepareSaved_effects callerContext prepared arguments preparedRun).1
  apply Proofs.CppMoveFrame.construct_allocationsValid calleeChanged.objects localVector.1 ty allow 5 calleeChanged.scope localVector.2 true localVectorRun
  rw [beforeHeap]
  exact transferredValid

theorem calleeOwnedBounds : Proofs.CppMoveWrite.GrantBounds calleeOwned.objects.heap := by
  have beforeHeap : calleeChanged.objects.heap = transferred.heap :=
    (Proofs.CppMoveContext.prepareSaved_effects callerContext prepared arguments preparedRun).1
  apply Proofs.CppMoveWrite.construct_grantBounds calleeChanged.objects localVector.1 allow 5 calleeChanged.scope localVector.2 true localVectorRun
  rw [beforeHeap]
  exact Proofs.CppMoveWrite.assign_grantBounds initial transferred allow 3 0 transferredRun WriteExamples.initialGrantBounds

example := returnOwned_invariants callerContext calleeOwned returned.1 ty localVector.2 returned.2 false returnedRun
  calleeOwnedUnique calleeOwnedReadable calleeOwnedCovered calleeOwnedValid calleeOwnedBounds
example := returnOwned_resources callerContext calleeOwned returned.1 ty localVector.2 returned.2 false returnedRun (by decide +kernel)
example := returnOwned_no_resurrection callerContext calleeOwned returned.1 ty localVector.2 returned.2 999 false returnedRun rfl
#guard work returned.1 == work calleeOwned+3
#guard returned.1.objects.heap.liveSpace == calleeOwned.objects.heap.liveSpace
#guard returned.1.objects.heap.baseSpace == calleeOwned.objects.heap.baseSpace

def highCallee : Context := {calleeOwned with objects := {calleeOwned.objects with heap := {calleeOwned.objects.heap with peak := 400,baseSpace := 2}},scalars := {calleeOwned.scalars with peak := 350},peak := 600}
def highReturned := (returnOwned callerContext highCallee ty localVector.2 true).getD (callerContext,0)
#guard (returnOwned callerContext highCallee ty localVector.2 true).isSome
#guard highReturned.1.objects.heap.peak == 400
#guard highReturned.1.objects.heap.baseSpace == 2
#guard highReturned.1.scalars.peak == 350
#guard highReturned.1.peak == 750
#guard work highReturned.1 == work highCallee+3

def emptyCaller : Context := ⟨⟨⟨[],[],[],0,0,0⟩,[]⟩,⟨[],[],0,0,0⟩,[],0,0⟩
def emptyCallee : Context := {emptyCaller with objects := ⟨⟨[some ⟨none,1,true,8⟩],[],[],0,0,0⟩,[⟨0,true⟩]⟩,scope := 1}
def emptyReturned := (returnOwned emptyCaller emptyCallee ty 0 false).getD (emptyCaller,0)
#guard (returnOwned emptyCaller emptyCallee ty 0 false).isSome
#guard emptyReturned.1.objects.heap.header 0 == none
#guard emptyReturned.1.objects.heap.header 1 == some ⟨none,0,false,8⟩
#guard emptyReturned.1.objects.heap.liveSpace == 1
#guard emptyReturned.1.objects.heap.peak == 2
#guard work emptyReturned.1 == 3

def reservedCallee : Context := {emptyCallee with objects := ⟨⟨[some ⟨some 0,1,true,8⟩],[some ⟨⟨0,[],4,8,0⟩,fun _ => 0⟩],[],0,0,0⟩,[⟨0,true⟩]⟩}
def reservedReturned := (returnOwned emptyCaller reservedCallee ty 0 false).getD (emptyCaller,0)
#guard (returnOwned emptyCaller reservedCallee ty 0 false).isSome
#guard reservedReturned.1.objects.heap.liveSpace == 5
#guard reservedReturned.1.objects.heap.peak == 6
#guard (reservedReturned.1.objects.heap.allocation 0).map (fun t => t.buffer.capacity) == some 4
#guard work reservedReturned.1 == 3

def otherCallee : Context := {emptyCallee with objects := ⟨⟨[some ⟨some 0,1,true,8⟩,some ⟨some 1,1,true,8⟩],
  [some ⟨⟨0,[1,2],2,8,0⟩,fun _ => 0⟩,some ⟨⟨1,[3,4,5],3,8,0⟩,fun _ => 0⟩],[],0,0,0⟩,[⟨0,true⟩,⟨1,true⟩]⟩}
def otherReturned := (returnOwned emptyCaller otherCallee ty 0 true).getD (emptyCaller,0)
#guard (returnOwned emptyCaller otherCallee ty 0 true).isSome
#guard otherReturned.1.objects.heap.header 0 == none
#guard otherReturned.1.objects.heap.header 1 == none
#guard otherReturned.1.objects.heap.header 2 == some ⟨some 0,0,true,8⟩
#guard (otherReturned.1.objects.heap.allocation 1).isNone
#guard (otherReturned.1.objects.heap.allocation 0).map (fun t => t.buffer.items) == some [1,2]
#guard work otherReturned.1 == 7
#guard otherReturned.1.objects.heap.liveSpace == 3
#guard otherReturned.1.objects.heap.peak == 8

def borrowedReturned := (returnOwned callerContext calleeChanged ty 5 true).getD (callerContext,0)
#guard (returnOwned callerContext calleeChanged ty 5 true).isSome
#guard borrowedReturned.1.objects.heap.header 1 == some ⟨none,0,true,8⟩
#guard borrowedReturned.1.objects.heap.header 2 == some ⟨some 0,2,true,8⟩
#guard work borrowedReturned.1 == work calleeChanged+2
#guard borrowedReturned.1.objects.heap.liveSpace == calleeChanged.objects.heap.liveSpace+1
end ReturnExamples
'''

NATIVE = r'''

#include <cassert>
#include <utility>
#include <vector>
static long long* escaped=nullptr;
std::vector<long long> makeData(int mode){
  std::vector<long long> data;
  if(mode==1)data.reserve(4);
  if(mode==2){data={1,2};data.reserve(4);escaped=&data.back();}
  std::vector<long long> unrelated{3,4,5};
  return std::move(data);
}
std::vector<long long> returnBorrowed(std::vector<long long>& source){
  std::vector<long long> unrelated{3,4,5};
  return std::move(source);
}
cp::UnionFind makeUnionFind(int n){
  cp::UnionFind data(n),unrelated(3);
  if(n>1)data.unite(0,n-1);
  return std::move(data);
}
int main(){
  for(int mode : {0,1,2}){
    const std::vector<long long> result=makeData(mode);
    if(mode==0)assert(result.empty() && result.capacity()==0);
    if(mode==1)assert(result.empty() && result.capacity()>=4);
    if(mode==2){assert(result.size()==2 && *escaped==2);*escaped=42;assert(result.back()==42);}
  }
  std::vector<long long> source{7,8};auto* saved=&source.back();
  auto returned=returnBorrowed(source);
  assert(source.empty() && source.capacity()==0 && &returned.back()==saved && *saved==8);
  source.push_back(3);*saved=19;assert(source[0]==3 && returned.back()==19);
  for(int n : {0,1,2,17}){
    auto returnedClass=makeUnionFind(n);
    assert(returnedClass.num_groups()==n-(n>1));
    if(n>1){assert(returnedClass.same(0,n-1));assert(returnedClass.size(0)==2);}
    else if(n==1)assert(returnedClass.size(0)==1);
  }
}
'''

class MoveReturnTests(unittest.TestCase):
    def test_owned_return_invariants_and_resources(self):
        with tempfile.TemporaryDirectory(prefix='move-return-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveReturn\n'+HEADER_CHECKS+FRAME_CHECKS+WRITE_CHECKS+CONTEXT_CHECKS+DESTROY_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_native_return_after_local_destruction(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='move-return-native-') as directory:
            source=Path(directory)/'check.cpp';binary=Path(directory)/'check'
            source.write_text('#include "'+str(SOURCE)+'"\n'+NATIVE)
            subprocess.run(['g++','-std=c++17','-O1','-fno-elide-constructors',
                '-fsanitize=address,undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

if __name__=='__main__':
    disable_network()
    unittest.main()
