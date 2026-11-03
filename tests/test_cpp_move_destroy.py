"""Reverse lifetime order, scope cleanup, reference invalidation and resources."""
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
from offline import disable_network

CHECKS = r'''

namespace DestroyExamples
open Proofs.CppMoveDestroy HeaderMoveExamples ViewExamples FrameExamples ContextExamples
-- Source header0 is empty after moving to target header1 (scope0).
def sourceGone := (destroyHeader transferred.heap allow 0).getD transferred.heap
#guard (destroyHeader transferred.heap allow 0).isSome
#guard sourceGone.header 0 == none
#guard Proofs.CppMoveHeaders.read sourceGone allow 0 == some 11
#guard sourceGone.liveSpace+1 == transferred.heap.liveSpace
#guard (Proofs.CppMoveViews.resolve ⟨sourceGone,transferred.views⟩ 0).isNone
#guard (Proofs.CppMoveViews.resolve ⟨sourceGone,transferred.views⟩ 3).isSome
def targetGone := (destroyHeader transferred.heap allow 1).getD transferred.heap
#guard targetGone.header 1 == none
#guard (Proofs.CppMoveHeaders.read targetGone allow 0).isNone
#guard targetGone.liveSpace == 1
#guard (destroyHeader sourceGone allow 0).isNone
#guard (destroyHeader transferred.heap allow 999).isNone
#guard (destroyHeader constructed.1.heap allow 2).isSome
#guard (destroyScope transferred.heap allow 1).map (fun s => s.liveSpace) == some 5
#guard (destroyScope transferred.heap allow 1).bind (fun s => Proofs.CppMoveHeaders.read s allow 0) == some 11
#guard (destroyScope constructed.1.heap allow 0).bind (fun s => Proofs.CppMoveHeaders.read s allow 0) == none

theorem transferredReadable : ReadableHeaders transferred.heap allow := by
  intro id header found
  have inside := source_inside transferred.heap id header found
  change id < 2 at inside
  have cases : id = 0 ∨ id = 1 := by omega
  rcases cases with eq | eq <;> subst id
  · have actual : transferred.heap.header 0 = some ⟨none,1,true,8⟩ := rfl
    rw [actual] at found
    cases Option.some.inj found
    decide
  · have actual : transferred.heap.header 1 = some ⟨some 0,0,true,8⟩ := rfl
    rw [actual] at found
    cases Option.some.inj found
    decide
example := destroyScope_ready transferred.heap allow 1 transferredUnique transferredReadable
example := destroyed_space transferred.heap 0 ⟨none,1,true,8⟩ rfl
example := destroyed_space transferred.heap 1 ⟨some 0,0,true,8⟩ rfl
example := destroyed_unique transferred.heap 1 ⟨some 0,0,true,8⟩ rfl transferredUnique
example := destroyed_ownsAll transferred.heap 1 ⟨some 0,0,true,8⟩ rfl transferredCovered
-- The callee moves a borrowed vector into a local object in its own scope.
def localVector := (Proofs.CppMoveViews.construct calleeChanged.objects allow 5 calleeChanged.scope true).getD (calleeChanged.objects,0)
def calleeOwned : Proofs.CppMoveContext.Context := {calleeChanged with objects := localVector.1}
#guard (Proofs.CppMoveContext.finishBorrowed callerContext calleeOwned).isNone
#guard (finishScope callerContext calleeOwned ty).isSome
def callerAfter := (finishScope callerContext calleeOwned ty).getD callerContext
#guard (Proofs.CppMoveHeaders.read callerAfter.objects.heap allow 0).isNone
#guard callerAfter.objects.heap.header 1 == some ⟨none,0,true,8⟩
#guard callerAfter.objects.heap.header 2 == none
#guard (Proofs.CppMoveContext.project callerAfter ty).scalarCell 1 ty == some (⟨0,true⟩,⟨ty,9⟩)

theorem localVectorRun : Proofs.CppMoveViews.construct calleeChanged.objects allow 5 calleeChanged.scope true = some localVector := by
  have live : (Proofs.CppMoveViews.construct calleeChanged.objects allow 5 calleeChanged.scope true).isSome = true := by decide +kernel
  have nonempty : Proofs.CppMoveViews.construct calleeChanged.objects allow 5 calleeChanged.scope true ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty (calleeChanged.objects,0)).symm
theorem calleeOwnedUnique : Unique calleeOwned.objects.heap := by
  have beforeHeap : calleeChanged.objects.heap = transferred.heap :=
    (Proofs.CppMoveContext.prepareSaved_effects callerContext prepared arguments preparedRun).1
  have beforeUnique : Unique calleeChanged.objects.heap := by rw [beforeHeap]; exact transferredUnique
  exact Proofs.CppMoveViews.construct_unique calleeChanged.objects localVector.1 allow 5 calleeChanged.scope localVector.2 true localVectorRun beforeUnique
theorem calleeOwnedReadable : ReadableHeaders calleeOwned.objects.heap ty.valid := by
  intro id header found
  have inside := source_inside calleeOwned.objects.heap id header found
  change id < 3 at inside
  have cases : id = 0 ∨ id = 1 ∨ id = 2 := by omega
  rcases cases with eq | eq | eq <;> subst id
  · have actual : calleeOwned.objects.heap.header 0 = some ⟨none,1,true,8⟩ := by decide +kernel
    rw [actual] at found
    cases Option.some.inj found
    decide
  · have actual : calleeOwned.objects.heap.header 1 = some ⟨none,0,true,8⟩ := by decide +kernel
    rw [actual] at found
    cases Option.some.inj found
    decide
  · have actual : calleeOwned.objects.heap.header 2 = some ⟨some 0,3,true,8⟩ := by decide +kernel
    rw [actual] at found
    cases Option.some.inj found
    decide +kernel
example := finishScope_ready callerContext calleeOwned ty (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) calleeOwnedUnique calleeOwnedReadable
def scopeSourceGone := (destroyScope transferred.heap allow 1).getD transferred.heap
theorem scopeSourceRun : destroyScope transferred.heap allow 1 = some scopeSourceGone := by
  have live : (destroyScope transferred.heap allow 1).isSome = true := by decide +kernel
  have nonempty : destroyScope transferred.heap allow 1 ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty transferred.heap).symm
example := destroyScope_all transferred.heap scopeSourceGone allow 1 scopeSourceRun
example := destroyScope_no_resurrection transferred.heap scopeSourceGone allow 1 999 scopeSourceRun rfl

example := destroyList_ownsAll transferred.heap scopeSourceGone allow 1
  (scopeOrder transferred.heap) scopeSourceRun transferredCovered
example := destroyList_allocationsValid transferred.heap scopeSourceGone allow ty 1
  (scopeOrder transferred.heap) scopeSourceRun transferredValid
example := destroyList_grantBounds transferred.heap scopeSourceGone allow 1
  (scopeOrder transferred.heap) scopeSourceRun
  (Proofs.CppMoveWrite.assign_grantBounds initial transferred allow 3 0 transferredRun WriteExamples.initialGrantBounds)
example := destroyList_resources transferred.heap scopeSourceGone allow 1
  (scopeOrder transferred.heap) scopeSourceRun
example := destroyScope_work transferred.heap scopeSourceGone allow 1 scopeSourceRun
#guard scopeBudget transferred.heap 1 [0,1] == 1
#guard scopeBudget transferred.heap 0 [0,1] == 3
#guard scopeBudget transferred.heap 0 [1,1] == 6
#guard (destroyList transferred.heap allow 0 [1,1]).map (fun out => out.work) == some (transferred.heap.work+3)
#guard (destroyScope transferred.heap allow 999).map (fun out => out.work) == some transferred.heap.work
#guard scopeSourceGone.peak == max transferred.heap.peak (transferred.heap.liveSpace-transferred.heap.baseSpace)
#guard scopeSourceGone.baseSpace == transferred.heap.baseSpace

#guard scopeOrder initial.heap == [1,0]
#guard scopeOrder constructed.1.heap == [2,1,0]
example := scopeOrder_construct second.1 moved.1 allow 0 0 2 false HeaderMoveExamples.actual
example := scopeOrder_nodup transferred.heap
example := destroyScope_invariants transferred.heap scopeSourceGone ty 1 rfl
  transferredUnique (by
    intro id header found
    have inside := source_inside transferred.heap id header found
    change id < 2 at inside
    have cases : id = 0 ∨ id = 1 := by omega
    rcases cases with rfl | rfl
    · have h : transferred.heap.header 0 = some ⟨none,1,true,8⟩ := rfl
      rw [h] at found
      cases Option.some.inj found
      decide
    · have h : transferred.heap.header 1 = some ⟨some 0,0,true,8⟩ := rfl
      rw [h] at found
      cases Option.some.inj found
      decide) transferredCovered transferredValid
  (Proofs.CppMoveWrite.assign_grantBounds initial transferred allow 3 0 transferredRun WriteExamples.initialGrantBounds)
end DestroyExamples
'''

NATIVE = r'''

#include <cassert>
#include <cstdlib>
#include <new>
#include <optional>
#include <utility>
#include <vector>
// Observe actual default-allocator deallocation without allocating in the log.
static void* watched[4]{};
static int released[8]{};
static int count=0;
void* operator new(std::size_t size){
  if(void* pointer=std::malloc(size ? size : 1))return pointer;
  throw std::bad_alloc();
}
void operator delete(void* pointer) noexcept {
  if(pointer){
    for(int id=0;id<4;++id)if(watched[id]==pointer){
      assert(count<8);released[count++]=id;watched[id]=nullptr;
    }
  }
  std::free(pointer);
}
void operator delete(void* pointer,std::size_t) noexcept {::operator delete(pointer);}
int main(){
  {
    std::vector<long long> first{10,11};watched[0]=first.data();
    const std::vector<long long> second{20,21,22};watched[1]=const_cast<long long*>(second.data());
    assert(count==0);
  }
  assert(count==2 && released[0]==1 && released[1]==0);
  count=0;
  std::optional<std::vector<long long>> outer;
  {
    std::vector<long long> source{7,8};source.reserve(8);
    auto storage=source.data();auto capacity=source.capacity();
    outer.emplace(std::move(source));watched[2]=storage;
    assert(source.empty() && source.capacity()==0);
    assert(outer->data()==storage && outer->capacity()==capacity);
  }
  assert(count==0 && (*outer)[1]==8);
  outer.reset();assert(count==1 && released[0]==2);
  count=0;
  {
    std::vector<long long> source;source.reserve(4);
    watched[3]=source.data();
    const std::vector<long long> target(std::move(source));
    assert(source.capacity()==0 && target.empty() && target.capacity()>=4);
    assert(count==0);
  }
  assert(count==1 && released[0]==3);
  count=0;
  {std::vector<long long> empty;const std::vector<long long> target(std::move(empty));}
  assert(count==0);
}
'''

class MoveDestroyTests(unittest.TestCase):
    def test_scope_lifetimes_invariants_and_resources(self):
        with tempfile.TemporaryDirectory(prefix='move-destroy-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveDestroy\n'+HEADER_CHECKS+FRAME_CHECKS+WRITE_CHECKS+CONTEXT_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_native_default_allocator_cleanup_order(self):
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='move-destroy-native-') as directory:
            source=Path(directory)/'check.cpp';binary=Path(directory)/'check'
            source.write_text(NATIVE)
            subprocess.run(['g++','-std=c++17','-O1','-fno-elide-constructors',
                '-fsanitize=address,undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0:abort_on_error=1'
            subprocess.run([str(binary)],env=env,check=True)

if __name__=='__main__':
    disable_network()
    unittest.main()
