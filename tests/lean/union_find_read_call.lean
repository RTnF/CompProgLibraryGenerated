import Proofs.CppMoveFrameScopes
namespace UfReadCallExamples
open Proofs.CppMoveContext Proofs.CppMoveReadReceiver Proofs.CppMoveObjectReceiver
open Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppConstructorFinish Proofs.CppScalar Proofs.DoublingNested Proofs.UfRootCall
open Proofs.UfReadPrograms Proofs.UfReadCall Proofs.CppMoveReceiverResolve
abbrev limit := Proofs.CppVectorBindings.sizeLimit i32
def parents : List Int := [-2,0,-2,2]
def data : Proofs.CppVector.Buffer Int := ⟨0,parents,4,limit,0⟩
def input (w : Bool) : Context := ⟨⟨⟨[some ⟨some 0,0,w,limit⟩],
  [some ⟨data,fun _ => 0⟩],[],0,0,0⟩,[⟨0,false⟩]⟩,
  ⟨[⟨i32,2⟩,⟨i32,99⟩,⟨i32,1⟩,⟨i32,3⟩],[⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1,.scalar 2,.scalar 3],0,0⟩
def object : ObjectRef := ⟨0,[1,2]⟩
def receiver (w : Bool) : ReadReceiver (input w) object i32 :=
  ⟨⟨1,0,0,false,2,rfl,rfl,rfl,by decide +kernel⟩,
   ⟨2,1,1,false,99,rfl,rfl,rfl,by decide +kernel⟩,
   rfl,0,⟨0,false⟩,⟨some 0,0,w,limit⟩,rfl,rfl⟩

theorem header (w : Bool) (id : Nat) (h : Header) (found : (input w).objects.heap.header id = some h) :
    id=0 ∧ h=⟨some 0,0,w,limit⟩ := by
  have inside := (List.getElem?_eq_some_iff.mp (header_lookup _ _ _ found)).1
  change id < 1 at inside
  have zero : id=0 := by omega
  subst id
  have atZero : (input w).objects.heap.header 0 = some ⟨some 0,0,w,limit⟩ := rfl
  rw [atZero] at found
  exact ⟨rfl,(Option.some.inj found).symm⟩

theorem unique (w : Bool) : Unique (input w).objects.heap := by
  intro i j hi hj owner fi fj oi oj
  exact (header w i hi fi).1.trans (header w j hj fj).1.symm

theorem covered (w : Bool) : OwnsAll (input w).objects.heap := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside (input w).objects.heap owner tracked found
  change owner < 1 at inside
  have zero : owner=0 := by omega
  subst owner
  exact ⟨0,⟨some 0,0,w,limit⟩,rfl,rfl⟩

theorem allocations (w : Bool) : AllocationsValid (input w).objects.heap i32 := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside (input w).objects.heap owner tracked found
  change owner < 1 at inside
  have zero : owner=0 := by omega
  subst owner
  have atZero : (input w).objects.heap.allocation 0 = some ⟨data,fun _ => 0⟩ := rfl
  rw [atZero] at found
  have same := Option.some.inj found
  subst tracked
  exact ⟨rfl,by decide +kernel⟩

theorem readable (w : Bool) : Proofs.CppMoveHeaders.readable (input w).objects.heap (receiver w).header i32.valid = true := by
  exact (by decide +kernel : Proofs.CppMoveHeaders.readable (input true).objects.heap (receiver true).header i32.valid = true)

theorem contexts (w : Bool) : ∀ owner scope, (project (input w) i32).frame.state.forest.context owner = some scope → scope ≤ (input w).scope := by
  apply Proofs.CppMoveFrameScopes.contexts_of_headers (input w).objects i32 (input w).scope
  intro id h found
  obtain ⟨_,rfl⟩ := header w id h found
  exact Nat.le_refl _

theorem forest : Forest parents id := by
  constructor
  · intro x member
    simp only [parents,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide +kernel
  · intro i p found nonneg
    have inside := (List.getElem?_eq_some_iff.mp found).1
    change i < 4 at inside
    have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl | rfl | rfl | rfl <;> simp [parents] at found <;> subst p <;> simp_all [parents]
  · intro i p found nonneg
    have inside := (List.getElem?_eq_some_iff.mp found).1
    change i < 4 at inside
    have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases choices with rfl | rfl | rfl | rfl <;> simp [parents] at found <;> subst p <;> simp_all

theorem weights : Proofs.UfFieldsSize.Weights parents := by
  intro i weight found negative
  have inside := (List.getElem?_eq_some_iff.mp found).1
  change i < 4 at inside
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases choices with rfl | rfl | rfl | rfl <;> simp [parents] at found <;> subst weight <;> simp_all [parents]

theorem oneArg (w : Bool) : Ready (input w) i32 [(.variable i32 3,1)] := by
  intro e value member
  rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
  exact ⟨rfl,rfl,rfl⟩

theorem twoArgs (w : Bool) : Ready (input w) i32 [(.variable i32 3,1),(.variable i32 4,3)] := by
  intro e value member
  rcases List.mem_cons.mp member with equal | member
  · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,rfl⟩
  · rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,rfl⟩

example (w : Bool) := size_call (input w) object (receiver w) data rfl id forest
  (by decide +kernel) weights 1 (by decide +kernel) (.variable i32 3) rfl rfl rfl
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
example (w : Bool) := same_call (input w) object (receiver w) data rfl id forest
  (by decide +kernel) 1 3 (by decide +kernel) (by decide +kernel)
  (.variable i32 3) (.variable i32 4) (twoArgs w)
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
example (w : Bool) := counter_call (input w) object (receiver w)
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)

#guard (match Proofs.CppMoveCallBindings.callFuel sizeProgram 128 (input false) i32
    [.vectorReference 0,.scalarReference 1,.value (.variable i32 2),.value (.variable i32 3)] with
  | .finished (out,result) => result == .scalar 2 && out.scalars.memory == (input false).scalars.memory &&
      out.objects.heap.headers == (input false).objects.heap.headers && out.objects.views == (input false).objects.views
  | _ => false)
#guard (match Proofs.CppMoveCallBindings.callFuel sameProgram 128 (input false) i32
    [.vectorReference 0,.scalarReference 1,.value (.variable i32 2),.value (.variable i32 3),.value (.variable i32 4)] with
  | .finished (out,result) => result == .scalar 0 && out.scalars.memory == (input false).scalars.memory &&
      out.objects.heap.headers == (input false).objects.heap.headers && out.objects.views == (input false).objects.views
  | _ => false)
#guard (match Proofs.CppMoveCallBindings.callFuel counterProgram 2 (input false) i32
    [.vectorReference 0,.scalarReference 1,.value (.variable i32 2)] with
  | .finished (out,result) => result == .scalar 2 && out.scalars.memory == (input false).scalars.memory
  | _ => false)
end UfReadCallExamples

namespace UfReadGeneratedCallChecks
open UfReadCallExamples Proofs.DoublingNested Proofs.CppNestedProgram
#guard (match UnionFindPublicCompat.UnionFind_size_1_2_callFuel 128 (input false) object [.value (.variable i32 3)] with
  | .finished (out,result) => result == .scalar 2 && out.scalars.memory == (input false).scalars.memory
  | _ => false)
#guard (match UnionFindPublicCompat.UnionFind_same_2_2_callFuel 128 (input false) object
    [.value (.variable i32 3),.value (.variable i32 4)] with
  | .finished (out,result) => result == .scalar 0 && out.scalars.memory == (input false).scalars.memory
  | _ => false)
#guard (match UnionFindPublicCompat.UnionFind_num_groups_0_2_callFuel 2 (input false) object [] with
  | .finished (out,result) => result == .scalar 2 && out.scalars.memory == (input false).scalars.memory
  | _ => false)
end UfReadGeneratedCallChecks
