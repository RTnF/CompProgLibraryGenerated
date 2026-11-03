import Proofs.UfObjectIdentity

namespace Proofs.UfObjectPair
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.DoublingNested
open Proofs.UfObjectState Proofs.UfObjectTrace Proofs.CppMoveCallLayout

def Apart {s : Context} {leftObject rightObject : ObjectRef}
    (left : State s leftObject) (right : State s rightObject) : Prop :=
  left.data.owner ≠ right.data.owner ∧ left.receiver.counter.address ≠ right.receiver.counter.address ∧
    left.receiver.counter.address ≠ right.receiver.size.address ∧ left.receiver.size.address ≠ right.receiver.counter.address

theorem Apart.swap {s : Context} {leftObject rightObject : ObjectRef}
    {left : State s leftObject} {right : State s rightObject} (apart : Apart left right) : Apart right left :=
  ⟨Ne.symm apart.1,Ne.symm apart.2.1,Ne.symm apart.2.2.2,Ne.symm apart.2.2.1⟩

theorem apart_after (s out : Context) (leftObject rightObject : ObjectRef)
    (left : State s leftObject) (right : State s rightObject)
    (leftAfter : State out leftObject) (rightAfter : State out rightObject)
    (layout : Layout s out) (apart : Apart left right) : Apart leftAfter rightAfter := by
  have leftIdentity := Proofs.UfObjectIdentity.state s out leftObject left leftAfter layout
  have rightIdentity := Proofs.UfObjectIdentity.state s out rightObject right rightAfter layout
  unfold Apart at apart ⊢
  simpa only [leftIdentity.1,leftIdentity.2.1,leftIdentity.2.2,rightIdentity.1,rightIdentity.2.1,rightIdentity.2.2] using apart

structure Pair (s : Context) (leftObject rightObject : ObjectRef) where
  left : State s leftObject
  right : State s rightObject
  apart : Apart left right

def Pair.swap {s : Context} {leftObject rightObject : ObjectRef} (pair : Pair s leftObject rightObject) : Pair s rightObject leftObject :=
  ⟨pair.right,pair.left,pair.apart.swap⟩

theorem step_left (s : Context) (leftObject rightObject : ObjectRef) (pair : Pair s leftObject rightObject)
    (op : Operation) (ready : op.Valid pair.left.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : Pair out leftObject rightObject),
      Step s leftObject pair.left op fuel out result next.left ∧
      next.right.rank = pair.right.rank ∧ next.right.data.items = pair.right.data.items ∧
      next.right.receiver.counter.value = pair.right.receiver.counter.value ∧ next.right.receiver.size.value = pair.right.receiver.size.value := by
  obtain ⟨fuel,out,result,leftAfter,rightAfter,method,rank,count,size,items⟩ :=
    Proofs.UfObjectValues.pair_step s leftObject rightObject pair.left pair.right op ready
      (Ne.symm pair.apart.1) (Ne.symm pair.apart.2.1) (Ne.symm pair.apart.2.2.1)
  have actual := method.actual
  rw [invoke_state fuel s leftObject pair.left op] at actual
  have layout := call_layout op.program fuel s out i32 _ result actual
  let next : Pair out leftObject rightObject :=
    ⟨leftAfter,rightAfter,apart_after s out leftObject rightObject pair.left pair.right leftAfter rightAfter layout pair.apart⟩
  exact ⟨fuel,out,result,next,method,rank,items,count,size⟩

theorem step_right (s : Context) (leftObject rightObject : ObjectRef) (pair : Pair s leftObject rightObject)
    (op : Operation) (ready : op.Valid pair.right.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : Pair out leftObject rightObject),
      Step s rightObject pair.right op fuel out result next.right ∧
      next.left.rank = pair.left.rank ∧ next.left.data.items = pair.left.data.items ∧
      next.left.receiver.counter.value = pair.left.receiver.counter.value ∧ next.left.receiver.size.value = pair.left.receiver.size.value := by
  obtain ⟨fuel,out,result,next,method,rank,items,count,size⟩ := step_left s rightObject leftObject pair.swap op ready
  exact ⟨fuel,out,result,next.swap,method,rank,items,count,size⟩

end Proofs.UfObjectPair
