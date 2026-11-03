import Proofs.CppMoveFrameScopes
namespace UfReadMultiOwnerExamples
open Proofs.CppMoveContext Proofs.CppMoveReadReceiver Proofs.CppMoveObjectReceiver
open Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppConstructorFinish Proofs.CppScalar Proofs.DoublingNested Proofs.UfRootCall
open Proofs.UfReadPrograms Proofs.UfReadCall Proofs.CppMoveReceiverResolve
abbrev limit := Proofs.CppVectorBindings.sizeLimit i32
def parents : List Int := [-2,0,-2,2]
def data : Proofs.CppVector.Buffer Int := ⟨0,parents,4,limit,0⟩
def otherData : Proofs.CppVector.Buffer Int := ⟨1,[-1,-1],2,limit,7⟩
def input (w : Bool) : Context := ⟨⟨⟨[some ⟨some 0,0,w,limit⟩,some ⟨some 1,1,true,limit⟩],
  [some ⟨data,fun _ => 0⟩,some ⟨otherData,fun _ => 0⟩],[],0,0,0⟩,[⟨0,false⟩,⟨1,true⟩]⟩,
  ⟨[⟨i32,2⟩,⟨i32,99⟩,⟨i32,1⟩,⟨i32,3⟩,⟨i32,2⟩,⟨i32,2⟩],
    [⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩,⟨4,true⟩,⟨5,true⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1,.scalar 2,.scalar 3,.vector 1,.scalar 4,.scalar 5],1,0⟩
def object : ObjectRef := ⟨0,[1,2]⟩
def receiver (w : Bool) : ReadReceiver (input w) object i32 :=
  ⟨⟨1,0,0,false,2,rfl,rfl,rfl,by decide +kernel⟩,
   ⟨2,1,1,false,99,rfl,rfl,rfl,by decide +kernel⟩,
   rfl,0,⟨0,false⟩,⟨some 0,0,w,limit⟩,rfl,rfl⟩

theorem header (w : Bool) (id : Nat) (h : Header) (found : (input w).objects.heap.header id = some h) :
    (id=0 ∧ h=⟨some 0,0,w,limit⟩) ∨ (id=1 ∧ h=⟨some 1,1,true,limit⟩) := by
  have inside := (List.getElem?_eq_some_iff.mp (header_lookup _ _ _ found)).1
  change id < 2 at inside
  have choices : id=0 ∨ id=1 := by omega
  rcases choices with rfl | rfl
  · have atZero : (input w).objects.heap.header 0 = some ⟨some 0,0,w,limit⟩ := rfl
    rw [atZero] at found
    exact Or.inl ⟨rfl,(Option.some.inj found).symm⟩
  · have atOne : (input w).objects.heap.header 1 = some ⟨some 1,1,true,limit⟩ := rfl
    rw [atOne] at found
    exact Or.inr ⟨rfl,(Option.some.inj found).symm⟩

theorem owner_header (w : Bool) (id : Nat) (h : Header) (owner : Nat)
    (found : (input w).objects.heap.header id = some h) (owns : h.allocation = some owner) : id=owner := by
  rcases header w id h found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Option.some.inj owns
  · exact Option.some.inj owns

theorem unique (w : Bool) : Unique (input w).objects.heap := by
  intro i j hi hj owner fi fj oi oj
  exact (owner_header w i hi owner fi oi).trans (owner_header w j hj owner fj oj).symm

theorem covered (w : Bool) : OwnsAll (input w).objects.heap := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside (input w).objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · exact ⟨0,⟨some 0,0,w,limit⟩,rfl,rfl⟩
  · exact ⟨1,⟨some 1,1,true,limit⟩,rfl,rfl⟩

theorem allocations (w : Bool) : AllocationsValid (input w).objects.heap i32 := by
  intro owner tracked found
  have inside := Proofs.CppMoveAssign.allocation_inside (input w).objects.heap owner tracked found
  change owner < 2 at inside
  have choices : owner=0 ∨ owner=1 := by omega
  rcases choices with rfl | rfl
  · have atZero : (input w).objects.heap.allocation 0 = some ⟨data,fun _ => 0⟩ := rfl
    rw [atZero] at found
    have same := Option.some.inj found
    subst tracked
    exact ⟨rfl,by decide +kernel⟩
  · have atOne : (input w).objects.heap.allocation 1 = some ⟨otherData,fun _ => 0⟩ := rfl
    rw [atOne] at found
    have same := Option.some.inj found
    subst tracked
    exact ⟨rfl,by decide +kernel⟩

theorem readable (w : Bool) : Proofs.CppMoveHeaders.readable (input w).objects.heap (receiver w).header i32.valid = true := by
  exact (by decide +kernel : Proofs.CppMoveHeaders.readable (input true).objects.heap (receiver true).header i32.valid = true)

theorem contexts (w : Bool) : ∀ owner scope, (project (input w) i32).frame.state.forest.context owner = some scope → scope ≤ (input w).scope := by
  apply Proofs.CppMoveFrameScopes.contexts_of_headers (input w).objects i32 (input w).scope
  intro id h found
  rcases header w id h found with ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1

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


def otherObject : ObjectRef := ⟨5,[6,7]⟩
def otherReceiver (w : Bool) : ReadReceiver (input w) otherObject i32 :=
  ⟨⟨6,4,4,true,2,rfl,rfl,rfl,by decide +kernel⟩,
   ⟨7,5,5,true,2,rfl,rfl,rfl,by decide +kernel⟩,
   rfl,1,⟨1,true⟩,⟨some 1,1,true,limit⟩,rfl,rfl⟩
def liveReference : Proofs.CppNestedVectorBindings.Reference := ⟨1,i32,true,⟨1,7,0⟩⟩
def staleReference : Proofs.CppNestedVectorBindings.Reference := ⟨1,i32,true,⟨1,6,0⟩⟩
#guard (project (input false) i32).frame.read liveReference == some (-1)
#guard ((project (input false) i32).frame.read staleReference).isNone
end UfReadMultiOwnerExamples

namespace UfReadMultiOwnerWorldExamples
open UfReadMultiOwnerExamples Proofs.UfReadValues Proofs.UfReadPrograms
open Proofs.CppMoveContext Proofs.CppMoveReadReceiver Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveReceiverResolve Proofs.CppMoveReceiverPermissions Proofs.CppMoveFrame Proofs.DoublingNested
open Proofs.CppMoveCallBindings Proofs.CppScalar

def Preserved (w : Bool) (out : Context) : Prop :=
  (∀ owner, (project out i32).frame.state.storage.lookup owner = (project (input w) i32).frame.state.storage.lookup owner) ∧
  (∀ reference, (project out i32).frame.read reference = (project (input w) i32).frame.read reference) ∧
  ∃ next : ReadReceiver out object i32,
    next.counter.value = (receiver w).counter.value ∧ next.size.value = (receiver w).size.value

theorem world (w : Bool) (out : Context) (program : NProgram) (expressions : List (NExpr × Int))
    (ready : Ready (input w) i32 expressions)
    (params : program.parameters = .vector i32 false :: .scalar i32 true false :: .scalar i32 false true :: parameters i32 expressions)
    (retType : Ty) (scalar : program.result = .scalar retType) (allowed : Proofs.CppFixedRun.Allowed program.body = true)
    (fuel : Nat) (result : Ret)
    (actual : callFuel program fuel (input w) i32 (readArguments (input w) object (receiver w) expressions) = .finished (out,result))
    (payload : ∃ buffer, (project out i32).frame.state.storage.lookup data.owner = some buffer ∧ buffer.items = data.items.map Proofs.CppNestedVectorStore.Value.integer)
    (memory : out.scalars.memory = (input w).scalars.memory) : Preserved w out := by
  have all := all_payload (input w) out object (receiver w) program expressions ready params retType scalar allowed data rfl
    (readable w) (unique w) (covered w) (allocations w) rfl (contexts w) fuel result actual payload
  have oldValid := materialize_ready (input w).objects i32 (by decide +kernel) (allocations w)
  have reads := reads (input w) out program fuel _ result (covered w) oldValid actual all
  let after := receiver_after (input w) out object (receiver w)
    (Proofs.CppMoveCallLayout.call_layout program fuel (input w) out i32 _ result actual) memory
  exact ⟨all,reads,after,rfl,rfl⟩

example (w : Bool) : ∃ fuel out weight,
    callFuel sizeProgram fuel (input w) i32 (readArguments (input w) object (receiver w) [(.variable i32 3,1)]) =
      .finished (out,.scalar (-weight)) ∧ Preserved w out := by
  obtain ⟨fuel,out,root,weight,call,_,_,_,_,_,_,memory,_,payload⟩ :=
    Proofs.UfReadPrepareBudget.size_call (input w) object (receiver w) data rfl id forest (by decide +kernel) weights 1
      (by decide +kernel) (.variable i32 3) rfl rfl rfl (readable w) (unique w) (covered w) (allocations w) rfl
      (by change 0 ≤ _; omega) (contexts w)
  exact ⟨fuel,out,weight,call,world w out sizeProgram [(.variable i32 3,1)] (oneArg w) rfl i32 rfl
    (by decide +kernel) fuel (.scalar (-weight)) call payload memory⟩

example (w : Bool) : ∃ fuel out answer,
    callFuel sameProgram fuel (input w) i32
      (readArguments (input w) object (receiver w) [(.variable i32 3,1),(.variable i32 4,3)]) =
      .finished (out,.scalar answer) ∧ Preserved w out := by
  obtain ⟨fuel,out,r1,r2,call,_,_,_,_,memory,_,payload⟩ :=
    Proofs.UfReadPrepareBudget.same_call (input w) object (receiver w) data rfl id forest (by decide +kernel) 1 3
      (by decide +kernel) (by decide +kernel) (.variable i32 3) (.variable i32 4) (twoArgs w)
      (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
  exact ⟨fuel,out,_,call,world w out sameProgram [(.variable i32 3,1),(.variable i32 4,3)] (twoArgs w) rfl
    Proofs.PrefixSumsCall.bT rfl (by decide +kernel) fuel _ call payload memory⟩

example (w : Bool) : ∃ fuel out,
    callFuel counterProgram fuel (input w) i32 (readArguments (input w) object (receiver w) []) =
      .finished (out,.scalar (receiver w).counter.value) ∧ Preserved w out := by
  obtain ⟨actualData,fuel,out,current,call,_,memory,_,payload⟩ :=
    Proofs.UfReadPrepareBudget.counter_call (input w) object (receiver w) (readable w) (unique w) (covered w)
      (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
  have same : actualData = data := Option.some.inj (current.symm.trans (show _ = some data from rfl))
  subst actualData
  exact ⟨fuel,out,call,world w out counterProgram [] (by intro e value member; simp at member) rfl i32 rfl
    (by decide +kernel) fuel _ call payload memory⟩
end UfReadMultiOwnerWorldExamples

namespace UfReadMultiOwnerSourceChecks
open UfReadMultiOwnerExamples Proofs.DoublingNested
example (w : Bool) := Proofs.UfReadValues.size_call (input w) object (receiver w) data rfl id forest
  (by decide +kernel) weights 1 (by decide +kernel) (.variable i32 3) rfl rfl rfl
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
example (w : Bool) := Proofs.UfReadValues.same_call (input w) object (receiver w) data rfl id forest
  (by decide +kernel) 1 3 (by decide +kernel) (by decide +kernel)
  (.variable i32 3) (.variable i32 4) (twoArgs w)
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
example (w : Bool) := Proofs.UfReadValues.counter_call (input w) object (receiver w)
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
end UfReadMultiOwnerSourceChecks

namespace UfReadOtherMutableExamples
open UfReadMultiOwnerExamples Proofs.UfReadValues Proofs.CppMoveContext
open Proofs.CppMoveObjectReceiver Proofs.CppMoveCallLayout Proofs.DoublingNested

def mutableOther (w : Bool) : Receiver (input w) otherObject i32 :=
  ⟨(otherReceiver w).counter,(otherReceiver w).size,(otherReceiver w).fields,rfl,
    (otherReceiver w).viewSlot,(otherReceiver w).view,(otherReceiver w).header,
    (otherReceiver w).located,(otherReceiver w).resolved,rfl⟩

example (w : Bool) (out : Context) (kept : Preserved (input w) out object (receiver w)) :
    ∃ next : Receiver out otherObject i32,
      next.counter.value = 2 ∧ next.size.value = 2 ∧ next.counter.writable = true ∧ next.view.writable = true := by
  let next := Receiver.update (input w) out otherObject i32 (mutableOther w) kept.layout 2 2
    (by rw [kept.memory]; rfl) (by decide +kernel) (by rw [kept.memory]; rfl) (by decide +kernel)
  exact ⟨next,rfl,rfl,rfl,rfl⟩

open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.UfReadPrograms
#guard (match Proofs.CppMoveCallBindings.callFuel sizeProgram 128 (input false) i32
    [.vectorReference 0,.scalarReference 1,.value (.variable i32 2),.value (.variable i32 3)] with
  | .finished (middle,_) =>
    match Proofs.CppMoveCallBindings.callFuel Proofs.UnionFindCandidateInstance.UnionFind_unite 256 middle i32
      [.vectorReference 5,.scalarReference 6,.value (.variable i32 7),.value (.literal i32 0),.value (.literal i32 1)] with
    | .finished (out,_) =>
      (project out i32).frame.read liveReference == some (-2) &&
      ((project out i32).frame.read staleReference).isNone &&
      (out.scalars.memory[4]?).map (·.value) == some 1 &&
      ((project out i32).frame.state.storage.lookup 0).map (·.items) == some (parents.map .integer)
    | _ => false
  | _ => false)
end UfReadOtherMutableExamples
