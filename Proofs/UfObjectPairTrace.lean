import Proofs.UfObjectPair

namespace Proofs.UfObjectPairTrace
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppLoop
open Proofs.UfObjectState Proofs.UfObjectTrace Proofs.UfObjectPair

inductive Action where
  | left (op : Operation)
  | right (op : Operation)
  deriving DecidableEq, Repr

def Action.Valid (leftLength rightLength : Nat) : Action → Prop
  | .left op => op.Valid leftLength
  | .right op => op.Valid rightLength

def Action.object (leftObject rightObject : ObjectRef) : Action → ObjectRef
  | .left _ => leftObject
  | .right _ => rightObject

def Action.operation : Action → Operation
  | .left op | .right op => op

def selected {s : Context} {leftObject rightObject : ObjectRef} (action : Action) (pair : Pair s leftObject rightObject) :
    State s (action.object leftObject rightObject) :=
  match action with
  | .left _ => pair.left
  | .right _ => pair.right

def Action.otherObject (leftObject rightObject : ObjectRef) : Action → ObjectRef
  | .left _ => rightObject
  | .right _ => leftObject

def other {s : Context} {leftObject rightObject : ObjectRef} (action : Action) (pair : Pair s leftObject rightObject) :
    State s (action.otherObject leftObject rightObject) :=
  match action with
  | .left _ => pair.right
  | .right _ => pair.left

structure PairStep (s : Context) (leftObject rightObject : ObjectRef) (pair : Pair s leftObject rightObject)
    (action : Action) (fuel : Nat) (out : Context) (result : Ret) (next : Pair out leftObject rightObject) : Prop where
  method : Step s (action.object leftObject rightObject) (selected action pair) action.operation fuel out result (selected action next)
  leftSize : next.left.receiver.size.value = pair.left.receiver.size.value
  rightSize : next.right.receiver.size.value = pair.right.receiver.size.value
  otherRank : (other action next).rank = (other action pair).rank
  otherItems : (other action next).data.items = (other action pair).data.items
  otherCount : (other action next).receiver.counter.value = (other action pair).receiver.counter.value
  otherSize : (other action next).receiver.size.value = (other action pair).receiver.size.value

theorem pair_step (s : Context) (leftObject rightObject : ObjectRef) (pair : Pair s leftObject rightObject)
    (action : Action) (ready : action.Valid pair.left.data.items.length pair.right.data.items.length) :
    ∃ (fuel : Nat) (out : Context) (result : Ret) (next : Pair out leftObject rightObject),
      PairStep s leftObject rightObject pair action fuel out result next := by
  cases action with
  | left op =>
    obtain ⟨fuel,out,result,next,method,rank,items,count,size⟩ := step_left s leftObject rightObject pair op ready
    exact ⟨fuel,out,result,next,method,method.size,size,rank,items,count,size⟩
  | right op =>
    obtain ⟨fuel,out,result,next,method,rank,items,count,size⟩ := step_right s leftObject rightObject pair op ready
    exact ⟨fuel,out,result,next,method,size,method.size,rank,items,count,size⟩

def run : Context → ObjectRef → ObjectRef → List (Nat × Action) → Outcome (Context × List Ret)
  | s,_,_,[] => .finished (s,[])
  | s,leftObject,rightObject,(fuel,action)::tail => do
    let (middle,result) ← invoke fuel s (action.object leftObject rightObject) action.operation
    let (out,results) ← run middle leftObject rightObject tail
    pure (out,result::results)

inductive History (leftObject rightObject : ObjectRef) : (s : Context) → Pair s leftObject rightObject → List Action →
    (out : Context) → List Ret → Pair out leftObject rightObject → Prop where
  | nil (s : Context) (pair : Pair s leftObject rightObject) : History leftObject rightObject s pair [] s [] pair
  | cons {s middle out : Context} {pair : Pair s leftObject rightObject} {next : Pair middle leftObject rightObject}
      {last : Pair out leftObject rightObject} {action : Action} {tail : List Action} {result : Ret} {results : List Ret}
      (ready : action.Valid pair.left.data.items.length pair.right.data.items.length) (fuel : Nat)
      (first : PairStep s leftObject rightObject pair action fuel middle result next)
      (rest : History leftObject rightObject middle next tail out results last) :
      History leftObject rightObject s pair (action::tail) out (result::results) last

theorem execute (s : Context) (leftObject rightObject : ObjectRef) (pair : Pair s leftObject rightObject) (actions : List Action)
    (ready : ∀ action ∈ actions, action.Valid pair.left.data.items.length pair.right.data.items.length) :
    ∃ (script : List (Nat × Action)) (out : Context) (results : List Ret) (next : Pair out leftObject rightObject),
      script.map Prod.snd = actions ∧ run s leftObject rightObject script = .finished (out,results) ∧
      results.length = actions.length ∧ next.left.receiver.size.value = pair.left.receiver.size.value ∧
      next.right.receiver.size.value = pair.right.receiver.size.value ∧
      History leftObject rightObject s pair actions out results next := by
  induction actions generalizing s with
  | nil => exact ⟨[],s,[],pair,rfl,rfl,rfl,rfl,rfl,.nil s pair⟩
  | cons action tail ih =>
    obtain ⟨fuel,middle,result,next,first⟩ := pair_step s leftObject rightObject pair action (ready action (by simp))
    have leftLength := same_length s middle leftObject pair.left next.left first.leftSize
    have rightLength := same_length s middle rightObject pair.right next.right first.rightSize
    have restReady : ∀ entry ∈ tail, entry.Valid next.left.data.items.length next.right.data.items.length := by
      intro entry member
      rw [leftLength,rightLength]
      exact ready entry (by simp [member])
    obtain ⟨script,out,results,final,mapped,ran,count,leftSize,rightSize,history⟩ := ih middle next restReady
    exact ⟨(fuel,action)::script,out,result::results,final,by simp [mapped],
      by simp [run,first.method.actual,ran,bind,Outcome.bind,pure],by simp [count],
      leftSize.trans first.leftSize,rightSize.trans first.rightSize,
      .cons (ready action (by simp)) fuel first history⟩

end Proofs.UfObjectPairTrace
