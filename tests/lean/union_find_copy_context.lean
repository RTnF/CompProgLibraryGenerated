namespace UfCopyExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.CppConstructorFinish Proofs.CppMoveFrame Proofs.DoublingNested
open UfReadMultiOwnerExamples

def copied (w : Bool) := Proofs.UfCopyContext.copy (input false) object w
def observeCopy (w : Bool) := copied w |>.map fun pair =>
  (pair.1.scalars.memory.map (·.value),
   pair.1.scalars.bindings.map (·.writable),
   pair.1.objects.heap.allocation 2 |>.map (fun a =>
     (a.buffer.items,a.buffer.capacity,a.buffer.epoch)),
   pair.1.objects.heap.header 2 |>.map (·.writable))

#guard observeCopy true == some ([2,99,1,3,2,2,2,99],
  [false,false,false,false,true,true,true,true],some (parents,4,0),some true)
#guard observeCopy false == some ([2,99,1,3,2,2,2,99],
  [false,false,false,false,true,true,false,false],some (parents,4,0),some false)

def readonlySize (w : Bool) := copied w |>.bind fun pair =>
  match Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_size_1_2_callFuel 64 pair.1 pair.2
      [.value (.literal i32 3)] with
  | .finished (out,.scalar value) => some (out,value)
  | _ => none
#guard (readonlySize true).map Prod.snd == some 2
#guard (readonlySize false).map Prod.snd == some 2

def mutateCopy (w : Bool) := copied w |>.bind fun pair =>
  match Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_unite_callFuel 256 pair.1 pair.2
      [.value (.literal i32 0),.value (.literal i32 2)] with
  | .finished (out,.scalar value) => some (out,value)
  | _ => none

#guard (mutateCopy true).map (fun pair =>
    (pair.2,pair.1.scalars.memory.map (·.value),
      (pair.1.objects.heap.allocation 0).map (fun a => (a.buffer.items,a.buffer.capacity,a.buffer.epoch)),
      (pair.1.objects.heap.allocation 1).map (fun a => (a.buffer.items,a.buffer.capacity,a.buffer.epoch)),
      (pair.1.objects.heap.allocation 2).map (fun a => (a.buffer.items,a.buffer.capacity,a.buffer.epoch)))) ==
  some (0,[2,99,1,3,2,2,1,99],some (parents,9,5),some ([-1,-1],2,7),some ([-4,0,0,2],4,0))
#guard (mutateCopy false).isNone

example (w : Bool) : Proofs.UfCopyContext.copy (input w) object false = some (
    Proofs.UfCopyContext.exported (input w)
      (Proofs.UfCopyContext.state (project (input w) i32) data 2 99 false) data false,
    reference (project (input w) i32) 2) :=
  Proofs.UfCopyContext.copied (input w) object (receiver w) data rfl (readable w)
    (unique w) (covered w) (allocations w) false

-- Apply the general copy/getter theorem, with neither successful copy nor call assumed.
theorem headers_live (w : Bool) : Proofs.CppMoveSpace.HeadersLive (input w).objects.heap := by
  intro id h owner found owns
  rcases header w id h found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have equal : 0 = owner := Option.some.inj owns
    subst owner
    exact rfl
  · have equal : 1 = owner := Option.some.inj owns
    subst owner
    exact rfl

example (sourceWritable targetWritable : Bool) :=
  Proofs.UfCopyCounterCall.counter (input sourceWritable) object (receiver sourceWritable)
    data rfl (readable sourceWritable) (unique sourceWritable) (covered sourceWritable)
    (headers_live sourceWritable) (allocations sourceWritable) rfl
    (by change 0 ≤ _; omega) (contexts sourceWritable) targetWritable

def readonlySame (w : Bool) (a b : Int) := copied w |>.bind fun pair =>
  match Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_same_2_2_callFuel 96 pair.1 pair.2
      [.value (.literal i32 a),.value (.literal i32 b)] with
  | .finished (out,.scalar value) => some (out,value)
  | _ => none

#guard (readonlySame true 0 1).map Prod.snd == some 1
#guard (readonlySame false 0 1).map Prod.snd == some 1
#guard (readonlySame true 1 3).map Prod.snd == some 0
#guard (readonlySame false 1 3).map Prod.snd == some 0
#guard (readonlySame true 3 2).map Prod.snd == some 1
#guard (readonlySame false 3 3).map Prod.snd == some 1

-- Both query branches keep the original and other owner, as well as the copy.
def queryWorld (out : Context) :=
  (out.scalars.memory.map (·.value),
   (out.objects.heap.allocation 0).map (fun a => (a.buffer.items,a.buffer.capacity,a.buffer.epoch)),
   (out.objects.heap.allocation 1).map (fun a => (a.buffer.items,a.buffer.capacity,a.buffer.epoch)),
   (out.objects.heap.allocation 2).map (fun a => (a.buffer.items,a.buffer.capacity,a.buffer.epoch)))
def expectedWorld := (([2,99,1,3,2,2,2,99] : List Int),some (parents,9,5),some ([-1,-1],2,7),some (parents,4,0))
#guard (readonlySize true).map (fun p => queryWorld p.1) == some expectedWorld
#guard (readonlySize false).map (fun p => queryWorld p.1) == some expectedWorld
#guard (readonlySame true 1 3).map (fun p => queryWorld p.1) == some expectedWorld
#guard (readonlySame false 0 1).map (fun p => queryWorld p.1) == some expectedWorld

-- Variable arguments are evaluated in the actual exported copy context.
example (sourceWritable targetWritable : Bool) :=
  Proofs.UfCopyReadQueries.size (input sourceWritable) object (receiver sourceWritable)
    data rfl (readable sourceWritable) (unique sourceWritable) (covered sourceWritable)
    (headers_live sourceWritable) (allocations sourceWritable) rfl
    (by change 0 ≤ _; omega) (contexts sourceWritable) targetWritable
    id forest (by decide +kernel) weights 1 (by decide +kernel)
    (.variable i32 3) rfl rfl rfl

example (sourceWritable targetWritable : Bool) :=
  Proofs.UfCopyReadQueries.same (input sourceWritable) object (receiver sourceWritable)
    data rfl (readable sourceWritable) (unique sourceWritable) (covered sourceWritable)
    (headers_live sourceWritable) (allocations sourceWritable) rfl
    (by change 0 ≤ _; omega) (contexts sourceWritable) targetWritable
    id forest (by decide +kernel) 1 3 (by decide +kernel) (by decide +kernel)
    (.variable i32 3) (.variable i32 4) (by
      intro e value member
      rcases List.mem_cons.mp member with equal | member
      · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
        exact ⟨rfl,rfl,rfl⟩
      · rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
        exact ⟨rfl,rfl,rfl⟩)

end UfCopyExamples
