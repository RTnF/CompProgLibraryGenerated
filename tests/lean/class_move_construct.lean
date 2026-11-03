namespace ClassMoveConstructExamples
open Proofs.CppClassMoveConstruct Proofs.CppMoveContext Proofs.CppConstructorFinish
open Proofs.CppMoveHeaders Proofs.CppNestedProgram Proofs.DoublingNested
abbrev limit := Proofs.CppVectorBindings.sizeLimit i32

def input : Context := ⟨⟨⟨[some ⟨some 0,0,true,limit⟩],
  [some ⟨⟨0,[-2,0,-1],8,limit,5⟩,fun _ => 0⟩],[⟨⟨⟨0,5,1⟩,0⟩,true⟩],0,0,0⟩,[⟨0,true⟩]⟩,
  ⟨[⟨i32,2⟩,⟨i32,3⟩],[⟨0,true⟩,⟨1,true⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1],0,0⟩
def source : ObjectRef := ⟨0,[1,2]⟩
def moved (tc : Bool) := Proofs.CachedMoveConstruct.construct input source tc
#guard (moved false).map (fun p => (p.2,p.1.scalars.memory.map (·.value),work p.1)) ==
  some (⟨3,[4,5]⟩,[2,3,2,3],4)
#guard (moved true).map (fun p => p.1.scalars.bindings.map (·.writable)) ==
  some [true,true,false,false]
#guard (moved true).bind (fun p => p.1.objects.heap.header 0) == some ⟨none,0,true,limit⟩
#guard (moved true).bind (fun p => p.1.objects.heap.header 1) == some ⟨some 0,0,false,limit⟩
#guard (moved false).bind (fun p => p.1.objects.heap.header 1) == some ⟨some 0,0,true,limit⟩
#guard (moved true).bind (fun p => (p.1.objects.heap.allocation 0).map
  (fun a => (a.buffer.items,a.buffer.capacity,a.buffer.epoch))) == some ([-2,0,-1],8,5)
#guard (moved true).bind (fun p => Proofs.CppMoveHeaders.read p.1.objects.heap i32.valid 0) == some 0
#guard (moved true).map (fun p => p.1.objects.heap.grants) == some input.objects.heap.grants
#guard (Proofs.CachedMoveConstruct.construct {input with
  objects := {input.objects with views := [⟨0,false⟩]}} source false).isNone

example (tc : Bool) : Proofs.CachedMoveConstruct.profileFor tc =
    (⟨i32,!tc,[(i32,!tc),(i32,!tc)]⟩ : Proofs.CppClassCopy.Profile) := by
  cases tc <;> rfl

theorem scalar_ready (tc : Bool) : ScalarReady (project input i32) source.scalarSlots
    (Proofs.CachedMoveConstruct.profileFor tc).scalarFields := by
  refine ⟨rfl,?_⟩
  intro slot field member
  rcases List.mem_cons.mp member with equal | member
  · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
    exact ⟨⟨0,true⟩,⟨i32,2⟩,rfl⟩
  · rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨⟨1,true⟩,⟨i32,3⟩,rfl⟩

example (tc : Bool) := construct_ready input source (Proofs.CachedMoveConstruct.profileFor tc)
  0 ⟨0,true⟩ ⟨some 0,0,true,limit⟩ rfl rfl rfl (by exact (by decide +kernel :
    Proofs.CppMoveHeaders.readable input.objects.heap ⟨some 0,0,true,limit⟩ i32.valid = true)) (scalar_ready tc)

def empty : Context := {input with
  objects := ⟨⟨[some ⟨none,0,true,limit⟩],[],[],0,0,0⟩,[⟨0,true⟩]⟩,
  scalars := {input.scalars with memory := [⟨i32,1⟩,⟨i32,4⟩]}}
#guard (Proofs.CachedMoveConstruct.construct empty source true).map
  (fun p => (p.1.scalars.memory.map (·.value),p.1.objects.heap.allocations.length)) ==
    some ([1,4,1,4],0)
def vectorMoved (tc : Bool) := (Proofs.CppMoveViews.construct input.objects i32.valid 0 input.scope (!tc)).getD (input.objects,0)

def newReceiver (tc : Bool) := receiverTwo input (vectorMoved tc).1 (vectorMoved tc).2 i32 2 3 (!tc) (!tc)
  (by decide +kernel) (by decide +kernel) ⟨1,!tc⟩ ⟨some 0,0,!tc,limit⟩ (by cases tc <;> rfl)

example (tc : Bool) : moved tc = some
    (finish input (vectorMoved tc).1 (vectorMoved tc).2 [(⟨i32,2⟩,!tc),(⟨i32,3⟩,!tc)],
      reference (project input i32) 2) := by cases tc <;> rfl

example (out : Context) (target : ObjectRef) (tc : Bool)
    (actual : Proofs.CachedMoveConstruct.construct input source tc = some (out,target)) :=
  construct_storage input out source target (Proofs.CachedMoveConstruct.profileFor tc) actual
example (out : Context) (target : ObjectRef) (tc : Bool)
    (actual : Proofs.CachedMoveConstruct.construct input source tc = some (out,target)) :=
  construct_resources input out source target (Proofs.CachedMoveConstruct.profileFor tc) actual

def oldCounter : Proofs.CppMoveObjectReceiver.Field input i32 :=
  ⟨1,0,0,true,2,rfl,rfl,rfl,by decide +kernel⟩
def oldSize : Proofs.CppMoveObjectReceiver.Field input i32 :=
  ⟨2,1,1,true,3,rfl,rfl,rfl,by decide +kernel⟩
def sourceReceiver (tc : Bool) : Proofs.CppMoveReadReceiver.ReadReceiver
    (finish input (vectorMoved tc).1 (vectorMoved tc).2 [(⟨i32,2⟩,!tc),(⟨i32,3⟩,!tc)]) source i32 :=
  ⟨oldField input _ _ _ i32 oldCounter,oldField input _ _ _ i32 oldSize,rfl,
    0,⟨0,true⟩,⟨none,0,true,limit⟩,rfl,by cases tc <;> rfl⟩
example (tc : Bool) : (newReceiver tc).counter.value = 2 ∧ (newReceiver tc).size.value = 3 ∧
    (sourceReceiver tc).counter.value = 2 ∧ (sourceReceiver tc).size.value = 3 := ⟨rfl,rfl,rfl,rfl⟩
#guard (constructClass input ⟨0,[1,999]⟩ (Proofs.CachedMoveConstruct.profileFor false)).isNone
#guard (constructClass input ⟨999,[1,2]⟩ (Proofs.CachedMoveConstruct.profileFor false)).isNone

def getter (tc target : Bool) := moved tc |>.bind fun p =>
  match Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_2_callFuel 8 p.1
      (if target then p.2 else source) [] with
  | .finished (_, .scalar value) => some value
  | _ => none
#guard getter false false == some 2
#guard getter false true == some 2
#guard getter true false == some 2
#guard getter true true == some 2

end ClassMoveConstructExamples
