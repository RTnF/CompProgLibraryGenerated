import Proofs.CppConstructorFinish
import Proofs.UfConstructionPrepare

namespace Proofs.UfConstructionExport
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.DoublingNested Proofs.DoublingCall
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState Proofs.MultiVecDynamic
open Proofs.CppRootModel Proofs.CppNestedVectorBindings Proofs.CppConstructorFinish
open Proofs.CppState (Cell)

def fields (hasArgument : Bool) : List ScalarField :=
  if hasArgument then [⟨2,i32⟩,⟨3,i32⟩] else [⟨1,i32⟩,⟨2,i32⟩]

def vectorField (hasArgument : Bool) : Nat := if hasArgument then 1 else 0

def cells (hasArgument : Bool) (count n : Int) : List Cell :=
  if hasArgument then [⟨i32,n⟩,⟨i32,count⟩,⟨i32,n⟩] else [⟨i32,count⟩,⟨i32,n⟩]

def locals (hasArgument : Bool) (P : List Cell) (count n : Int) : Locals :=
  if hasArgument then
    ⟨P++cells true count n,[⟨P.length,true⟩,⟨P.length+1,true⟩,⟨P.length+2,true⟩],
      [.scalar 0,.vector 0,.scalar 1,.scalar 2]⟩
  else ⟨P++cells false count n,[⟨P.length,true⟩,⟨P.length+1,true⟩],[.vector 0,.scalar 0,.scalar 1]⟩

def profile (caller : NState) (h : ContentsHeap) (vec : List Int) (count n : Int) (hasArgument : Bool) : State :=
  ⟨⟨locals hasArgument (callerP caller) count n,
      putContents h caller.frame.state.storage.objects.length (.flat i32 (caller.scope+1) vec)⟩,
    [⟨0,caller.frame.state.storage.objects.length,.integer i32,caller.scope+1,true,true⟩],
    caller.frame.state.storage.objects.length+1,1,caller.scope+1⟩

def payload (count n : Int) : List ScalarValue := [(⟨i32,count⟩,true),(⟨i32,n⟩,true)]

theorem fields_match (s : NState) (P : List Cell) (count n : Int) (hasArgument : Bool)
    (cv : i32.valid count = true) (nv : i32.valid n = true)
    (shape : snapshot s = locals hasArgument P count n) :
    FieldsMatch s (fields hasArgument) (payload count n) := by
  have mem := congrArg Locals.memory shape
  have binds := congrArg Locals.bindings shape
  have slots := congrArg Locals.slots shape
  cases hasArgument <;>
    simp [locals,cells,snapshot] at mem binds slots <;>
    simp [FieldsMatch,fields,payload,NState.scalarCell,NState.scalarSlot,mem,binds,slots,
      cv,nv,List.getElem?_append_right]

theorem export_fields (caller callee : NState) (h : ContentsHeap) (vec : List Int) (count n : Int)
    (hasArgument : Bool) (cv : i32.valid count = true) (nv : i32.valid n = true)
    (real : Realizes (profile caller h vec count n hasArgument) callee) :
    ∃ out, finish caller callee (vectorField hasArgument) (.integer i32) (fields hasArgument) =
        some (out,reference caller 2) ∧
      Models out.frame.state caller.frame.state.storage.objects.length (.flat i32 caller.scope vec) ∧
      out.scalars.memory = caller.scalars.memory ++ [⟨i32,count⟩,⟨i32,n⟩] ∧
      out.scalarCell (caller.slots.length+1) i32 = some (⟨caller.scalars.memory.length,true⟩,⟨i32,count⟩) ∧
      out.scalarCell (caller.slots.length+2) i32 = some (⟨caller.scalars.memory.length+1,true⟩,⟨i32,n⟩) ∧
      out.vectorSlot caller.slots.length = some caller.frame.bindings.length ∧
      out.frame.bindings[caller.frame.bindings.length]? =
        some ⟨caller.frame.state.storage.objects.length,.integer i32,true,.root caller.scope⟩ ∧
      out.frame.rootWritable[caller.frame.state.storage.objects.length]? = some true ∧ out.scope = caller.scope := by
  obtain ⟨heap,m,family,erased⟩ := real.data.heap
  let root := caller.frame.state.storage.objects.length
  let b : Binding := ⟨root,.integer i32,true,.root (caller.scope+1)⟩
  let view : View := .flat i32 (caller.scope+1) vec
  have member : (⟨0,root,.integer i32,caller.scope+1,true,true⟩ : Parameter) ∈
      (profile caller h vec count n hasArgument).params := by simp [profile,root]
  have bound : callee.frame.bindings[0]? = some b := family.bindings _ member
  have logical : eraseHeap heap root = some (.flat i32 (caller.scope+1) vec) := by
    rw [erased]
    simp [profile,root,putContents]
  have lifted := Proofs.DynamicFlatSound.flat_lift heap root i32 (caller.scope+1) vec logical
  have model : Models callee.frame.state root view := family.models root _ lifted
  have shape : snapshot callee = locals hasArgument (callerP caller) count n := real.data.locals
  have mem : callee.scalars.memory = callerP caller ++ cells hasArgument count n := by
    have same := congrArg Locals.memory shape
    cases hasArgument <;> simpa [snapshot,locals] using same
  have taken : callee.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [mem]
    exact Proofs.UfRootCall.take_P caller _
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    rw [mem]
    simp [callerP]
  have slot : callee.vectorSlot (vectorField hasArgument) = some 0 := by
    have same := congrArg Locals.slots shape
    cases hasArgument <;> simp [snapshot,locals] at same <;> simp [NState.vectorSlot,vectorField,same]
  have scopeEq : callee.scope = caller.scope+1 := real.scopedState
  have matched := fields_match callee (callerP caller) count n hasArgument cv nv shape
  obtain ⟨out,finished,outEq,kept,memory,bindings,slots,scope⟩ := finish_ok caller callee
    (vectorField hasArgument) 0 (.integer i32) (fields hasArgument) (payload count n) b view
    scopeEq fits (by rw [taken]) slot bound rfl (by rw [scopeEq]) matched model rfl scopeEq.symm
  let exportedFrame := Proofs.DynamicRetire.retiredFrame
    (Proofs.DynamicTransfer.movedFrame callee.frame b.owner caller.scope view) callee.scope
  have counter := restored_scalar caller callee exportedFrame b (payload count n) 0 ⟨i32,count⟩ true fits rfl cv
  have size := restored_scalar caller callee exportedFrame b (payload count n) 1 ⟨i32,n⟩ true fits rfl nv
  have vector := restored_vector caller callee exportedFrame b (payload count n)
  refine ⟨out,finished,kept,?_,?_,?_,?_,?_,?_,scope⟩
  · rw [memory,taken]
    rfl
  · rw [outEq]
    simpa using counter
  · rw [outEq]
    simpa [Nat.add_assoc] using size
  · rw [outEq]
    exact vector.1
  · rw [outEq]
    exact vector.2
  · rw [outEq]
    exact family.flags _ member


def Initialized (caller out : NState) (vec : List Int) (count n : Int) : Prop :=
  Models out.frame.state caller.frame.state.storage.objects.length (.flat i32 caller.scope vec) ∧
  out.scalars.memory = caller.scalars.memory ++ [⟨i32,count⟩,⟨i32,n⟩] ∧
  out.scalarCell (caller.slots.length+1) i32 = some (⟨caller.scalars.memory.length,true⟩,⟨i32,count⟩) ∧
  out.scalarCell (caller.slots.length+2) i32 = some (⟨caller.scalars.memory.length+1,true⟩,⟨i32,n⟩) ∧
  out.vectorSlot caller.slots.length = some caller.frame.bindings.length ∧
  out.frame.bindings[caller.frame.bindings.length]? =
    some ⟨caller.frame.state.storage.objects.length,.integer i32,true,.root caller.scope⟩ ∧
  out.frame.rootWritable[caller.frame.state.storage.objects.length]? = some true ∧ out.scope = caller.scope

theorem sized_layout : Proofs.UnionFindConstructionInstance.UnionFind_construct1_fields.map Prod.snd =
    vectorField true :: (fields true).map ScalarField.slot ∧
    Proofs.UnionFindConstructionInstance.UnionFind_construct1_fields.map Prod.fst = ["_ps","_num_groups","_n"] := ⟨rfl,rfl⟩

theorem default_layout : Proofs.UnionFindConstructionInstance.UnionFind_construct0_fields.map Prod.snd =
    vectorField false :: (fields false).map ScalarField.slot ∧
    Proofs.UnionFindConstructionInstance.UnionFind_construct0_fields.map Prod.fst = ["_ps","_num_groups","_n"] := ⟨rfl,rfl⟩

theorem construct_sized (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (vectorField true) (.integer i32) (fields true) = .finished (out,reference caller 2) ∧
      Initialized caller out (List.replicate n (-1)) n n ∧
      Proofs.UfClassInvariant.Valid (List.replicate n (-1)) n (fun _ => 0) := by
  obtain ⟨init,step,prepared,ran,after,ret,br,invariant,base,work⟩ :=
    Proofs.UfConstructionPrepare.sized_from_caller caller heap valid models lengths en n small scalar type value
  have real : Realizes (profile caller (eraseHeap heap) (List.replicate n (-1)) n n true) step.state := after
  obtain ⟨out,finished,post⟩ := export_fields caller step.state (eraseHeap heap) (List.replicate n (-1)) n n true
    (Proofs.UfConstructionStage.nat_i32 n small) (Proofs.UfConstructionStage.nat_i32 n small) real
  have stepEq : step = ⟨step.state,none,false⟩ := by cases step; simp_all
  have executed := construct_of_steps Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    caller init step.state out [.value en] (vectorField true) (.integer i32) (fields true) (reference caller 2)
    rfl prepared (ran.trans (congrArg Proofs.CppLoop.Outcome.finished stepEq)) finished
  exact ⟨out,executed,post,invariant⟩

theorem construct_default (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (vectorField false) (.integer i32) (fields false) = .finished (out,reference caller 2) ∧
      Initialized caller out [] 0 0 ∧ Proofs.UfClassInvariant.Valid [] 0 (fun _ => 0) := by
  obtain ⟨init,step,prepared,ran,after,ret,br,invariant,base,work⟩ :=
    Proofs.UfConstructionPrepare.default_from_caller caller heap valid models lengths
  have real : Realizes (profile caller (eraseHeap heap) [] 0 0 false) step.state := after
  obtain ⟨out,finished,post⟩ := export_fields caller step.state (eraseHeap heap) [] 0 0 false rfl rfl real
  have stepEq : step = ⟨step.state,none,false⟩ := by cases step; simp_all
  have executed := construct_of_steps Proofs.UnionFindConstructionInstance.UnionFind_construct0 8
    caller init step.state out [] (vectorField false) (.integer i32) (fields false) (reference caller 2)
    rfl prepared (ran.trans (congrArg Proofs.CppLoop.Outcome.finished stepEq)) finished
  exact ⟨out,executed,post,invariant⟩

end Proofs.UfConstructionExport
