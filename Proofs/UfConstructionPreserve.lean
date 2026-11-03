import Proofs.CppConstructionRetire
import Proofs.UfConstructionFootprint

namespace Proofs.UfConstructionPreserve
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppRootModel
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicOwnedState
open Proofs.UfConstructionExport Proofs.CppConstructorFinish Proofs.CppConstructionRetire
open Proofs.DoublingNested (i32)

-- A well-scoped caller has no object owned by its future constructor scope.
def OldScopes (caller : NState) : Prop := ∀ owner, owner < caller.frame.state.storage.objects.length →
  caller.frame.state.forest.context owner ≠ some (caller.scope+1)

theorem construct_sized (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (scopes : OldScopes caller)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (vectorField true) (.integer i32) (fields true) = .finished (out,reference caller 2) ∧
      Initialized caller out (List.replicate n (-1)) n n ∧
      (∀ owner, owner < caller.frame.state.storage.objects.length →
        out.frame.state.storage.lookup owner = caller.frame.state.storage.lookup owner ∧
        out.frame.state.forest.lookup owner = caller.frame.state.forest.lookup owner) ∧
      out.frame.state.storage.lookup caller.frame.state.storage.objects.length =
        some ⟨caller.frame.state.storage.objects.length,List.replicate n (.integer (-1)),n,
          Proofs.CppVectorBindings.sizeLimit i32,0⟩ ∧
      out.frame.rootWritable = caller.frame.rootWritable++[true] ∧
      out.frame.bindings = caller.frame.bindings++
        [⟨caller.frame.state.storage.objects.length,.integer i32,true,.root caller.scope⟩] ∧
      out.frame.state.forest.objects.length = caller.frame.state.forest.objects.length+1 := by
  obtain ⟨init,t,prepared,ran,after,footprint⟩ := Proofs.UfConstructionFootprint.sized_from_caller
    caller heap valid models lengths en n small scalar type value
  have real : Realizes (profile caller (eraseHeap heap) (List.replicate n (-1)) n n true) t := after
  obtain ⟨out,finished,post⟩ := export_fields caller t (eraseHeap heap) (List.replicate n (-1)) n n true
    (Proofs.UfConstructionStage.nat_i32 n small) (Proofs.UfConstructionStage.nat_i32 n small) real
  have executed := construct_of_steps Proofs.UnionFindConstructionInstance.UnionFind_construct1 8
    caller init t out [.value en] (vectorField true) (.integer i32) (fields true) (reference caller 2)
    rfl prepared ran finished
  obtain ⟨snap,bound,_,flat⟩ := Proofs.UfConstructionStage.final_fields _ _ _ _ _ _ n t after
  have slot : t.vectorSlot (vectorField true) = some 0 := by
    have same := congrArg Locals.slots snap
    simp only [snapshot] at same
    simp [NState.vectorSlot,vectorField,same]
  have viewScope : (.flat i32 (caller.scope+1) (List.replicate n (-1)) : View).scope = t.scope :=
    real.scopedState.symm
  obtain ⟨frame,flags,bindings⟩ := finish_frame caller t out (vectorField true) 0 (.integer i32)
    (fields true) (reference caller 2) _ (.flat i32 (caller.scope+1) (List.replicate n (-1)))
    slot bound flat rfl viewScope finished
  have outState : out.frame.state = settled caller.frame.state i32 caller.scope n (-1) := by
    rw [frame,footprint,real.scopedState]
    rfl
  have lens := (wellFormed_parts caller.frame.state valid).1
  refine ⟨out,executed,post,?_,?_,?_,bindings,?_⟩
  · intro owner inside
    rw [outState]
    exact settled_old caller.frame.state i32 caller.scope n (-1) lens owner inside (scopes owner inside)
  · rw [outState]
    exact settled_new caller.frame.state i32 caller.scope n (-1) lens
  · rw [flags,footprint]
    rfl
  · rw [outState]
    simp [settled,State.retired,Forest.retired,Forest.transferred,
      Proofs.CppConstructionFootprint.filledState,Forest.declareRoot]

theorem construct_default (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (scopes : OldScopes caller) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (vectorField false) (.integer i32) (fields false) = .finished (out,reference caller 2) ∧
      Initialized caller out [] 0 0 ∧
      (∀ owner, owner < caller.frame.state.storage.objects.length →
        out.frame.state.storage.lookup owner = caller.frame.state.storage.lookup owner ∧
        out.frame.state.forest.lookup owner = caller.frame.state.forest.lookup owner) ∧
      out.frame.state.storage.lookup caller.frame.state.storage.objects.length =
        some (Proofs.CppNestedConstruct.flatBuffer i32 caller.frame.state.storage.objects.length) ∧
      out.frame.rootWritable = caller.frame.rootWritable++[true] ∧
      out.frame.bindings = caller.frame.bindings++
        [⟨caller.frame.state.storage.objects.length,.integer i32,true,.root caller.scope⟩] ∧
      out.frame.state.forest.objects.length = caller.frame.state.forest.objects.length+1 := by
  obtain ⟨init,t,prepared,ran,after,footprint⟩ := Proofs.UfConstructionFootprint.default_from_caller
    caller heap valid models lengths
  have real : Realizes (profile caller (eraseHeap heap) [] 0 0 false) t := after
  obtain ⟨out,finished,post⟩ := export_fields caller t (eraseHeap heap) [] 0 0 false rfl rfl real
  have executed := construct_of_steps Proofs.UnionFindConstructionInstance.UnionFind_construct0 8
    caller init t out [] (vectorField false) (.integer i32) (fields false) (reference caller 2)
    rfl prepared ran finished
  let root := caller.frame.state.storage.objects.length
  let q : Proofs.MultiVecDynamic.Parameter := ⟨0,root,.integer i32,caller.scope+1,true,true⟩
  have member : q ∈ (profile caller (eraseHeap heap) [] 0 0 false).params := by simp [profile,q,root]
  obtain ⟨h,m,family,erased⟩ := real.data.heap
  have logical : eraseHeap h root = some (.flat i32 (caller.scope+1) []) := by
    rw [erased]
    simp [profile,root,putContents]
  have model : Models t.frame.state root (.flat i32 (caller.scope+1) []) :=
    family.models root _ (Proofs.DynamicFlatSound.flat_lift h root i32 (caller.scope+1) [] logical)
  have bound := family.bindings q member
  have slot : t.vectorSlot (vectorField false) = some 0 := by
    have same := congrArg Locals.slots real.data.locals
    simp only [snapshot,profile,locals] at same
    simp [NState.vectorSlot,vectorField,same]
  obtain ⟨frame,flags,bindings⟩ := finish_frame caller t out (vectorField false) 0 (.integer i32)
    (fields false) (reference caller 2) _ (.flat i32 (caller.scope+1) []) slot bound model rfl
    real.scopedState.symm finished
  have forestEq : out.frame.state.forest = (settled caller.frame.state i32 caller.scope 0 (-1)).forest := by
    rw [frame,footprint,real.scopedState]
    rfl
  have objectsEq : out.frame.state.storage.objects =
      (settled caller.frame.state i32 caller.scope 0 (-1)).storage.objects := by
    rw [frame,footprint,real.scopedState]
    rfl
  have lens := (wellFormed_parts caller.frame.state valid).1
  refine ⟨out,executed,post,?_,?_,?_,bindings,?_⟩
  · intro owner inside
    have kept := settled_old caller.frame.state i32 caller.scope 0 (-1) lens owner inside (scopes owner inside)
    constructor
    · simpa only [Proofs.CppVectorStore.Store.lookup,objectsEq] using kept.1
    · rw [forestEq]
      exact kept.2
  · simpa only [Proofs.CppVectorStore.Store.lookup,objectsEq,Proofs.CppNestedConstruct.flatBuffer,List.replicate_zero] using
      (settled_new caller.frame.state i32 caller.scope 0 (-1) lens)
  · rw [flags,footprint]
    rfl
  · rw [forestEq]
    simp [settled,State.retired,Forest.retired,Forest.transferred,
      Proofs.CppConstructionFootprint.filledState,Forest.declareRoot]

end Proofs.UfConstructionPreserve
