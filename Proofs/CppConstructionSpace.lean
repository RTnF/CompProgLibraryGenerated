import Proofs.CppConstructorPeak

namespace Proofs.CppConstructionSpace
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppVectorStore Proofs.CppNestedVectorStore
open Proofs.CppNestedConstruct Proofs.CppConstructionFootprint

-- The appended root's capacity and one root header are the only new resident
-- storage. Scope changes do not change this accounting.
theorem appended_root_live (s t : State) (ty : Ty) (scope : Nat) (buffer : Proofs.CppVector.Buffer Value)
    (lengths : s.forest.objects.length = s.storage.objects.length)
    (forest : t.forest = s.forest.declareRoot ty scope)
    (objects : t.storage.objects = s.storage.objects++[some buffer]) :
    t.liveSpace = s.liveSpace+buffer.capacity+1 := by
  have oldNode (owner : Nat) (inside : owner < s.storage.objects.length) : t.nodeSpace owner = s.nodeSpace owner := by
    have oldTag := declareRoot_old s.forest ty scope owner (by omega)
    simp only [State.nodeSpace,forest,oldTag]
    have oldBuffer : t.storage.lookup owner = s.storage.lookup owner := by
      simp [Store.lookup,objects,List.getElem?_append_left inside]
    rw [oldBuffer]
  have newNode : t.nodeSpace s.storage.objects.length = buffer.capacity+1 := by
    have tag := declareRoot_new s.forest ty scope
    rw [lengths] at tag
    simp [State.nodeSpace,forest,tag,Store.lookup,objects,flatTag]
  have oldSum : ((List.range s.storage.objects.length).map t.nodeSpace).sum = s.liveSpace := by
    unfold State.liveSpace
    congr 1
    apply List.map_congr_left
    intro owner member
    exact oldNode owner (List.mem_range.mp member)
  unfold State.liveSpace
  rw [objects,List.length_append,List.length_singleton,List.range_succ,List.map_append,List.sum_append]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,oldSum,newNode]
  change s.liveSpace+(buffer.capacity+1) = s.liveSpace+buffer.capacity+1
  omega

theorem filled_live (s : State) (ty : Ty) (scope count : Nat) (x : Int)
    (lengths : s.forest.objects.length = s.storage.objects.length) :
    (filledState s ty scope count x).liveSpace = s.liveSpace+count+1 := by
  exact appended_root_live s (filledState s ty scope count x) ty scope
    ⟨s.storage.objects.length,List.replicate count (.integer x),count,Proofs.CppVectorBindings.sizeLimit ty,0⟩ lengths rfl rfl

theorem empty_live (s : State) (ty : Ty) (scope : Nat)
    (lengths : s.forest.objects.length = s.storage.objects.length) :
    (emptyState s ty scope).liveSpace = s.liveSpace+1 := by
  have result := appended_root_live s (emptyState s ty scope) ty scope
    (flatBuffer ty s.storage.objects.length) lengths rfl rfl
  simpa [flatBuffer] using result

open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppConstructorFinish
theorem finish_live (caller callee out : NState) (vslot : Nat) (element : Element)
    (fields : List ScalarField) (values : List ScalarValue) (object : ObjectRef)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (captured : captureAll callee fields = some values)
    (actual : Proofs.CppConstructorFinish.finish caller callee vslot element fields = some (out,object)) :
    Proofs.CppNestedEval.liveS out = Proofs.CppNestedEval.liveS caller+2*values.length := by
  unfold Proofs.CppConstructorFinish.finish at actual
  split at actual
  · rename_i guarded
    obtain ⟨index,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
    obtain ⟨binding,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    split at rest
    · obtain ⟨actualValues,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
      have valuesEq : actualValues = values := Option.some.inj (found.symm.trans captured)
      subst actualValues
      obtain ⟨moved,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
      obtain ⟨retired,_,same⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
      have eq := (Prod.mk.inj (Option.some.inj same)).1
      subst out
      exact Proofs.CppConstructorPeak.restored_live caller callee retired binding values guarded.2.1 baseline
    · simp at rest
  · simp at actual

end Proofs.CppConstructionSpace
