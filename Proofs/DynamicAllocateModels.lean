import Proofs.DynamicOwnedScope

namespace Proofs.DynamicAllocateModels
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppVectorStore Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct Proofs.CppRowsFrame Proofs.CppRootModel Proofs.CppRowsContents

-- Allocation appends objects. Existing rows may have arbitrary IDs/epochs.
theorem prefix_model {s t : State} {root : Nat} {v : View} (model : Models s root v)
    (valid : t.wellFormed = true)
    (tags : ∀ owner, owner < s.forest.objects.length → t.forest.lookup owner = s.forest.lookup owner)
    (buffers : ∀ owner, owner < s.storage.objects.length → t.storage.lookup owner = s.storage.lookup owner) : Models t root v := by
  have bound := model.bound
  have lengths := (wellFormed_parts s model.valid).1
  cases v with
  | flat ty sc vs =>
    refine ⟨valid,?_,?_⟩
    · rw [tags root (by omega)]; exact model.tag
    · obtain ⟨b,found,items⟩ := model.buffer
      exact ⟨b,by rw [buffers root bound]; exact found,items⟩
  | rows ty sc ids epoch vs =>
    refine ⟨⟨valid,?_,?_⟩,model.length,?_⟩
    · rw [tags root (by omega)]; exact model.rows.rootTag
    · obtain ⟨b,found,he,items⟩ := model.rows.buffer
      exact ⟨b,by rw [buffers root bound]; exact found,he,items⟩
    · intro k owner lookup
      obtain ⟨b,found,items⟩ := model.contents k owner lookup
      exact ⟨b,by rw [buffers owner (lookup_bound s.storage owner b found)]; exact found,items⟩

theorem rows_old (s next : State) (ty : Ty) (scope count : Nat)
    (run : s.constructRows ty scope count = some next) (root : Nat) (v : View) (model : Models s root v) : Models next root v := by
  apply prefix_model model (constructRows_state_wellFormed s ty scope count next run)
  · intro owner bound
    rw [constructRows_forest s ty scope count next run]
    exact constructRows_old s.forest ty scope count owner bound
  · intro owner bound; exact constructRows_storage_old s ty scope count owner next run bound

theorem empty_old (s next : State) (ty : Ty) (scope : Nat)
    (run : s.declareVector ty scope = some next) (root : Nat) (v : View) (model : Models s root v) : Models next root v := by
  apply prefix_model model (declareVector_wellFormed s ty scope next run)
  · intro owner bound
    rw [declareVector_forest s ty scope next run]
    exact declareRoot_old s.forest ty scope owner bound
  · intro owner bound; exact declareVector_storage_old s ty scope owner next run bound

theorem filled_old (s next : State) (ty : Ty) (scope count : Nat) (value : Int)
    (run : s.fillVector ty scope count value = some next) (root : Nat) (v : View) (model : Models s root v) : Models next root v := by
  apply prefix_model model (fillVector_wellFormed s ty scope count value next run)
  · intro owner bound
    rw [fillVector_forest s ty scope count value next run]
    exact declareRoot_old s.forest ty scope owner bound
  · intro owner bound; exact fillVector_storage_old s ty scope count value owner next run bound

theorem rows_new (s next : State) (ty : Ty) (scope count : Nat)
    (run : s.constructRows ty scope count = some next) :
    Models next s.storage.objects.length (.rows ty scope (rowIds s.storage.objects.length count) 0 (List.replicate count [])) := by
  have valid := constructRows_state_wellFormed s ty scope count next run
  have oldValid := (constructRows_inv s ty scope count next run).1
  have lengths := (wellFormed_parts s oldValid).1
  refine ⟨⟨valid,?_,rootBuffer s.storage.objects.length count,constructRows_storage_root s ty scope count next run,rfl,rfl⟩,?_,?_⟩
  · rw [constructRows_forest s ty scope count next run,← lengths,constructRows_root]
    rfl
  · simp [rowIds]
  · intro k owner lookup
    have bound : k < count := by have h := (List.getElem?_eq_some_iff.mp lookup).1; simpa [rowIds] using h
    have same : owner = s.storage.objects.length+1+k := by
      have expected := Proofs.CppNestedRows.rowIds_get s.storage.objects.length count k bound
      exact Option.some.inj (lookup.symm.trans expected)
    subst owner
    refine ⟨rowBuffer ty (s.storage.objects.length+1+k),constructRows_storage_row s ty scope count k next run bound,?_⟩
    simp [rowBuffer,List.getElem?_replicate,bound]

theorem empty_new (s next : State) (ty : Ty) (scope : Nat) (run : s.declareVector ty scope = some next) :
    Models next s.storage.objects.length (.flat ty scope []) := by
  have lengths := (wellFormed_parts s (declareVector_inv s ty scope next run).1).1
  refine ⟨declareVector_wellFormed s ty scope next run,?_,flatBuffer ty s.storage.objects.length,declareVector_storage_new s ty scope next run,rfl⟩
  rw [declareVector_forest s ty scope next run,← lengths,declareRoot_new]
  rfl

theorem filled_new (s next : State) (ty : Ty) (scope count : Nat) (value : Int)
    (run : s.fillVector ty scope count value = some next) :
    Models next s.storage.objects.length (.flat ty scope (List.replicate count value)) := by
  have lengths := (wellFormed_parts s (fillVector_inv s ty scope count value next run).1).1
  refine ⟨fillVector_wellFormed s ty scope count value next run,?_,_,fillVector_storage_new s ty scope count value next run,?_⟩
  · rw [fillVector_forest s ty scope count value next run,← lengths,declareRoot_new]
    rfl
  · simp

end Proofs.DynamicAllocateModels
