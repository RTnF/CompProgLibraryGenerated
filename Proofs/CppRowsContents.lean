import Proofs.CppRowsGraph

namespace Proofs.CppRowsContents
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct
open Proofs.CppRowsGraph

-- Logical row contents are indexed by position, while storage uses the actual
-- owner ID. Both the number of rows and their individual lengths may change.
structure Data (s : State) (root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int)) : Prop where
  rows : Rows s root ty sc ids epoch
  length : values.length = ids.length
  contents : ∀ (k owner : Nat), ids[k]? = some owner →
    ∃ b, s.storage.lookup owner = some b ∧ b.items = (values[k]?.getD []).map Value.integer

theorem appendRow_data (s : State) (root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (data : Data s root ty sc ids epoch values) (old : Buffer Value)
    (found : s.storage.lookup root = some old) (room : old.items.length < old.limit) :
    ∃ r, s.appendRow root ty = some (CppAppendRow.added s root (tag ty sc ids) ty old r) ∧
      Data (CppAppendRow.added s root (tag ty sc ids) ty old r) root ty sc
        (ids ++ [s.storage.objects.length]) r.buffer.epoch (values ++ [[]]) := by
  obtain ⟨r,run,rows⟩ := appendRow_rows s root ty sc ids epoch data.rows old found room
  refine ⟨r,run,rows,by simp [data.length],?_⟩
  intro k owner lookup
  have bound : k < (ids ++ [s.storage.objects.length]).length :=
    (List.getElem?_eq_some_iff.mp lookup).1
  by_cases inside : k < ids.length
  · have previous : ids[k]? = some owner := by
      simpa [List.getElem?_append_left inside] using lookup
    obtain ⟨b,hb,hi⟩ := data.contents k owner previous
    obtain ⟨rb,ro,rf,earlier⟩ := row_object (⟨s,[],[]⟩ : Frame) root ty sc ids epoch k owner data.rows previous
    have stored : owner < s.storage.objects.length := CppVectorStore.lookup_bound s.storage owner b hb
    refine ⟨b,(CppAppendRow.storage_old s root (tag ty sc ids) ty old r owner stored (by omega)).trans hb,?_⟩
    have vi : k < values.length := by rw [data.length]; exact inside
    simpa [List.getElem?_append_left vi] using hi
  · have last : k = ids.length := by simp only [List.length_append,List.length_singleton] at bound; omega
    subst k
    have fresh : owner = s.storage.objects.length := by
      simpa using lookup.symm
    subst owner
    refine ⟨rowBuffer ty s.storage.objects.length,CppAppendRow.storage_fresh s root (tag ty sc ids) ty old r,?_⟩
    simp [← data.length,rowBuffer]

theorem updated_data (f : Frame) (root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (data : Data f.state root ty sc ids epoch values) (k owner : Nat)
    (lookup : ids[k]? = some owner) (old : Buffer Value) (result : Result Value Unit)
    (newValues : List Int) (items : result.buffer.items = newValues.map Value.integer)
    (valid : (f.updated owner old result).state.wellFormed = true) :
    Data (f.updated owner old result).state root ty sc ids epoch (values.set k newValues) := by
  obtain ⟨b,object,found,earlier⟩ := row_object f root ty sc ids epoch k owner data.rows lookup
  have bound : k < ids.length := (List.getElem?_eq_some_iff.mp lookup).1
  have vbound : k < values.length := by rw [data.length]; exact bound
  have nodup : ids.Nodup :=
    (CppVectorOwnership.wellFormed_tag f.state.forest root (tag ty sc ids)
      (wellFormed_parts f.state data.rows.valid).2.1 data.rows.rootTag).2.1
  refine ⟨updated_rows f root owner ty sc ids epoch old result data.rows (by omega) valid,
    by simpa using data.length,?_⟩
  intro j other otherLookup
  by_cases same : j = k
  · subst j
    have equal : other = owner := Option.some.inj (otherLookup.symm.trans lookup)
    subst other
    refine ⟨result.buffer,CppNestedOps.updated_lookup_self f owner old result
      (CppVectorStore.lookup_bound f.state.storage owner b found),?_⟩
    simpa [List.getElem?_set_self vbound] using items
  · have distinct : owner ≠ other := by
      intro equal
      have positions : k = j := (nodup.getElem?_inj bound).mp (by rw [lookup,otherLookup,equal])
      exact same positions.symm
    obtain ⟨before,hb,hi⟩ := data.contents j other otherLookup
    refine ⟨before,(CppNestedOps.updated_lookup_other f owner other old result distinct).trans hb,?_⟩
    simpa [List.getElem?_set_ne (Ne.symm same)] using hi

end Proofs.CppRowsContents
