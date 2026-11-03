import Proofs.CppMoveAppendOwned
import Proofs.CppMoveRestore

namespace Proofs.CppMoveFrameScopes
open Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveSpace Proofs.CppMoveRestore
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore

def HeaderScopes (s : Heap Int) (upper : Nat) : Prop :=
  ∀ id header, s.header id = some header → header.scope ≤ upper

theorem headers_of_contexts (s : Proofs.CppMoveViews.State Int) (ty : Proofs.CppScalar.Ty) (upper : Nat)
    (unique : Unique s.heap) (covered : OwnsAll s.heap) (live : HeadersLive s.heap)
    (contexts : ∀ owner sc, (materialize s ty).frame.state.forest.context owner = some sc → sc ≤ upper) :
    HeaderScopes s.heap upper := by
  intro id header found
  cases owns : header.allocation with
  | none =>
    have entry := entries_empty s.heap ty id header found owns
    have tag := (materialize_entry s ty _ _ _ entry).2
    exact contexts _ header.scope (context_of_root _ _ _ tag rfl)
  | some owner =>
    have present := live id header owner found owns
    cases allocation : s.heap.allocation owner with
    | none => simp [allocation] at present
    | some tracked =>
      have ownerHeader := ownerHeader_unique s.heap owner id header unique found owns
        (ownerHeader_exists s.heap owner tracked covered allocation)
      have entry := entries_allocation s.heap ty owner tracked header allocation ownerHeader
      have tag := (materialize_entry s ty _ _ _ entry).2
      exact contexts _ header.scope (context_of_root _ _ _ tag rfl)

theorem entry_root (s : Heap Int) (ty : Proofs.CppScalar.Ty) (owner : Nat)
    (buffer : Proofs.CppVector.Buffer Value) (tag : Tag)
    (found : (entries s ty)[owner]? = some (some (buffer,tag))) :
    ∃ id header, s.header id = some header ∧ tag = ⟨.integer ty,none,some header.scope,[]⟩ := by
  unfold entries at found
  by_cases inside : owner < s.allocations.length
  · rw [List.getElem?_append_left (by simpa using inside)] at found
    simp only [List.getElem?_mapIdx] at found
    cases slot : s.allocations[owner]? with
    | none => simp [slot] at found
    | some entry =>
      cases entry with
      | none => simp [slot] at found
      | some tracked =>
        cases hf : ownerHeader s owner with
        | none => simp [slot,hf] at found
        | some header =>
          simp only [slot,Option.map_some,Bind.bind,Option.bind,hf] at found
          have same := Prod.mk.inj (Option.some.inj (Option.some.inj found))
          obtain ⟨id,headerFound,owns⟩ := ownerHeader_parts s owner header hf
          exact ⟨id,header,headerFound,same.2.symm⟩
  · rw [List.getElem?_append_right (by simpa using (Nat.le_of_not_gt inside))] at found
    simp only [List.length_mapIdx,List.getElem?_mapIdx] at found
    cases slot : s.headers[owner-s.allocations.length]? with
    | none => simp [slot] at found
    | some entry =>
      cases entry with
      | none => simp [slot] at found
      | some header =>
        cases owns : header.allocation with
        | some allocation => simp [slot,owns] at found
        | none =>
          simp only [slot,Option.map_some,Bind.bind,Option.bind,owns,ite_true] at found
          have same := Prod.mk.inj (Option.some.inj (Option.some.inj found))
          exact ⟨owner-s.allocations.length,header,by simp [Heap.header,slot],same.2.symm⟩

theorem materialize_root (s : Proofs.CppMoveViews.State Int) (ty : Proofs.CppScalar.Ty) (owner : Nat) (tag : Tag)
    (found : (materialize s ty).frame.state.forest.lookup owner = some tag) :
    ∃ id header, s.heap.header id = some header ∧ tag = ⟨.integer ty,none,some header.scope,[]⟩ := by
  cases entry : (entries s.heap ty)[owner]? with
  | none => simp [materialize,Forest.lookup,List.getElem?_map,entry] at found
  | some value =>
    cases value with
    | none => simp [materialize,Forest.lookup,List.getElem?_map,entry] at found
    | some pair =>
      rcases pair with ⟨buffer,actualTag⟩
      have equal : actualTag = tag := by
        simpa [materialize,Forest.lookup,List.getElem?_map,entry] using found
      subst actualTag
      exact entry_root s.heap ty owner buffer tag entry

theorem contexts_of_headers (s : Proofs.CppMoveViews.State Int) (ty : Proofs.CppScalar.Ty) (upper : Nat)
    (headers : HeaderScopes s.heap upper) :
    ∀ owner sc, (materialize s ty).frame.state.forest.context owner = some sc → sc ≤ upper := by
  intro owner sc context
  cases found : (materialize s ty).frame.state.forest.lookup owner with
  | none =>
    rw [context_of_none _ _ found] at context
    contradiction
  | some tag =>
    obtain ⟨id,header,headerFound,tagEq⟩ := materialize_root s ty owner tag found
    have root : tag.parent = none := by rw [tagEq]
    have contextEq := context_of_root _ _ _ found root
    rw [tagEq] at contextEq
    have equal : header.scope = sc := Option.some.inj (contextEq.symm.trans context)
    rw [← equal]
    exact headers id header headerFound

theorem appended_scopes (s : Heap Int) (buffer : Proofs.CppVector.Buffer Int) (scope upper : Nat) (writable : Bool)
    (headers : HeaderScopes s upper) (newScope : scope ≤ upper) :
    HeaderScopes (Proofs.CppMoveAppendOwned.appended s buffer scope writable) upper := by
  intro id header found
  rw [Proofs.CppMoveAppendOwned.header_lookup] at found
  by_cases fresh : id = s.headers.length
  · rw [ite_eq_left fresh] at found
    cases Option.some.inj found
    exact newScope
  · rw [ite_eq_right fresh] at found
    exact headers id header found

end Proofs.CppMoveFrameScopes
