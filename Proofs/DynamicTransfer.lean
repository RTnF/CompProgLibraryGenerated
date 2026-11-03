import Proofs.DynamicFlatAppend
import Proofs.DynamicOwnedCleanup

namespace Proofs.DynamicTransfer
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.CppRowsGraph Proofs.MultiVecDynamic
open Proofs.DynamicExpr Proofs.DynamicContents

def tagOf : View → Tag
  | .flat ty sc _ => ⟨.integer ty,none,some sc,[]⟩
  | .rows ty sc ids _ _ => CppRowsGraph.tag ty sc ids

def inScope (v : View) (scope : Nat) : View := match v with
  | .flat ty _ vs => .flat ty scope vs
  | .rows ty _ ids epoch vs => .rows ty scope ids epoch vs

def contentsInScope (v : Contents) (scope : Nat) : Contents := match v with
  | .flat ty _ vs => .flat ty scope vs
  | .rows ty _ vs => .rows ty scope vs

def moveHeap (h : Heap) (root scope : Nat) : Heap := fun owner =>
  if owner = root then (h owner).map (fun v => inScope v scope) else h owner

def moveContents (h : ContentsHeap) (root scope : Nat) : ContentsHeap := fun owner =>
  if owner = root then (h owner).map (fun v => contentsInScope v scope) else h owner

def movedFrame (f : Frame) (root scope : Nat) (v : View) : Frame :=
  {f with state := {f.state with forest := f.state.forest.transferred root scope (tagOf v)}}

theorem erase_move (h : Heap) (root scope : Nat) : eraseHeap (moveHeap h root scope) = moveContents (eraseHeap h) root scope := by
  funext owner
  by_cases same : owner = root
  · subst owner
    cases found : h root with
    | none => simp [eraseHeap,moveHeap,moveContents,found]
    | some v => cases v <;> simp [eraseHeap,moveHeap,moveContents,found,inScope,contentsInScope,erase]
  · simp [eraseHeap,moveHeap,moveContents,same]

theorem lift (h : Heap) (root : Nat) (v : Contents) (found : eraseHeap h root = some v) :
    ∃ original, h root = some original ∧ erase original = v := by
  cases lookup : h root with
  | none => simp [eraseHeap,lookup] at found
  | some original => exact ⟨original,rfl,Option.some.inj (by simpa [eraseHeap,lookup] using found)⟩

theorem Models.tag {s : State} {root : Nat} {v : View} (model : Models s root v) :
    s.forest.lookup root = some (tagOf v) := by
  cases v with
  | flat _ _ _ => exact model.tag
  | rows _ _ _ _ _ => exact model.rows.rootTag

theorem Models.moved {s : State} {root : Nat} {v : View} (model : Models s root v) (scope : Nat) :
    Models {s with forest := s.forest.transferred root scope (tagOf v)} root (inScope v scope) := by
  have tag := Models.tag model
  have parent : (tagOf v).parent = none := by cases v <;> rfl
  have oldScope : (tagOf v).scope.isSome = true := by cases v <;> simp [tagOf,CppRowsGraph.tag]
  have valid : ({s with forest := s.forest.transferred root scope (tagOf v)} : State).wellFormed = true := by
    rw [Proofs.CppNestedVectorStore.wellFormed_transferred s root scope (tagOf v) tag parent oldScope]; exact model.valid
  have transferred := transferred_lookup_root s.forest root scope (tagOf v) tag
  cases v with
  | flat ty sc values => exact ⟨valid,transferred,model.buffer⟩
  | rows ty sc ids epoch values => exact ⟨⟨valid,transferred,model.rows.buffer⟩,model.length,model.contents⟩

theorem Models.other {s : State} {root other : Nat} {v w : View} (model : Models s root v)
    (otherModel : Models s other w) (different : other ≠ root) (scope : Nat) :
    Models {s with forest := s.forest.transferred root scope (tagOf v)} other w := by
  have tag := Models.tag model
  have parent : (tagOf v).parent = none := by cases v <;> rfl
  have oldScope : (tagOf v).scope.isSome = true := by cases v <;> simp [tagOf,CppRowsGraph.tag]
  have valid : ({s with forest := s.forest.transferred root scope (tagOf v)} : State).wellFormed = true := by
    rw [Proofs.CppNestedVectorStore.wellFormed_transferred s root scope (tagOf v) tag parent oldScope]; exact model.valid
  have kept := transferred_lookup_other s.forest root other scope (tagOf v) different
  cases w with
  | flat ty sc values => exact ⟨valid,kept.trans otherModel.tag,otherModel.buffer⟩
  | rows ty sc ids epoch values => exact ⟨⟨valid,kept.trans otherModel.rows.rootTag,otherModel.rows.buffer⟩,otherModel.length,otherModel.contents⟩

theorem frame_runs (f : Frame) (root scope : Nat) (v : View) (model : Models f.state root v) :
    f.transferRoot root v.element v.scope scope = some (movedFrame f root scope v) := by
  have parent : (tagOf v).parent = none := by cases v <;> rfl
  have scopeEq : (tagOf v).scope = some v.scope := by cases v <;> rfl
  have typed : (tagOf v).element = v.element := by cases v <;> rfl
  simp [Frame.transferRoot,transfer_valid_root f.state root v.element v.scope scope (tagOf v) model.valid (Models.tag model) parent scopeEq typed,movedFrame]

theorem Family.moved {params kept : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (root scope : Nat) (v : View) (lookup : h root = some v)
    (subset : ∀ p ∈ kept, p ∈ params) (different : ∀ p ∈ kept, p.owner ≠ root) :
    Family kept (moveHeap h root scope) (movedFrame f root scope v) (resources (movedFrame f root scope v)) := by
  have model := family.models root v lookup
  have valid := (Models.moved model scope).valid
  refine ⟨valid,?_,?_,?_,?_,?_,?_,measured_resources _⟩
  · intro owner view found
    by_cases same : owner = root
    · subst owner
      simp only [moveHeap,ite_true,lookup,Option.map_some,Option.some.injEq] at found
      subst view
      exact Models.moved model scope
    · have original : h owner = some view := by simpa [moveHeap,same] using found
      exact Models.other model (family.models owner view original) same scope
  · change f.rootWritable.length = (f.state.forest.transferred root scope (tagOf v)).objects.length
    rw [transferred_length]; exact family.lengths
  · intro p member; exact family.bindings p (subset p member)
  · intro p member; exact family.flags p (subset p member)
  · intro p member; exact family.permissions p (subset p member)
  · intro p member
    obtain ⟨view,found,element,scopeEq⟩ := family.views p (subset p member)
    exact ⟨view,by simpa [moveHeap,different p member] using found,element,scopeEq⟩

end Proofs.DynamicTransfer
