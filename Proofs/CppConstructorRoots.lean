import Proofs.DynamicTransfer
import Proofs.DynamicRetire

namespace Proofs.CppConstructorRoots
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppRootModel Proofs.DynamicTransfer Proofs.DynamicRetire

-- Capture the complete owned views before changing any scope. Root owners must
-- be distinct: transferring one member twice is not exporting two C++ members.
abbrev Root := Nat × View
abbrev RootSpec := Nat × Proofs.CppVectorOwnership.Element

-- The executable operation needs only owner IDs and element types. Logical
-- contents belong to the proof and are not runtime arguments.
def specs (roots : List Root) : List RootSpec :=
  roots.map fun root => (root.1,root.2.element)

def transferAll (frame : Frame) (roots : List RootSpec) (source target : Nat) : Option Frame :=
  match roots with
  | [] => some frame
  | (owner,element)::rest => do
    let moved ← frame.transferRoot owner element source target
    transferAll moved rest source target

def movedAll (frame : Frame) (roots : List Root) (target : Nat) : Frame :=
  match roots with
  | [] => frame
  | (owner,view)::rest => movedAll (movedFrame frame owner target view) rest target

def finishRoots (frame : Frame) (roots : List RootSpec) (source target : Nat) : Option Frame := do
  let moved ← transferAll frame roots source target
  moved.retireScope source

def HaveModels (frame : Frame) (roots : List Root) (scope : Nat) : Prop :=
  ∀ root ∈ roots, Models frame.state root.1 root.2 ∧ root.2.scope = scope

theorem scope_inScope (view : View) (scope : Nat) : (inScope view scope).scope = scope := by
  cases view <;> rfl

-- This is an actual execution theorem, including failure checks in transferRoot.
-- Besides every selected root, it preserves every model of an unrelated root.
theorem transferAll_ok (frame : Frame) (roots : List Root) (source target : Nat)
    (distinct : (roots.map Prod.fst).Nodup) (models : HaveModels frame roots source) :
    transferAll frame (specs roots) source target = some (movedAll frame roots target) ∧
    (∀ root ∈ roots, Models (movedAll frame roots target).state root.1 (inScope root.2 target)) ∧
    (∀ owner view, Models frame.state owner view → owner ∉ roots.map Prod.fst →
      Models (movedAll frame roots target).state owner view) := by
  induction roots generalizing frame with
  | nil => exact ⟨rfl,by simp,by intro owner view model _; exact model⟩
  | cons root rest ih =>
    rcases root with ⟨owner,view⟩
    obtain ⟨notRest,tailDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨model,scopeEq⟩ := models (owner,view) (by simp)
    have headRun : frame.transferRoot owner view.element source target =
        some (movedFrame frame owner target view) := by
      rw [← scopeEq]
      exact Proofs.DynamicTransfer.frame_runs frame owner target view model
    have tailModels : HaveModels (movedFrame frame owner target view) rest source := by
      intro root member
      obtain ⟨original,sc⟩ := models root (by simp [member])
      have different : root.1 ≠ owner := by
        intro eq
        exact notRest (List.mem_map.mpr ⟨root,member,eq⟩)
      exact ⟨Models.other model original different target,sc⟩
    obtain ⟨tailRun,tailExported,tailKept⟩ := ih _ tailDistinct tailModels
    refine ⟨?_,?_,?_⟩
    · simpa only [specs,List.map_cons,transferAll,headRun,Bind.bind,Option.bind,movedAll] using tailRun
    · intro root member
      rcases List.mem_cons.mp member with same | member
      · subst root
        exact tailKept owner (inScope view target) (Models.moved model target) notRest
      · exact tailExported root member
    · intro other otherView otherModel absent
      have different : other ≠ owner := by
        intro same
        exact absent (by simp [same])
      have absentRest : other ∉ rest.map Prod.fst := by
        intro member
        exact absent (by simp [member])
      exact tailKept other otherView (Models.other model otherModel different target) absentRest

-- Transfer changes forest ownership only; it does not copy vector payloads,
-- replace bindings, or change the root permission table.
theorem movedAll_layout (frame : Frame) (roots : List Root) (target : Nat) :
    (movedAll frame roots target).state.storage = frame.state.storage ∧
    (movedAll frame roots target).bindings = frame.bindings ∧
    (movedAll frame roots target).rootWritable = frame.rootWritable := by
  induction roots generalizing frame with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons root rest ih => exact ih (movedFrame frame root.1 target root.2)

theorem movedAll_length (frame : Frame) (roots : List Root) (target : Nat) :
    (movedAll frame roots target).state.forest.objects.length = frame.state.forest.objects.length := by
  induction roots generalizing frame with
  | nil => rfl
  | cons root rest ih =>
    change (movedAll (movedFrame frame root.1 target root.2) rest target).state.forest.objects.length = _
    rw [ih]
    exact Proofs.CppVectorOwnership.transferred_length _ _ _ _

-- Retirement happens exactly once, after all members have moved. Both flat
-- roots and nested row roots (including their descendants) are covered by Models.
theorem finishRoots_ok (frame : Frame) (roots : List Root) (source target : Nat)
    (valid : frame.state.wellFormed = true)
    (different : target ≠ source)
    (distinct : (roots.map Prod.fst).Nodup) (models : HaveModels frame roots source) :
    finishRoots frame (specs roots) source target =
      some (retiredFrame (movedAll frame roots target) source) ∧
    (∀ root ∈ roots, Models (retiredFrame (movedAll frame roots target) source).state
      root.1 (inScope root.2 target)) ∧
    (∀ owner view, Models frame.state owner view → owner ∉ roots.map Prod.fst →
      view.scope ≠ source →
      Models (retiredFrame (movedAll frame roots target) source).state owner view) := by
  obtain ⟨ran,exported,kept⟩ := transferAll_ok frame roots source target distinct models
  have movedValid : (movedAll frame roots target).state.wellFormed = true := by
    cases roots with
    | nil => exact valid
    | cons root rest => exact (exported root (by simp)).valid
  have retired := Proofs.DynamicRetire.frame_runs (movedAll frame roots target) source movedValid
  refine ⟨by simp only [finishRoots,ran,Bind.bind,Option.bind,retired],?_,?_⟩
  · intro root member
    exact Models.retired (exported root member) source (by rw [scope_inScope]; exact different)
  · intro owner view model absent outside
    exact Models.retired (kept owner view model absent) source outside

end Proofs.CppConstructorRoots
