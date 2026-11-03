import Proofs.CppConstructorRoots

namespace Proofs.CppConstructorRetirement
open Proofs.CppVectorOwnership Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppRootModel Proofs.DynamicTransfer Proofs.DynamicRetire Proofs.CppConstructorRoots

private theorem context_none (f : Forest) (owner : Nat) (gone : f.lookup owner = none) :
    f.context owner = none := by
  have root : f.rootOwner owner = none := by rw [Forest.rootOwner]; simp [gone]
  simp [Forest.context,root]

-- Retirement cannot invent a new context. Every surviving root/descendant
-- keeps its original context, which differs from the destroyed scope.
theorem retired_context_some (f : Forest) (valid : f.wellFormed = true) (scope owner c : Nat)
    (found : (f.retired scope).context owner = some c) :
    f.context owner = some c ∧ c ≠ scope := by
  induction owner using Nat.strongRecOn generalizing c with
  | ind owner ih =>
    cases original : f.lookup owner with
    | none =>
      have gone : (f.retired scope).lookup owner = none := by
        simp [Proofs.CppVectorOwnership.retired_lookup,original]
      rw [context_none _ _ gone] at found
      contradiction
    | some tag =>
      by_cases removed : f.context owner = some scope
      · rw [context_none _ _ (retired_same_context f scope owner removed)] at found
        contradiction
      have kept := (retired_other_context f scope owner removed).trans original
      cases parent : tag.parent with
      | none =>
        have before : f.context owner = tag.scope := by
          simp [Forest.context,root_runs f owner tag original parent,original]
        have after : (f.retired scope).context owner = tag.scope := by
          simp [Forest.context,root_runs (f.retired scope) owner tag kept parent,kept]
        have same := before.trans (after.symm.trans found)
        exact ⟨same,by intro eq; subst c; exact removed same⟩
      | some ancestor =>
        have good := (wellFormed_tag f owner tag valid original).2.2.1
        simp only [Forest.parentOK,parent] at good
        have earlier : ancestor < owner := good.1
        have after := context_child (f.retired scope) owner ancestor tag kept parent earlier
        obtain ⟨before,other⟩ := ih ancestor earlier c (after.symm.trans found)
        exact ⟨(context_child f owner ancestor tag original parent earlier).trans before,other⟩

theorem movedFrame_scope_le (frame : Frame) (root target upper : Nat) (view : View)
    (model : Models frame.state root view) (targetBound : target ≤ upper)
    (before : ∀ owner c, frame.state.forest.context owner = some c → c ≤ upper) :
    ∀ owner c, (movedFrame frame root target view).state.forest.context owner = some c → c ≤ upper := by
  intro owner c found
  have parent : (tagOf view).parent = none := by cases view <;> rfl
  change (frame.state.forest.transferred root target (tagOf view)).context owner = some c at found
  rw [context_transferred frame.state.forest root target (tagOf view) (Proofs.DynamicTransfer.Models.tag model) parent owner] at found
  split at found
  · cases found; exact targetBound
  · exact before owner c found

theorem movedAll_scope_le (frame : Frame) (roots : List Root) (source target upper : Nat)
    (distinct : (roots.map Prod.fst).Nodup) (models : HaveModels frame roots source)
    (targetBound : target ≤ upper)
    (before : ∀ owner c, frame.state.forest.context owner = some c → c ≤ upper) :
    ∀ owner c, (movedAll frame roots target).state.forest.context owner = some c → c ≤ upper := by
  induction roots generalizing frame with
  | nil => exact before
  | cons root rest ih =>
    obtain ⟨absent,tailDistinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨model,_⟩ := models root (by simp)
    have tailModels : HaveModels (movedFrame frame root.1 target root.2) rest source := by
      intro other member
      obtain ⟨original,scope⟩ := models other (by simp [member])
      have different : other.1 ≠ root.1 := by
        intro same
        exact absent (List.mem_map.mpr ⟨other,member,same⟩)
      exact ⟨Models.other model original different target,scope⟩
    exact ih _ tailDistinct tailModels (movedFrame_scope_le frame root.1 target upper root.2 model targetBound before)

theorem finished_scope_le (frame : Frame) (roots : List Root) (target : Nat)
    (valid : frame.state.wellFormed = true) (distinct : (roots.map Prod.fst).Nodup)
    (models : HaveModels frame roots (target+1))
    (before : ∀ owner c, frame.state.forest.context owner = some c → c ≤ target+1) :
    ∀ owner c, (retiredFrame (movedAll frame roots target) (target+1)).state.forest.context owner = some c → c ≤ target := by
  have movedBound := movedAll_scope_le frame roots (target+1) target (target+1) distinct models (by omega) before
  have movedValid : (movedAll frame roots target).state.wellFormed = true := by
    cases roots with
    | nil => exact valid
    | cons root rest => exact ((transferAll_ok frame (root::rest) (target+1) target distinct models).2.1 root (by simp)).valid
  intro owner c found
  have forestValid := (Proofs.CppNestedVectorStore.wellFormed_parts _ movedValid).2.1
  obtain ⟨original,other⟩ := retired_context_some (movedAll frame roots target).state.forest forestValid (target+1) owner c found
  have bound := movedBound owner c original
  omega

-- The entire selected root buffer survives, including capacity, limit, epoch
-- and owner metadata; this is stronger than retaining just its items.
theorem finished_buffer (frame : Frame) (roots : List Root) (source target : Nat)
    (distinct : (roots.map Prod.fst).Nodup) (models : HaveModels frame roots source)
    (different : target ≠ source) (root : Root) (member : root ∈ roots) :
    (retiredFrame (movedAll frame roots target) source).state.storage.lookup root.1 =
      frame.state.storage.lookup root.1 := by
  have model := (transferAll_ok frame roots source target distinct models).2.1 root member
  have context := Models.context model
  have kept : (movedAll frame roots target).state.forest.context root.1 ≠ some source := by
    rw [context,scope_inScope]
    intro same
    exact different (Option.some.inj same)
  change ((movedAll frame roots target).state.retired source).storage.lookup root.1 = _
  rw [Proofs.CppNestedVectorStore.retired_kept _ source root.1 kept,(movedAll_layout frame roots target).1]

end Proofs.CppConstructorRetirement
