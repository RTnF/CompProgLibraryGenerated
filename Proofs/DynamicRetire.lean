import Proofs.DynamicEffectRuns

namespace Proofs.DynamicRetire
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.CppRowsGraph Proofs.CppRowsContents Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr

-- Remove roots owned by the exiting scope. Descendants are removed by the
-- concrete forest; their contents belong to the corresponding root view.
def retireHeap (h : Heap) (scope : Nat) : Heap := fun owner => do
  let view ← h owner
  if view.scope = scope then none else some view

def retireContents (h : ContentsHeap) (scope : Nat) : ContentsHeap := fun owner => do
  let view ← h owner
  if view.scope = scope then none else some view

theorem erase_retire (h : Heap) (scope : Nat) : eraseHeap (retireHeap h scope) = retireContents (eraseHeap h) scope := by
  funext owner
  cases found : h owner with
  | none => simp [eraseHeap,retireHeap,retireContents,found]
  | some view =>
    by_cases same : view.scope = scope <;> cases view <;> simp_all [eraseHeap,retireHeap,retireContents,erase,View.scope,Contents.scope]

theorem Models.context {s : State} {root : Nat} {v : View} (model : Models s root v) : s.forest.context root = some v.scope := by
  obtain ⟨tag,found,_,parent,scope⟩ := model.root_tag
  simp [Forest.context,root_runs s.forest root tag found parent,found,scope]

theorem Models.retired {s : State} {root : Nat} {v : View} (model : Models s root v) (scope : Nat)
    (different : v.scope ≠ scope) : Models (s.retired scope) root v := by
  have rootContext := Models.context model
  have keepRoot : s.forest.context root ≠ some scope := by
    rw [rootContext]; intro same; exact different (Option.some.inj same)
  have rootTag : (s.retired scope).forest.lookup root = s.forest.lookup root :=
    retired_other_context s.forest scope root keepRoot
  have rootBuffer := retired_kept s scope root keepRoot
  cases v with
  | flat ty sc vs =>
    refine ⟨retired_wellFormed s scope model.valid,?_,?_⟩
    · rw [rootTag]; exact model.tag
    · obtain ⟨b,found,items⟩ := model.buffer
      exact ⟨b,by rw [rootBuffer]; exact found,items⟩
  | rows ty sc ids epoch vs =>
    refine ⟨⟨retired_wellFormed s scope model.rows.valid,?_,?_⟩,model.length,?_⟩
    · rw [rootTag]; exact model.rows.rootTag
    · obtain ⟨b,found,he,items⟩ := model.rows.buffer
      exact ⟨b,by rw [rootBuffer]; exact found,he,items⟩
    · intro k owner lookup
      obtain ⟨b,found,items⟩ := model.contents k owner lookup
      obtain ⟨_,object,_,earlier⟩ := row_object (⟨s,[],[]⟩ : Frame) root ty sc ids epoch k owner model.rows lookup
      have childTag := (Proofs.CppNestedFacts.object_buffer _ _ _ _ _ object).2.2.1
      have childContext := context_child s.forest owner root _ childTag rfl earlier
      have keepChild : s.forest.context owner ≠ some scope := by rw [childContext]; exact keepRoot
      exact ⟨b,by rw [retired_kept s scope owner keepChild]; exact found,items⟩

def retiredFrame (f : Frame) (scope : Nat) : Frame := {f with state := f.state.retired scope}

theorem frame_runs (f : Frame) (scope : Nat) (valid : f.state.wellFormed = true) :
    f.retireScope scope = some (retiredFrame f scope) := by
  simp [Frame.retireScope,retireScope_valid_input f.state scope valid,retiredFrame]

theorem Family.retired {params kept : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (scope : Nat) (subset : ∀ p ∈ kept, p ∈ params)
    (different : ∀ p ∈ kept, p.scope ≠ scope) :
    Family kept (retireHeap h scope) (retiredFrame f scope) (resources (retiredFrame f scope)) := by
  refine ⟨retired_wellFormed f.state scope family.valid,?_,?_,?_,?_,?_,?_,measured_resources _⟩
  · intro owner view lookup
    cases found : h owner with
    | none => simp [retireHeap,found] at lookup
    | some v =>
      simp only [retireHeap,found,Bind.bind,Option.bind] at lookup
      split at lookup
      · contradiction
      · rename_i other
        have same := Option.some.inj lookup
        subst view
        exact Models.retired (family.models owner v found) scope other
  · change f.rootWritable.length = (f.state.retired scope).forest.objects.length
    rw [(retired_lengths f.state scope).1]; exact family.lengths
  · intro p member; exact family.bindings p (subset p member)
  · intro p member; exact family.flags p (subset p member)
  · intro p member; exact family.permissions p (subset p member)
  · intro p member
    obtain ⟨v,found,element,scopedView⟩ := family.views p (subset p member)
    have other : v.scope ≠ scope := by rw [scopedView]; exact different p member
    exact ⟨v,by simp [retireHeap,found,other],element,scopedView⟩

end Proofs.DynamicRetire
