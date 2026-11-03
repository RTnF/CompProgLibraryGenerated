import Proofs.CppFixedRun
import Proofs.CppCallFrame

namespace Proofs.CppPrepareTarget
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.DynamicResultValid Proofs.CppFixedWrite

theorem root_added (f g : Frame) (owner scope : Nat) (element : Element) (wr : Bool) (index : Nat)
    (actual : f.bindRoot owner element scope wr = some (g,index)) :
    (g,index) = f.addBinding ⟨owner,element,wr,.root scope⟩ := by
  unfold Frame.bindRoot at actual
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ actual
  obtain ⟨maximum,_,rest⟩ := bind_some _ _ _ rest
  try dsimp only at rest
  split at rest
  · exact (Option.some.inj rest).symm
  · simp at rest

theorem bind_one_extension (s t : NState) (r : Resolved) (actual : bindOne s r = some t) :
    ∃ bs xs, t.frame.bindings = s.frame.bindings++bs ∧ t.slots = s.slots++xs := by
  cases r with
  | scalar ty wr v | scalarAddress ty address wr =>
    unfold bindOne at actual
    obtain ⟨scalars,_,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    subst t
    exact ⟨[],[.scalar s.scalars.bindings.length],by simp,rfl⟩
  | vectorChild owner address ty wr =>
    unfold bindOne at actual
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    subst t
    exact ⟨[⟨owner,.integer ty,wr,.child address⟩],[.vector s.frame.bindings.length],rfl,rfl⟩
  | vector owner scope ty wr =>
    unfold bindOne at actual
    obtain ⟨⟨frame,index⟩,bound,rest⟩ := bind_some _ _ _ actual
    have added := root_added s.frame frame owner scope _ wr index bound
    have frameEq := congrArg Prod.fst added
    dsimp only [Frame.addBinding] at frameEq
    have eq := Option.some.inj rest
    subst t
    refine ⟨[⟨owner,(.integer ty),wr,.root scope⟩],[.vector index],?_,rfl⟩
    change frame.bindings = _
    rw [frameEq]
  | nestedRoot owner scope ty wr =>
    unfold bindOne at actual
    obtain ⟨⟨frame,index⟩,bound,rest⟩ := bind_some _ _ _ actual
    have added := root_added s.frame frame owner scope _ wr index bound
    have frameEq := congrArg Prod.fst added
    dsimp only [Frame.addBinding] at frameEq
    have eq := Option.some.inj rest
    subst t
    refine ⟨[⟨owner,(.vector (.integer ty)),wr,.root scope⟩],[.vector index],?_,rfl⟩
    change frame.bindings = _
    rw [frameEq]

theorem target_extension (s t : NState) (root : Nat) (target : Target s root)
    (extension : ∃ bs xs, t.frame.bindings = s.frame.bindings++bs ∧ t.slots = s.slots++xs) : Target t root := by
  obtain ⟨bs,xs,bindings,slots⟩ := extension
  obtain ⟨index,binding,slot,found,owner⟩ := target
  have inside : 0 < s.slots.length := by
    by_cases h : 0 < s.slots.length
    · exact h
    have missing : s.slots[0]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp [NState.vectorSlot,missing] at slot
  have first : t.slots[0]? = s.slots[0]? := by rw [slots]; exact List.getElem?_append_left inside
  refine ⟨index,binding,?_,?_,owner⟩
  · simpa only [NState.vectorSlot,first] using slot
  · rw [bindings]
    simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found

theorem bind_all_target (s t : NState) (rs : List Resolved) (root : Nat) (target : Target s root)
    (actual : bindAll s rs = some t) : Target t root := by
  induction rs generalizing s with
  | nil => have eq := Option.some.inj actual; subst t; exact target
  | cons r rs ih =>
    unfold bindAll at actual
    obtain ⟨mid,head,tail⟩ := bind_some _ _ _ actual
    exact ih mid (target_extension s mid root target (bind_one_extension s mid r head)) tail

theorem first_vector (s t : NState) (root scope : Nat) (ty : Ty) (wr : Bool)
    (empty : s.slots = []) (actual : bindOne s (.vector root scope ty wr) = some t) : Target t root := by
  unfold bindOne at actual
  obtain ⟨⟨frame,index⟩,bound,rest⟩ := bind_some _ _ _ actual
  have added := root_added s.frame frame root scope (.integer ty) wr index bound
  have frameEq := congrArg Prod.fst added
  have indexEq := congrArg Prod.snd added
  dsimp only [Frame.addBinding] at frameEq indexEq
  have eq := Option.some.inj rest
  subst t
  refine ⟨index,⟨root,.integer ty,wr,.root scope⟩,?_,?_,rfl⟩
  · simp [NState.vectorSlot,NState.observe,empty]
  · change frame.bindings[index]? = _
    rw [frameEq,indexEq]
    simp [Frame.addBinding]

theorem first_child (s t : NState) (owner : Nat) (address : Proofs.CppVector.ElementRef)
    (ty : Ty) (wr : Bool) (empty : s.slots = [])
    (actual : bindOne s (.vectorChild owner address ty wr) = some t) : Target t owner := by
  unfold bindOne at actual
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ actual
  have eq := Option.some.inj rest
  subst t
  refine ⟨s.frame.bindings.length,⟨owner,.integer ty,wr,.child address⟩,?_,?_,rfl⟩
  · simp [NState.vectorSlot,NState.observe,empty,Frame.addBinding]
  · simp [NState.observe,Frame.addBinding]

theorem prepare_target (caller init : NState) (ty : Ty) (wr : Bool)
    (ps : List Proofs.CppVectorBindings.Parameter) (args : List NArgument) (slot index : Nat) (binding : Binding)
    (vectorSlot : caller.vectorSlot slot = some index) (found : caller.frame.bindings[index]? = some binding)
    (actual : prepare caller (.vector ty wr::ps) (.vectorReference slot::args) = some init) : Target init binding.owner := by
  unfold prepare at actual
  split at actual
  · obtain ⟨⟨last,rs⟩,resolved,rest⟩ := bind_some _ _ _ actual
    unfold resolveAll at resolved
    obtain ⟨⟨mid,r⟩,head,tail⟩ := bind_some _ _ _ resolved
    unfold resolve at head
    try dsimp only at head
    simp only [vectorSlot,found,Bind.bind,Option.bind] at head
    obtain ⟨⟨buf,tag⟩,_,head⟩ := bind_some _ _ _ head
    try dsimp only at head
    cases header : binding.header with
    | child address =>
      simp only [header] at head
      split at head
      · have rEq := congrArg Prod.snd (Option.some.inj head)
        change Resolved.vectorChild binding.owner address ty wr = r at rEq
        subst r
        dsimp only at tail
        obtain ⟨⟨lastState,restRs⟩,_,rsEq⟩ := bind_some _ _ _ tail
        have resolvedEq := congrArg Prod.snd (Option.some.inj rsEq)
        change Resolved.vectorChild binding.owner address ty wr::restRs = rs at resolvedEq
        subst rs
        dsimp only at rest
        unfold bindAll at rest
        obtain ⟨next,bound,remaining⟩ := bind_some _ _ _ rest
        exact bind_all_target next init restRs binding.owner (first_child _ next binding.owner address ty wr rfl bound) remaining
      · simp at head
    | root scope =>
      simp only [header] at head
      split at head
      · have rEq := congrArg Prod.snd (Option.some.inj head)
        change Resolved.vector binding.owner scope ty wr = r at rEq
        subst r
        dsimp only at tail
        obtain ⟨⟨lastState,restRs⟩,_,rsEq⟩ := bind_some _ _ _ tail
        have resolvedEq := congrArg Prod.snd (Option.some.inj rsEq)
        change Resolved.vector binding.owner scope ty wr::restRs = rs at resolvedEq
        subst rs
        dsimp only at rest
        unfold bindAll at rest
        obtain ⟨next,bound,remaining⟩ := bind_some _ _ _ rest
        exact bind_all_target next init restRs binding.owner (first_vector _ next binding.owner scope ty wr rfl bound) remaining
      · simp at head
  · simp at actual

end Proofs.CppPrepareTarget
