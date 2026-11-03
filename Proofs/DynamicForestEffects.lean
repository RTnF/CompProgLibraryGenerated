import Proofs.DynamicCallAuto

namespace Proofs.DynamicForestEffects
open Proofs.CppVectorOwnership Proofs.CppForestAppend

-- Absence in one retiring scope allows unrelated roots at any other scope.
def NoScope (f : Forest) (scope : Nat) : Prop := ∀ owner, f.context owner ≠ some scope

def Preserves (before after : Forest) : Prop := ∀ scope, NoScope before scope → NoScope after scope

theorem Preserves.refl (f : Forest) : Preserves f f := fun _ h => h
theorem Preserves.trans {a b c : Forest} (ab : Preserves a b) (bc : Preserves b c) : Preserves a c :=
  fun scope absent => bc scope (ab scope absent)

theorem context_missing (f : Forest) (owner : Nat) (missing : f.lookup owner = none) : f.context owner = none := by
  have root : f.rootOwner owner = none := by rw [Forest.rootOwner,missing]; rfl
  simp [Forest.context,root]

theorem NoScope.of_tags (f : Forest) (scope : Nat)
    (checked : f.objects.all (fun entry => entry.all (fun tag => tag.scope.all (fun sc => decide (sc ≠ scope)))) = true) :
    NoScope f scope := by
  intro owner bad
  unfold Forest.context at bad
  cases root : f.rootOwner owner with
  | none => simp [root] at bad
  | some r =>
    cases found : f.lookup r with
    | none => simp [root,found] at bad
    | some tag =>
      simp only [root,found,Bind.bind,Option.bind] at bad
      have member : some tag ∈ f.objects := by
        unfold Forest.lookup at found
        cases entry : f.objects[r]? with
        | none => simp [entry] at found
        | some value =>
          cases value with
          | none => simp [entry] at found
          | some t =>
            simp only [entry,Option.join_some,Option.some.injEq] at found
            subst t; exact List.mem_of_getElem? entry
      have accepted := List.all_eq_true.mp checked (some tag) member
      simp [bad] at accepted

theorem append_context_new (f : Forest) (parent : Nat) (tag : Tag) (element : Element)
    (valid : f.wellFormed = true) (found : f.lookup parent = some tag) :
    (f.appendChild parent tag element).context f.objects.length = f.context parent := by
  rw [context_child _ f.objects.length parent (childTag parent element) (append_fresh f parent tag element) rfl (lookup_lt f parent tag found)]
  exact context_extends f _ (append_extends f parent tag element found) valid parent tag found

theorem append_preserves (f : Forest) (parent : Nat) (tag : Tag) (element : Element)
    (valid : f.wellFormed = true) (found : f.lookup parent = some tag) :
    Preserves f (f.appendChild parent tag element) := by
  intro scope absent owner
  by_cases fresh : owner = f.objects.length
  · subst owner
    rw [append_context_new f parent tag element valid found]
    exact absent parent
  · by_cases bound : owner < f.objects.length
    · cases old : f.lookup owner with
      | some t =>
        rw [context_extends f _ (append_extends f parent tag element found) valid owner t old]
        exact absent owner
      | none =>
        have different : parent ≠ owner := by intro same; subst owner; rw [old] at found; contradiction
        have missing : (f.appendChild parent tag element).lookup owner = none := (append_old f parent tag element owner bound different).trans old
        rw [context_missing _ _ missing]; simp
    · have missing := lookup_past_end (f.appendChild parent tag element) owner (by rw [append_length]; omega)
      rw [context_missing _ _ missing]; simp

end Proofs.DynamicForestEffects
