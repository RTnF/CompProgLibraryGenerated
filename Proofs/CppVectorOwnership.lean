import Proofs.CppVectorBindings

namespace Proofs.CppVectorOwnership
open Proofs.CppScalar

inductive Element where
  | integer (type : Ty)
  | vector (element : Element)
deriving DecidableEq, Repr

def Element.supported : Element → Bool
  | .integer ty => decide (CppVectorBindings.supported ty)
  | .vector element => element.supported

-- These are logical allocation owners, not C++ header addresses. Root binding
-- lifetimes and payload / epoch / resource adapters must be checked separately.
structure Tag where
  element : Element
  parent : Option Nat
  scope : Option Nat
  children : List Nat := []
deriving DecidableEq, Repr

structure Forest where
  objects : List (Option Tag) := []
deriving DecidableEq, Repr

def Forest.lookup (f : Forest) (owner : Nat) : Option Tag := (f.objects[owner]?).join

def Forest.childOK (f : Forest) (owner : Nat) (expected : Element) (child : Nat) : Prop :=
  owner < child ∧ match f.lookup child with
    | none => False
    | some tag => tag.parent = some owner ∧ tag.scope = none ∧ tag.element = expected
instance (f : Forest) (owner : Nat) (expected : Element) (child : Nat) :
    Decidable (f.childOK owner expected child) := by
  unfold Forest.childOK
  cases f.lookup child <;> infer_instance

def Forest.parentOK (f : Forest) (owner : Nat) (tag : Tag) : Prop :=
  match tag.parent with
  | none => tag.scope.isSome = true
  | some parent => parent < owner ∧ tag.scope = none ∧ match f.lookup parent with
    | none => False
    | some origin => owner ∈ origin.children ∧ origin.element = .vector tag.element
instance (f : Forest) (owner : Nat) (tag : Tag) : Decidable (f.parentOK owner tag) := by
  unfold Forest.parentOK
  cases tag.parent with
  | none => infer_instance
  | some parent =>
    dsimp only
    cases f.lookup parent <;> infer_instance

def Forest.tagOK (f : Forest) (owner : Nat) (tag : Tag) : Prop :=
  tag.element.supported = true ∧ tag.children.Nodup ∧ f.parentOK owner tag ∧
    match tag.element with
    | .integer _ => tag.children = []
    | .vector element => ∀ child ∈ tag.children, f.childOK owner element child
instance (f : Forest) (owner : Nat) (tag : Tag) : Decidable (f.tagOK owner tag) := by
  unfold Forest.tagOK
  split <;> infer_instance

def Forest.check (f : Forest) (owner : Nat) : Bool :=
  match f.lookup owner with | none => true | some tag => decide (f.tagOK owner tag)
def Forest.wellFormed (f : Forest) : Bool := (List.range f.objects.length).all f.check

def Forest.rootOwner (f : Forest) (owner : Nat) : Option Nat := do
  let tag ← f.lookup owner
  match tag.parent with
  | none => some owner
  | some parent => if parent < owner then f.rootOwner parent else none
termination_by owner

def Forest.context (f : Forest) (owner : Nat) : Option Nat := do
  let root ← f.rootOwner owner
  let tag ← f.lookup root
  tag.scope

-- Every descendant is classified in the original forest before any deletion.
def Forest.retired (f : Forest) (scope : Nat) : Forest :=
  ⟨f.objects.mapIdx fun owner tag => if f.context owner = some scope then none else tag⟩

def Forest.retireScope (f : Forest) (scope : Nat) : Option Forest :=
  if f.wellFormed then
    let next := f.retired scope
    if next.wellFormed then some next else none
  else none

def Forest.transferred (f : Forest) (owner scope : Nat) (tag : Tag) : Forest :=
  ⟨f.objects.set owner (some {tag with scope := some scope})⟩

def Forest.transfer (f : Forest) (owner : Nat) (expected : Element) (fromScope toScope : Nat) : Option Forest := do
  if f.wellFormed then
    let tag ← f.lookup owner
    if tag.parent = none ∧ tag.scope = some fromScope ∧ tag.element = expected then
      let next := f.transferred owner toScope tag
      if next.wellFormed then some next else none
    else none
  else none

theorem lookup_past_end (f : Forest) (owner : Nat) (past : f.objects.length ≤ owner) :
    f.lookup owner = none := by simp [Forest.lookup,List.getElem?_eq_none_iff.mpr past]

theorem wellFormed_tag (f : Forest) (owner : Nat) (tag : Tag)
    (valid : f.wellFormed = true) (found : f.lookup owner = some tag) : f.tagOK owner tag := by
  have bound : owner < f.objects.length := by
    by_cases bounded : owner < f.objects.length
    · exact bounded
    · rw [lookup_past_end f owner (by omega)] at found
      contradiction
  have checked := List.all_eq_true.mp valid owner (List.mem_range.mpr bound)
  simpa [Forest.check,found] using checked

theorem root_runs (f : Forest) (owner : Nat) (tag : Tag)
    (found : f.lookup owner = some tag) (root : tag.parent = none) :
    f.rootOwner owner = some owner := by rw [Forest.rootOwner]; simp [found,root]

theorem child_runs (f : Forest) (owner parent : Nat) (tag : Tag)
    (found : f.lookup owner = some tag) (child : tag.parent = some parent) (earlier : parent < owner) :
    f.rootOwner owner = f.rootOwner parent := by rw [Forest.rootOwner]; simp [found,child,earlier]

theorem invalid_parent_fails (f : Forest) (owner parent : Nat) (tag : Tag)
    (found : f.lookup owner = some tag) (child : tag.parent = some parent) (wrong : owner ≤ parent) :
    f.rootOwner owner = none := by rw [Forest.rootOwner]; simp [found,child,Nat.not_lt.mpr wrong]

theorem wellFormed_root_exists (f : Forest) (valid : f.wellFormed = true)
    (owner : Nat) (tag : Tag) (found : f.lookup owner = some tag) :
    ∃ root, f.rootOwner owner = some root := by
  induction owner using Nat.strongRecOn generalizing tag with
  | ind owner ih =>
    have good := wellFormed_tag f owner tag valid found
    have parentGood := good.2.2.1
    cases hp : tag.parent with
    | none => exact ⟨owner,root_runs f owner tag found hp⟩
    | some parent =>
      cases origin : f.lookup parent with
      | none => simp [Forest.parentOK,hp,origin] at parentGood
      | some parentTag =>
        simp only [Forest.parentOK,hp,origin] at parentGood
        obtain ⟨root,ran⟩ := ih parent parentGood.1 parentTag origin
        exact ⟨root,(child_runs f owner parent tag found hp parentGood.1).trans ran⟩

theorem rootOwner_is_root (f : Forest) (owner root : Nat)
    (ran : f.rootOwner owner = some root) :
    ∃ tag, f.lookup root = some tag ∧ tag.parent = none := by
  induction owner using Nat.strongRecOn with
  | ind owner ih =>
    cases found : f.lookup owner with
    | none => rw [Forest.rootOwner] at ran; simp [found] at ran
    | some tag =>
      cases hp : tag.parent with
      | none =>
        rw [root_runs f owner tag found hp] at ran
        cases ran
        exact ⟨tag,found,hp⟩
      | some parent =>
        by_cases earlier : parent < owner
        · rw [child_runs f owner parent tag found hp earlier] at ran
          exact ih parent earlier ran
        · rw [invalid_parent_fails f owner parent tag found hp (by omega)] at ran
          contradiction


theorem wellFormed_context_exists (f : Forest) (valid : f.wellFormed = true)
    (owner : Nat) (tag : Tag) (found : f.lookup owner = some tag) :
    ∃ scope, f.context owner = some scope := by
  obtain ⟨root,ran⟩ := wellFormed_root_exists f valid owner tag found
  obtain ⟨origin,lookup,parent⟩ := rootOwner_is_root f owner root ran
  have rooted := (wellFormed_tag f root origin valid lookup).2.2.1
  simp only [Forest.parentOK,parent] at rooted
  cases scope : origin.scope with
  | none => simp [scope] at rooted
  | some context => exact ⟨context,by simp [Forest.context,ran,lookup,scope]⟩

theorem context_child (f : Forest) (owner parent : Nat) (tag : Tag)
    (found : f.lookup owner = some tag) (child : tag.parent = some parent) (earlier : parent < owner) :
    f.context owner = f.context parent := by
  simp only [Forest.context,child_runs f owner parent tag found child earlier]


theorem retired_length (f : Forest) (scope : Nat) : (f.retired scope).objects.length = f.objects.length := by
  simp [Forest.retired]

theorem retired_lookup (f : Forest) (scope owner : Nat) :
    (f.retired scope).lookup owner = if f.context owner = some scope then none else f.lookup owner := by
  simp only [Forest.lookup,Forest.retired,List.getElem?_mapIdx]
  cases f.objects[owner]? <;> simp

theorem retired_same_context (f : Forest) (scope owner : Nat) (same : f.context owner = some scope) :
    (f.retired scope).lookup owner = none := by rw [retired_lookup]; simp [same]

theorem retired_other_context (f : Forest) (scope owner : Nat) (other : f.context owner ≠ some scope) :
    (f.retired scope).lookup owner = f.lookup owner := by rw [retired_lookup]; simp [other]

theorem retireScope_success_valid (f next : Forest) (scope : Nat)
    (ran : f.retireScope scope = some next) : next.wellFormed = true := by
  unfold Forest.retireScope at ran
  dsimp only at ran
  split at ran
  · split at ran
    · cases ran; assumption
    · contradiction
  · contradiction

theorem retireScope_success_length (f next : Forest) (scope : Nat)
    (ran : f.retireScope scope = some next) : next.objects.length = f.objects.length := by
  unfold Forest.retireScope at ran
  dsimp only at ran
  split at ran
  · split at ran
    · cases ran; exact retired_length f scope
    · contradiction
  · contradiction

theorem transfer_wrong_scope (f : Forest) (owner : Nat) (expected : Element) (fromScope toScope : Nat)
    (tag : Tag) (found : f.lookup owner = some tag) (wrong : tag.scope ≠ some fromScope) :
    f.transfer owner expected fromScope toScope = none := by
  simp [Forest.transfer,found,wrong]

theorem transfer_runs (f : Forest) (owner : Nat) (expected : Element) (fromScope toScope : Nat)
    (tag : Tag) (valid : f.wellFormed = true) (found : f.lookup owner = some tag)
    (root : tag.parent = none) (scope : tag.scope = some fromScope) (type : tag.element = expected)
    (nextValid : (f.transferred owner toScope tag).wellFormed = true) :
    f.transfer owner expected fromScope toScope = some (f.transferred owner toScope tag) := by
  simp [Forest.transfer,valid,found,root,scope,type,nextValid]

theorem transfer_child_fails (f : Forest) (owner parent : Nat) (expected : Element)
    (fromScope toScope : Nat) (tag : Tag) (found : f.lookup owner = some tag)
    (child : tag.parent = some parent) : f.transfer owner expected fromScope toScope = none := by
  simp [Forest.transfer,found,child]

theorem transferred_length (f : Forest) (owner scope : Nat) (tag : Tag) :
    (f.transferred owner scope tag).objects.length = f.objects.length := by
  simp [Forest.transferred]

theorem transferred_lookup_other (f : Forest) (owner other scope : Nat) (tag : Tag)
    (different : other ≠ owner) :
    (f.transferred owner scope tag).lookup other = f.lookup other := by
  simp [Forest.lookup,Forest.transferred,Ne.symm different]


theorem transferred_lookup_root (f : Forest) (owner scope : Nat) (tag : Tag)
    (found : f.lookup owner = some tag) :
    (f.transferred owner scope tag).lookup owner = some {tag with scope := some scope} := by
  have bound : owner < f.objects.length := by
    by_cases bounded : owner < f.objects.length
    · exact bounded
    · rw [lookup_past_end f owner (by omega)] at found
      contradiction
  simp [Forest.lookup,Forest.transferred,bound]

theorem rootOwner_transferred (f : Forest) (root scope : Nat) (tag : Tag)
    (found : f.lookup root = some tag) (parent : tag.parent = none) (owner : Nat) :
    (f.transferred root scope tag).rootOwner owner = f.rootOwner owner := by
  induction owner using Nat.strongRecOn with
  | ind owner ih =>
    by_cases same : owner = root
    · subst owner
      rw [root_runs f root tag found parent]
      exact root_runs _ root {tag with scope := some scope}
        (transferred_lookup_root f root scope tag found) parent
    · have unchanged := transferred_lookup_other f root owner scope tag same
      cases lookup : f.lookup owner with
      | none =>
        rw [Forest.rootOwner,Forest.rootOwner]
        simp [unchanged,lookup]
      | some current =>
        have updated : (f.transferred root scope tag).lookup owner = some current := unchanged.trans lookup
        cases hp : current.parent with
        | none => rw [root_runs _ owner current updated hp,root_runs f owner current lookup hp]
        | some earlier =>
          by_cases less : earlier < owner
          · rw [child_runs _ owner earlier current updated hp less,child_runs f owner earlier current lookup hp less]
            exact ih earlier less
          · rw [invalid_parent_fails _ owner earlier current updated hp (by omega),
                invalid_parent_fails f owner earlier current lookup hp (by omega)]


theorem context_transferred (f : Forest) (root scope : Nat) (tag : Tag)
    (found : f.lookup root = some tag) (parent : tag.parent = none) (owner : Nat) :
    (f.transferred root scope tag).context owner =
      if f.rootOwner owner = some root then some scope else f.context owner := by
  simp only [Forest.context,rootOwner_transferred f root scope tag found parent owner]
  cases ran : f.rootOwner owner with
  | none => simp
  | some ancestor =>
    by_cases same : ancestor = root
    · subst ancestor
      simp [transferred_lookup_root f root scope tag found]
    · simp [same,transferred_lookup_other f root ancestor scope tag same]

theorem child_has_one_parent (f : Forest) (first second child : Nat) (a b : Element)
    (left : f.childOK first a child) (right : f.childOK second b child) : first = second := by
  cases found : f.lookup child with
  | none => simp [Forest.childOK,found] at left
  | some tag =>
    simp only [Forest.childOK,found] at left right
    exact Option.some.inj (left.2.1.symm.trans right.2.1)


theorem parentOK_transferred (f : Forest) (root scope owner : Nat) (tag current : Tag)
    (found : f.lookup root = some tag) :
    (f.transferred root scope tag).parentOK owner current ↔ f.parentOK owner current := by
  cases hp : current.parent with
  | none => simp [Forest.parentOK,hp]
  | some parent =>
    by_cases same : parent = root
    · subst parent
      simp [Forest.parentOK,hp,transferred_lookup_root f root scope tag found,found]
    · simp [Forest.parentOK,hp,transferred_lookup_other f root parent scope tag same]

theorem childOK_transferred (f : Forest) (root scope owner child : Nat) (tag : Tag) (expected : Element)
    (found : f.lookup root = some tag) (oldScope : tag.scope.isSome = true) :
    (f.transferred root scope tag).childOK owner expected child ↔ f.childOK owner expected child := by
  by_cases same : child = root
  · subst child
    cases hs : tag.scope with
    | none => simp [hs] at oldScope
    | some previous => simp [Forest.childOK,transferred_lookup_root f root scope tag found,found,hs]
  · simp [Forest.childOK,transferred_lookup_other f root child scope tag same]

theorem tagOK_transferred (f : Forest) (root scope owner : Nat) (tag current : Tag)
    (found : f.lookup root = some tag) (oldScope : tag.scope.isSome = true) :
    (f.transferred root scope tag).tagOK owner current ↔ f.tagOK owner current := by
  simp only [Forest.tagOK,parentOK_transferred f root scope owner tag current found]
  cases current.element <;> simp [childOK_transferred f root scope owner _ tag _ found oldScope]

theorem wellFormed_transferred (f : Forest) (root scope : Nat) (tag : Tag)
    (found : f.lookup root = some tag) (parent : tag.parent = none) (oldScope : tag.scope.isSome = true) :
    (f.transferred root scope tag).wellFormed = f.wellFormed := by
  have checked : (f.transferred root scope tag).check = f.check := by
    funext owner
    by_cases same : owner = root
    · subst owner
      simp only [Forest.check,transferred_lookup_root f root scope tag found,found]
      apply decide_eq_decide.mpr
      simp only [tagOK_transferred f root scope root tag {tag with scope := some scope} found oldScope]
      simp [Forest.tagOK,Forest.parentOK,parent,oldScope]
    · simp only [Forest.check,transferred_lookup_other f root owner scope tag same]
      cases lookup : f.lookup owner with
      | none => rfl
      | some current => simp only [tagOK_transferred f root scope owner tag current found oldScope]
  simp only [Forest.wellFormed,transferred_length,checked]

theorem transfer_valid_root (f : Forest) (owner : Nat) (expected : Element) (fromScope toScope : Nat)
    (tag : Tag) (valid : f.wellFormed = true) (found : f.lookup owner = some tag)
    (root : tag.parent = none) (scope : tag.scope = some fromScope) (type : tag.element = expected) :
    f.transfer owner expected fromScope toScope = some (f.transferred owner toScope tag) := by
  apply transfer_runs f owner expected fromScope toScope tag valid found root scope type
  rw [wellFormed_transferred f owner toScope tag found root (by simp [scope])]
  exact valid


theorem parentOK_retired_kept (f : Forest) (scope owner : Nat) (tag : Tag)
    (found : f.lookup owner = some tag) (good : f.parentOK owner tag)
    (kept : f.context owner ≠ some scope) : (f.retired scope).parentOK owner tag := by
  cases hp : tag.parent with
  | none => simpa [Forest.parentOK,hp] using good
  | some parent =>
    cases origin : f.lookup parent with
    | none => simp [Forest.parentOK,hp,origin] at good
    | some parentTag =>
      have fields := good
      simp only [Forest.parentOK,hp,origin] at fields
      have same := context_child f owner parent tag found hp fields.1
      have keepParent : f.context parent ≠ some scope := by rw [← same]; exact kept
      have lookup := (retired_other_context f scope parent keepParent).trans origin
      simpa [Forest.parentOK,hp,lookup] using fields

theorem childOK_retired_kept (f : Forest) (scope owner child : Nat) (expected : Element)
    (good : f.childOK owner expected child) (kept : f.context owner ≠ some scope) :
    (f.retired scope).childOK owner expected child := by
  cases found : f.lookup child with
  | none => simp [Forest.childOK,found] at good
  | some tag =>
    have fields := good
    simp only [Forest.childOK,found] at fields
    have same := context_child f child owner tag found fields.2.1 fields.1
    have keepChild : f.context child ≠ some scope := by rw [same]; exact kept
    have lookup := (retired_other_context f scope child keepChild).trans found
    simpa [Forest.childOK,lookup] using fields

theorem tagOK_retired_kept (f : Forest) (scope owner : Nat) (tag : Tag)
    (found : f.lookup owner = some tag) (good : f.tagOK owner tag)
    (kept : f.context owner ≠ some scope) : (f.retired scope).tagOK owner tag := by
  refine ⟨good.1,good.2.1,parentOK_retired_kept f scope owner tag found good.2.2.1 kept,?_⟩
  have children := good.2.2.2
  cases element : tag.element with
  | integer ty => simpa [element] using children
  | vector expected =>
    simp only [element] at children ⊢
    intro child member
    exact childOK_retired_kept f scope owner child expected (children child member) kept

theorem retired_wellFormed (f : Forest) (scope : Nat) (valid : f.wellFormed = true) :
    (f.retired scope).wellFormed = true := by
  apply List.all_eq_true.mpr
  intro owner member
  cases found : f.lookup owner with
  | none => simp [Forest.check,retired_lookup,found]
  | some tag =>
    by_cases removed : f.context owner = some scope
    · simp [Forest.check,retired_same_context f scope owner removed]
    · have good := wellFormed_tag f owner tag valid found
      have nextGood := tagOK_retired_kept f scope owner tag found good removed
      simpa [Forest.check,retired_other_context f scope owner removed,found] using nextGood

theorem retireScope_valid_input (f : Forest) (scope : Nat) (valid : f.wellFormed = true) :
    f.retireScope scope = some (f.retired scope) := by
  simp [Forest.retireScope,valid,retired_wellFormed f scope valid]


end Proofs.CppVectorOwnership
