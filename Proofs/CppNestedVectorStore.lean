import Proofs.CppVectorOwnership

namespace Proofs.CppNestedVectorStore
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership

-- A vector element is either a fixed-width integer or the logical owner of
-- a child vector. A child ID is not a C++ header address or a borrowed binding.
inductive Value where
  | integer (value : Int)
  | child (owner : Nat)
deriving DecidableEq, Repr

def accepts : Element → Value → Bool
  | .integer ty, .integer value => ty.valid value
  | .vector _, .child _ => true
  | _, _ => false

def payloadOK (tag : Tag) (buffer : Buffer Value) : Prop :=
  buffer.Valid (accepts tag.element) ∧
  match tag.element with
  | .integer _ => True
  | .vector _ => buffer.items = tag.children.map Value.child
instance (tag : Tag) (buffer : Buffer Value) : Decidable (payloadOK tag buffer) := by
  unfold payloadOK
  cases tag.element <;> infer_instance

structure State where
  forest : Forest
  storage : Store Value
deriving DecidableEq, Repr

def State.check (s : State) (owner : Nat) : Bool :=
  match s.forest.lookup owner, s.storage.lookup owner with
  | none, none => true
  | some tag, some buffer => decide (buffer.owner = owner ∧ payloadOK tag buffer)
  | _, _ => false

def State.wellFormed (s : State) : Bool :=
  decide (s.forest.objects.length = s.storage.objects.length) &&
    s.forest.wellFormed && (List.range s.storage.objects.length).all s.check

-- Each root has a header; a child's header is already included in its
-- parent's capacity. Units are abstract storage cells, not bytes. Limits
-- are supplied by the future checked ABI / binding adapter.
def State.nodeSpace (s : State) (owner : Nat) : Nat :=
  match s.forest.lookup owner, s.storage.lookup owner with
  | some tag, some buffer => buffer.capacity + if tag.parent = none then 1 else 0
  | _, _ => 0
def State.liveSpace (s : State) : Nat :=
  ((List.range s.storage.objects.length).map s.nodeSpace).sum

-- Integer destruction has no element destructor. Nested destruction visits
-- each constructed child header once, and releases each live buffer once.
def State.destroyWork (s : State) (scope : Nat) : Nat :=
  ((List.range s.storage.objects.length).map fun owner =>
    if s.forest.context owner = some scope then
      match s.forest.lookup owner, s.storage.lookup owner with
      | some tag, some buffer => match tag.element with
        | .integer _ => 1
        | .vector _ => buffer.items.length+1
      | _, _ => 0
    else 0).sum

-- Classify both lists using the ORIGINAL forest, before removing any parent.
def State.retired (s : State) (scope : Nat) : State :=
  {forest := s.forest.retired scope,
   storage := {s.storage with
     objects := s.storage.objects.mapIdx fun owner buffer =>
       if s.forest.context owner = some scope then none else buffer,
     work := s.storage.work+s.destroyWork scope,
     peak := max s.storage.peak (s.liveSpace-s.storage.baseSpace)}}

def State.retireScope (s : State) (scope : Nat) : Option State :=
  if s.wellFormed then
    let next := s.retired scope
    if next.wellFormed then some next else none
  else none

-- Moving a ROOT changes scope metadata only. Physical root bindings and
-- references to child headers still require separate lifetime checks.
def State.transfer (s : State) (owner : Nat) (expected : Element)
    (fromScope toScope : Nat) : Option State := do
  if s.wellFormed then
    let forest ← s.forest.transfer owner expected fromScope toScope
    some {s with forest := forest}
  else none

theorem wellFormed_parts (s : State) (valid : s.wellFormed = true) :
    s.forest.objects.length = s.storage.objects.length ∧ s.forest.wellFormed = true ∧
    (List.range s.storage.objects.length).all s.check = true := by
  simp only [State.wellFormed,Bool.and_eq_true,decide_eq_true_eq] at valid
  exact ⟨valid.1.1,valid.1.2,valid.2⟩

theorem wellFormed_buffer (s : State) (owner : Nat) (buffer : Buffer Value)
    (valid : s.wellFormed = true) (found : s.storage.lookup owner = some buffer) :
    ∃ tag, s.forest.lookup owner = some tag ∧ buffer.owner = owner ∧ payloadOK tag buffer := by
  have bound := lookup_bound s.storage owner buffer found
  have good := List.all_eq_true.mp (wellFormed_parts s valid).2.2 owner (List.mem_range.mpr bound)
  cases tagFound : s.forest.lookup owner with
  | none => simp [State.check,tagFound,found] at good
  | some tag =>
    refine ⟨tag,rfl,?_⟩
    simpa [State.check,tagFound,found] using good

theorem retired_lengths (s : State) (scope : Nat) :
    (s.retired scope).forest.objects.length = s.forest.objects.length ∧
    (s.retired scope).storage.objects.length = s.storage.objects.length := by
  simp [State.retired,Forest.retired]

theorem retired_lookup (s : State) (scope owner : Nat) :
    (s.retired scope).storage.lookup owner =
      if s.forest.context owner = some scope then none else s.storage.lookup owner := by
  simp only [State.retired,Store.lookup,List.getElem?_mapIdx]
  cases s.storage.objects[owner]? <;> simp

theorem retired_removed (s : State) (scope owner : Nat)
    (removed : s.forest.context owner = some scope) :
    (s.retired scope).storage.lookup owner = none := by
  rw [retired_lookup]; simp [removed]

theorem retired_kept (s : State) (scope owner : Nat)
    (kept : s.forest.context owner ≠ some scope) :
    (s.retired scope).storage.lookup owner = s.storage.lookup owner := by
  rw [retired_lookup]; simp [kept]

theorem retired_check (s : State) (scope owner : Nat) (good : s.check owner = true) :
    (s.retired scope).check owner = true := by
  have forest : (s.retired scope).forest = s.forest.retired scope := rfl
  by_cases removed : s.forest.context owner = some scope
  · simp only [State.check,forest,CppVectorOwnership.retired_same_context s.forest scope owner removed,
      retired_removed s scope owner removed]
  · simpa only [State.check,forest,CppVectorOwnership.retired_other_context s.forest scope owner removed,
      retired_kept s scope owner removed] using good

theorem retired_wellFormed (s : State) (scope : Nat) (valid : s.wellFormed = true) :
    (s.retired scope).wellFormed = true := by
  obtain ⟨lengths,forest,checks⟩ := wellFormed_parts s valid
  have nextForest := CppVectorOwnership.retired_wellFormed s.forest scope forest
  have nextChecks : (List.range (s.retired scope).storage.objects.length).all
      (s.retired scope).check = true := by
    rw [(retired_lengths s scope).2]
    apply List.all_eq_true.mpr
    intro owner member
    exact retired_check s scope owner (List.all_eq_true.mp checks owner member)
  simp only [State.wellFormed,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨by rw [(retired_lengths s scope).1,(retired_lengths s scope).2]; exact lengths,
    nextForest⟩,nextChecks⟩

theorem retireScope_valid_input (s : State) (scope : Nat) (valid : s.wellFormed = true) :
    s.retireScope scope = some (s.retired scope) := by
  simp [State.retireScope,valid,retired_wellFormed s scope valid]

theorem retired_invalidates (s : State) (scope : Nat) (reference : ElementRef)
    (accept : Value → Bool) (removed : s.forest.context reference.owner = some scope) :
    (s.retired scope).storage.readReference accept reference = none := by
  exact read_dead _ accept reference (retired_removed s scope reference.owner removed)

theorem retired_preserves_reference (s : State) (scope : Nat) (reference : ElementRef)
    (accept : Value → Bool) (kept : s.forest.context reference.owner ≠ some scope) :
    (s.retired scope).storage.readReference accept reference =
      s.storage.readReference accept reference := by
  simp only [Store.readReference,retired_kept s scope reference.owner kept]

theorem retired_id_not_reused (s : State) (scope owner work peak : Nat) (buffer : Buffer Value)
    (bound : owner < s.storage.objects.length) (removed : s.forest.context owner = some scope) :
    ((s.retired scope).storage.allocate buffer work peak).lookup owner = none := by
  apply allocate_preserves_dead
  · simpa only [(retired_lengths s scope).2] using bound
  · exact retired_removed s scope owner removed

theorem retired_cost (s : State) (scope : Nat) :
    (s.retired scope).storage.work = s.storage.work+s.destroyWork scope ∧
    (s.retired scope).storage.peak = max s.storage.peak (s.liveSpace-s.storage.baseSpace) ∧
    (s.retired scope).storage.baseSpace = s.storage.baseSpace := by
  exact ⟨rfl,rfl,rfl⟩

theorem retired_nodeSpace (s : State) (scope owner : Nat) :
    (s.retired scope).nodeSpace owner =
      if s.forest.context owner = some scope then 0 else s.nodeSpace owner := by
  have forest : (s.retired scope).forest = s.forest.retired scope := rfl
  by_cases removed : s.forest.context owner = some scope
  · simp [State.nodeSpace,forest,CppVectorOwnership.retired_same_context s.forest scope owner removed,
      retired_removed s scope owner removed,removed]
  · simp only [State.nodeSpace,forest,CppVectorOwnership.retired_other_context s.forest scope owner removed,
      retired_kept s scope owner removed,ite_eq_right removed]

theorem retired_space_le (s : State) (scope : Nat) :
    (s.retired scope).liveSpace ≤ s.liveSpace := by
  have each : ∀ owner, (s.retired scope).nodeSpace owner ≤ s.nodeSpace owner := by
    intro owner
    rw [retired_nodeSpace]
    split <;> omega
  have summed : ∀ owners : List Nat,
      (owners.map (s.retired scope).nodeSpace).sum ≤ (owners.map s.nodeSpace).sum := by
    intro owners
    induction owners with
    | nil => simp
    | cons owner tail ih =>
      simp only [List.map_cons,List.sum_cons]
      have h := each owner
      omega
  unfold State.liveSpace
  rw [(retired_lengths s scope).2]
  exact summed _

theorem retired_peak_bound (s : State) (scope : Nat) :
    (s.retired scope).liveSpace-(s.retired scope).storage.baseSpace ≤
      (s.retired scope).storage.peak := by
  have space := retired_space_le s scope
  have peak := Nat.le_max_right s.storage.peak (s.liveSpace-s.storage.baseSpace)
  change (s.retired scope).liveSpace-s.storage.baseSpace ≤
    max s.storage.peak (s.liveSpace-s.storage.baseSpace)
  omega

theorem check_transferred (s : State) (owner scope other : Nat) (tag : Tag)
    (found : s.forest.lookup owner = some tag) :
    ({s with forest := s.forest.transferred owner scope tag} : State).check other = s.check other := by
  by_cases same : other = owner
  · subst other
    simp only [State.check,CppVectorOwnership.transferred_lookup_root s.forest owner scope tag found,found]
    cases s.storage.lookup owner <;> rfl
  · simp only [State.check,CppVectorOwnership.transferred_lookup_other s.forest owner other scope tag same]

theorem wellFormed_transferred (s : State) (owner scope : Nat) (tag : Tag)
    (found : s.forest.lookup owner = some tag) (root : tag.parent = none)
    (oldScope : tag.scope.isSome = true) :
    ({s with forest := s.forest.transferred owner scope tag} : State).wellFormed = s.wellFormed := by
  have checks : ({s with forest := s.forest.transferred owner scope tag} : State).check = s.check := by
    funext other
    exact check_transferred s owner scope other tag found
  simp only [State.wellFormed,CppVectorOwnership.transferred_length,
    CppVectorOwnership.wellFormed_transferred s.forest owner scope tag found root oldScope,checks]

theorem transfer_valid_root (s : State) (owner : Nat) (expected : Element) (fromScope toScope : Nat)
    (tag : Tag) (valid : s.wellFormed = true) (found : s.forest.lookup owner = some tag)
    (root : tag.parent = none) (scope : tag.scope = some fromScope) (type : tag.element = expected) :
    s.transfer owner expected fromScope toScope =
      some {s with forest := s.forest.transferred owner toScope tag} := by
  have forest := (wellFormed_parts s valid).2.1
  simp [State.transfer,valid,
    CppVectorOwnership.transfer_valid_root s.forest owner expected fromScope toScope tag
      forest found root scope type]

theorem transferred_preserves_storage (s : State) (owner scope : Nat) (tag : Tag) :
    ({s with forest := s.forest.transferred owner scope tag} : State).storage = s.storage := rfl

theorem mismatched_payload (tag : Tag) (buffer : Buffer Value) (element : Element)
    (type : tag.element = .vector element)
    (mismatch : buffer.items ≠ tag.children.map Value.child) : ¬ payloadOK tag buffer := by
  simp [payloadOK,type,mismatch]

end Proofs.CppNestedVectorStore
