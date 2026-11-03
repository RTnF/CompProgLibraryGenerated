import Proofs.CppVectorRange

namespace Proofs.CppVectorStore
open Proofs.CppVector Proofs.CppVectorRange

-- Slots and tombstones are proof bookkeeping, not C++ storage. Owner IDs
-- are slot indices; destruction never truncates the list or reuses an ID.
structure Store (α : Type) where
  objects : List (Option (Buffer α)) := []
  work : Nat := 0
  peak : Nat := 0
  baseSpace : Nat := 0
deriving DecidableEq, Repr

def Store.lookup (s : Store α) (owner : Nat) : Option (Buffer α) :=
  (s.objects[owner]?).join

def Store.Valid (s : Store α) (accept : α → Bool) : Prop :=
  ∀ owner buffer, s.lookup owner = some buffer → buffer.owner = owner ∧ buffer.Valid accept

def footprint (buffer : Option (Buffer α)) : Nat :=
  match buffer with | none => 0 | some b => b.capacity+1

def Store.liveSpace (s : Store α) : Nat :=
  (s.objects.map footprint).sum

def Store.allocate (s : Store α) (buffer : Buffer α) (work peak : Nat) : Store α :=
  {s with objects := s.objects ++ [some {buffer with owner := s.objects.length}], work := s.work+work,peak := max s.peak (s.liveSpace+peak-s.baseSpace)}

def Store.construct (s : Store α) (accept : α → Bool) (limit count : Nat) (value : α) :
    Option (Store α × Nat) := do
  let result ← fill s.objects.length limit count value accept
  some (s.allocate result.buffer result.work result.peak,s.objects.length)

-- A successful primitive may change values, capacity and epoch, but cannot
-- change the lifetime's owner. Store adapters check that before committing.
def Store.commit (s : Store α) (owner : Nat) (accept : α → Bool)
    (result : Result α β) : Option (Store α × β) := do
  let old ← s.lookup owner
  if old.owner = owner ∧ result.buffer.owner = owner ∧ result.buffer.Valid accept ∧
      old.capacity+1 ≤ result.peak ∧ result.buffer.capacity+1 ≤ result.peak then
    some ({s with objects := s.objects.set owner (some result.buffer), work := s.work+result.work, peak := max s.peak (s.liveSpace+(result.peak-(old.capacity+1))-s.baseSpace)},result.value)
  else none

def Store.destroy (s : Store α) (owner : Nat) : Option (Store α) := do
  let old ← s.lookup owner
  if old.owner = owner then
    some {s with objects := s.objects.set owner none,work := s.work+1, peak := max s.peak (s.liveSpace-s.baseSpace)}
  else none

def Store.readReference (s : Store α) (accept : α → Bool) (reference : ElementRef) :
    Option (Result α α) := do
  let buffer ← s.lookup reference.owner
  readRef buffer accept reference

def Store.read (s : Store α) (accept : α → Bool) (reference : ElementRef) : Option (Store α × α) := do
  let result ← s.readReference accept reference
  s.commit reference.owner accept result

def Store.writeReference (s : Store α) (accept : α → Bool) (writable : Bool)
    (reference : ElementRef) (value : α) : Option (Store α × Unit) := do
  let buffer ← s.lookup reference.owner
  let result ← writeRef buffer accept writable reference value
  s.commit reference.owner accept result

def Store.reserve (s : Store α) (accept : α → Bool) (writable : Bool)
    (owner requested : Nat) : Option (Store α × Unit) := do
  let buffer ← s.lookup owner
  let result ← CppVector.reserve buffer accept writable requested
  s.commit owner accept result

def Store.appendReserved (s : Store α) (accept : α → Bool) (writable : Bool)
    (owner : Nat) (value : α) : Option (Store α × Unit) := do
  let buffer ← s.lookup owner
  let result ← CppVector.appendReserved buffer accept writable value
  s.commit owner accept result

def Store.assign (s : Store α) (accept : α → Bool) (writable : Bool)
    (targetOwner : Nat) (range : IteratorRange) : Option (Store α × Unit) := do
  let target ← s.lookup targetOwner
  let source ← s.lookup range.owner
  let result ← assignRange target source accept writable range
  s.commit targetOwner accept result

theorem lookup_allocate_old (s : Store α) (buffer : Buffer α) (work peak owner : Nat)
    (old : owner < s.objects.length) :
    (s.allocate buffer work peak).lookup owner = s.lookup owner := by
  simp [Store.lookup,Store.allocate,List.getElem?_append,old]

theorem lookup_allocate_new (s : Store α) (buffer : Buffer α) (work peak : Nat) :
    (s.allocate buffer work peak).lookup s.objects.length =
      some {buffer with owner := s.objects.length} := by
  simp [Store.lookup,Store.allocate]

theorem lookup_past_end (s : Store α) (owner : Nat) (past : s.objects.length ≤ owner) :
    s.lookup owner = none := by
  simp [Store.lookup,List.getElem?_eq_none_iff.mpr past]

theorem allocate_fresh (s : Store α) : s.lookup s.objects.length = none := by
  exact lookup_past_end s _ (Nat.le_refl _)

theorem allocate_length (s : Store α) (buffer : Buffer α) (work peak : Nat) :
    (s.allocate buffer work peak).objects.length = s.objects.length+1 := by
  simp [Store.allocate]

theorem allocate_valid (s : Store α) (buffer : Buffer α) (accept : α → Bool) (work peak : Nat)
    (valid : s.Valid accept) (bv : buffer.Valid accept) :
    (s.allocate buffer work peak).Valid accept := by
  intro owner found lookup
  by_cases old : owner < s.objects.length
  · rw [lookup_allocate_old s buffer work peak owner old] at lookup
    exact valid owner found lookup
  · by_cases equal : owner = s.objects.length
    · subst owner
      rw [lookup_allocate_new] at lookup
      cases lookup
      exact ⟨rfl,bv⟩
    · have past : (s.allocate buffer work peak).objects.length ≤ owner := by
        rw [allocate_length]; omega
      rw [lookup_past_end _ _ past] at lookup
      contradiction

theorem construct_runs (s : Store α) (accept : α → Bool) (limit count : Nat) (value : α)
    (bounded : count ≤ limit) (accepted : accept value = true) :
    s.construct accept limit count value = some
      (s.allocate ⟨s.objects.length,List.replicate count value,count,limit,0⟩ (count+1) (count+2),
       s.objects.length) := by
  simp [Store.construct,fill_runs _ _ _ _ _ bounded accepted]

theorem construct_valid (s : Store α) (accept : α → Bool) (limit count : Nat) (value : α)
    (valid : s.Valid accept) (bounded : count ≤ limit) (accepted : accept value = true) :
    (s.allocate ⟨s.objects.length,List.replicate count value,count,limit,0⟩ (count+1) (count+2)).Valid accept := by
  exact allocate_valid s _ accept _ _ valid (fill_valid _ _ _ _ _ bounded accepted)

theorem lookup_set_same (s : Store α) (owner : Nat) (buffer : Option (Buffer α))
    (bounded : owner < s.objects.length) :
    ({s with objects := s.objects.set owner buffer} : Store α).lookup owner = buffer := by
  simp [Store.lookup,List.getElem?_set_self bounded]

theorem lookup_set_other (s : Store α) (owner other : Nat) (buffer : Option (Buffer α))
    (different : owner ≠ other) :
    ({s with objects := s.objects.set owner buffer} : Store α).lookup other = s.lookup other := by
  simp [Store.lookup,List.getElem?_set_ne different]

theorem lookup_bound (s : Store α) (owner : Nat) (buffer : Buffer α)
    (lookup : s.lookup owner = some buffer) : owner < s.objects.length := by
  by_cases bound : owner < s.objects.length
  · exact bound
  · have past : s.objects.length ≤ owner := by omega
    rw [lookup_past_end s owner past] at lookup
    contradiction

theorem set_valid (s : Store α) (owner : Nat) (buffer : Option (Buffer α)) (accept : α → Bool)
    (valid : s.Valid accept) (bounded : owner < s.objects.length)
    (replacement : ∀ b, buffer = some b → b.owner = owner ∧ b.Valid accept) :
    ({s with objects := s.objects.set owner buffer} : Store α).Valid accept := by
  intro other found lookup
  by_cases equal : owner = other
  · subst other
    rw [lookup_set_same s owner buffer bounded] at lookup
    exact replacement found lookup
  · rw [lookup_set_other s owner other buffer equal] at lookup
    exact valid other found lookup

theorem destroy_runs (s : Store α) (owner : Nat) (buffer : Buffer α)
    (lookup : s.lookup owner = some buffer) (owns : buffer.owner = owner) :
    s.destroy owner = some {s with objects := s.objects.set owner none,work := s.work+1, peak := max s.peak (s.liveSpace-s.baseSpace)} := by
  simp [Store.destroy,lookup,owns]

theorem destroy_valid (s : Store α) (owner : Nat) (accept : α → Bool)
    (valid : s.Valid accept) (bounded : owner < s.objects.length) :
    ({s with objects := s.objects.set owner none} : Store α).Valid accept := by
  apply set_valid s owner none accept valid bounded
  simp

theorem destroy_invalidates (s : Store α) (owner : Nat) (accept : α → Bool) (epoch index : Nat)
    (bounded : owner < s.objects.length) :
    ({s with objects := s.objects.set owner none} : Store α).readReference accept
      ⟨owner,epoch,index⟩ = none := by
  simp [Store.readReference,lookup_set_same s owner none bounded]

theorem destroyed_id_not_reused (s : Store α) (owner : Nat) (buffer : Buffer α)
    (work peak : Nat) (bounded : owner < s.objects.length) :
    (({s with objects := s.objects.set owner none} : Store α).allocate buffer work peak).lookup owner = none := by
  have old : owner < (s.objects.set owner none).length := by simpa using bounded
  rw [lookup_allocate_old _ buffer work peak owner old]
  exact lookup_set_same s owner none bounded

theorem commit_runs (s : Store α) (owner : Nat) (accept : α → Bool) (old : Buffer α)
    (result : Result α β) (lookup : s.lookup owner = some old) (owns : old.owner = owner)
    (same : result.buffer.owner = owner) (valid : result.buffer.Valid accept)
    (oldPeak : old.capacity+1 ≤ result.peak) (newPeak : result.buffer.capacity+1 ≤ result.peak) :
    s.commit owner accept result = some ({s with objects := s.objects.set owner (some result.buffer), work := s.work+result.work, peak := max s.peak (s.liveSpace+(result.peak-(old.capacity+1))-s.baseSpace)},result.value) := by
  simp [Store.commit,lookup,owns,same,valid,oldPeak,newPeak]

theorem commit_valid (s : Store α) (owner : Nat) (accept : α → Bool) (result : Result α β)
    (valid : s.Valid accept) (bounded : owner < s.objects.length)
    (same : result.buffer.owner = owner) (bv : result.buffer.Valid accept) :
    ({s with objects := s.objects.set owner (some result.buffer)} : Store α).Valid accept := by
  apply set_valid s owner (some result.buffer) accept valid bounded
  intro buffer equal
  cases equal
  exact ⟨same,bv⟩

theorem empty_valid (accept : α → Bool) : (⟨[],0,0,0⟩ : Store α).Valid accept := by
  intro owner buffer lookup
  simp [Store.lookup] at lookup

theorem allocate_space (s : Store α) (buffer : Buffer α) (work peak : Nat) :
    (s.allocate buffer work peak).liveSpace = s.liveSpace+buffer.capacity+1 := by
  simp [Store.liveSpace,Store.allocate,footprint,Nat.add_assoc]

theorem allocate_cost (s : Store α) (buffer : Buffer α) (work peak : Nat) :
    (s.allocate buffer work peak).work = s.work+work ∧
    (s.allocate buffer work peak).peak = max s.peak (s.liveSpace+peak-s.baseSpace) := by
  exact ⟨rfl,rfl⟩

theorem set_length (s : Store α) (owner : Nat) (buffer : Option (Buffer α)) :
    ({s with objects := s.objects.set owner buffer} : Store α).objects.length = s.objects.length := by
  simp

theorem commit_dead (s : Store α) (owner : Nat) (accept : α → Bool) (result : Result α β)
    (dead : s.lookup owner = none) : s.commit owner accept result = none := by
  simp [Store.commit,dead]

theorem commit_wrong_owner (s : Store α) (owner : Nat) (accept : α → Bool) (result : Result α β)
    (wrong : result.buffer.owner ≠ owner) : s.commit owner accept result = none := by
  simp [Store.commit,wrong]

theorem read_dead (s : Store α) (accept : α → Bool) (reference : ElementRef)
    (dead : s.lookup reference.owner = none) : s.readReference accept reference = none := by
  simp [Store.readReference,dead]

theorem allocate_preserves_dead (s : Store α) (buffer : Buffer α) (work peak owner : Nat)
    (old : owner < s.objects.length) (dead : s.lookup owner = none) :
    (s.allocate buffer work peak).lookup owner = none := by
  rw [lookup_allocate_old s buffer work peak owner old,dead]

theorem replace_space (objects : List (Option (Buffer α))) (owner : Nat)
    (old replacement : Option (Buffer α)) (lookup : objects[owner]? = some old) :
    ((objects.set owner replacement).map footprint).sum + footprint old =
      (objects.map footprint).sum + footprint replacement := by
  induction objects generalizing owner with
  | nil => simp at lookup
  | cons head tail ih =>
      cases owner with
      | zero =>
          simp at lookup
          subst old
          simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      | succ index =>
          simp only [List.getElem?_cons_succ] at lookup
          have h := ih index lookup
          simp only [List.set_cons_succ,List.map_cons,List.sum_cons]
          omega

theorem present_space (s : Store α) (owner : Nat) (old : Buffer α)
    (lookup : s.objects[owner]? = some (some old)) : old.capacity+1 ≤ s.liveSpace := by
  have h := replace_space s.objects owner (some old) none lookup
  simp only [footprint,Store.liveSpace] at h ⊢
  omega

theorem update_space (s : Store α) (owner : Nat) (old replacement : Buffer α)
    (lookup : s.objects[owner]? = some (some old)) :
    ({s with objects := s.objects.set owner (some replacement)} : Store α).liveSpace+old.capacity+1 =
      s.liveSpace+replacement.capacity+1 := by
  have h := replace_space s.objects owner (some old) (some replacement) lookup
  simpa [Store.liveSpace,footprint,Nat.add_assoc] using h

theorem update_peak_bound (s : Store α) (owner : Nat) (old : Buffer α) (result : Result α β)
    (lookup : s.objects[owner]? = some (some old))
    (oldPeak : old.capacity+1 ≤ result.peak) (newPeak : result.buffer.capacity+1 ≤ result.peak) :
    ({s with objects := s.objects.set owner (some result.buffer)} : Store α).liveSpace-s.baseSpace ≤
      max s.peak (s.liveSpace+(result.peak-(old.capacity+1))-s.baseSpace) := by
  have present := present_space s owner old lookup
  have replacement := update_space s owner old result.buffer lookup
  have upper := Nat.le_max_right s.peak (s.liveSpace+(result.peak-(old.capacity+1))-s.baseSpace)
  omega

theorem commit_peak_too_small (s : Store α) (owner : Nat) (accept : α → Bool) (result : Result α β)
    (small : result.peak < result.buffer.capacity+1) : s.commit owner accept result = none := by
  have h : ¬ result.buffer.capacity+1 ≤ result.peak := by omega
  simp [Store.commit,h]

end Proofs.CppVectorStore
