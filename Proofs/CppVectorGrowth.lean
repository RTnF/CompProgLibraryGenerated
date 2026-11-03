import Proofs.CppVector

namespace Proofs.CppVectorGrowth
open Proofs.CppVector

-- Explicit growth policy for the fixed libstdc++ target: double the size,
-- starting at one, and saturate at max_size. Allocation success is assumed.
def nextCapacity (b : Buffer α) : Nat :=
  min b.limit (max 1 (2 * b.items.length))

def append (b : Buffer α) (accept : α → Bool) (writable : Bool)
    (value : α) : Option (Result α Unit) :=
  if b.Valid accept ∧ writable = true ∧ accept value = true ∧ b.items.length < b.limit then
    if b.items.length < b.capacity then
      some ⟨{b with items := b.items ++ [value]}, (), 2, b.capacity + 2⟩
    else
      some ⟨{b with items := b.items ++ [value], capacity := nextCapacity b, epoch := b.epoch + 1}, (), b.items.length + 3, b.capacity + nextCapacity b + 2⟩
  else none

-- At max_size no further reallocation is possible. Erasing the remaining
-- credit there also pays for a final, smaller-than-doubling reallocation.
def potential (b : Buffer α) : Nat :=
  if b.capacity = b.limit then 0 else 2 * b.items.length - b.capacity

theorem next_bounds (b : Buffer α) (room : b.items.length < b.limit) :
    b.items.length < nextCapacity b ∧ nextCapacity b ≤ b.limit ∧
      nextCapacity b ≤ 2 * b.items.length + 1 := by
  unfold nextCapacity
  omega

theorem append_keep (b : Buffer α) (accept : α → Bool) (value : α)
    (valid : b.Valid accept) (accepted : accept value = true)
    (space : b.items.length < b.capacity) :
    append b accept true value = appendReserved b accept true value := by
  have room : b.items.length < b.limit := by have := valid.2.1; omega
  simp [append, appendReserved, valid, accepted, space, room]

theorem append_reserved_success (b : Buffer α) (accept : α → Bool) (writable : Bool)
    (value : α) (r : Result α Unit)
    (run : appendReserved b accept writable value = some r) :
    append b accept writable value = some r := by
  unfold appendReserved at run
  split at run
  · rename_i h
    have room : b.items.length < b.limit := by have := h.1.2.1; omega
    simpa [append, h.1, h.2.1, h.2.2.1, h.2.2.2, room] using run
  · contradiction

theorem append_grow (b : Buffer α) (accept : α → Bool) (value : α)
    (valid : b.Valid accept) (accepted : accept value = true)
    (full : b.items.length = b.capacity) (room : b.items.length < b.limit) :
    append b accept true value = some ⟨{b with items := b.items ++ [value], capacity := nextCapacity b, epoch := b.epoch + 1}, (), b.items.length + 3,
      b.capacity + nextCapacity b + 2⟩ := by
  simp only [append, valid, accepted, room, and_self, ite_true]
  simp [full]

theorem append_spec (b : Buffer α) (accept : α → Bool) (value : α)
    (valid : b.Valid accept) (accepted : accept value = true)
    (room : b.items.length < b.limit) :
    ∃ r, append b accept true value = some r ∧ r.buffer.Valid accept ∧
      r.buffer.items = b.items ++ [value] ∧ r.buffer.owner = b.owner ∧
      r.buffer.limit = b.limit ∧
      r.work + potential r.buffer ≤ potential b + 5 ∧
      r.peak ≤ 3 * b.capacity + 3 ∧
      (if b.items.length < b.capacity then r.buffer.epoch = b.epoch
       else r.buffer.epoch = b.epoch + 1) := by
  by_cases space : b.items.length < b.capacity
  · refine ⟨⟨{b with items := b.items ++ [value]}, (), 2, b.capacity + 2⟩, ?_,
      append_preserves_valid b accept value valid accepted space, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [append, valid, accepted, room, space]
    · simp only [potential, List.length_append, List.length_cons, List.length_nil]
      split <;> omega
    · dsimp; omega
    · simp [space]
  · have full : b.items.length = b.capacity := by have := valid.1; omega
    have bounds := next_bounds b room
    refine ⟨⟨{b with items := b.items ++ [value], capacity := nextCapacity b, epoch := b.epoch + 1}, (), b.items.length + 3, b.capacity + nextCapacity b + 2⟩,
      append_grow b accept value valid accepted full room, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · exact ⟨by dsimp; simp only [List.length_append, List.length_cons, List.length_nil]; omega, bounds.2.1, by simp [valid.2.2, accepted]⟩
    · have old : b.capacity ≠ b.limit := by omega
      simp only [potential, old, ite_false, List.length_append, List.length_cons, List.length_nil]
      by_cases last : nextCapacity b = b.limit
      · simp only [last, ite_true]; omega
      · simp only [last, ite_false]
        have growth : nextCapacity b = max 1 (2 * b.items.length) := by
          unfold nextCapacity at *
          omega
        omega
    · dsimp; omega
    · simp [space]

theorem append_readonly (b : Buffer α) (accept : α → Bool) (value : α) :
    append b accept false value = none := by simp [append]

theorem append_at_limit (b : Buffer α) (accept : α → Bool) (writable : Bool) (value : α)
    (full : b.limit ≤ b.items.length) : append b accept writable value = none := by
  have h : ¬ b.items.length < b.limit := by omega
  simp [append, h]

theorem append_rejected (b : Buffer α) (accept : α → Bool) (writable : Bool) (value : α)
    (rejected : accept value = false) : append b accept writable value = none := by
  simp [append, rejected]

theorem grow_invalidates (b : Buffer α) (accept : α → Bool) (value : α) (index : Nat) :
    readRef ({b with items := b.items ++ [value], capacity := nextCapacity b, epoch := b.epoch + 1} : Buffer α) accept ⟨b.owner, b.epoch, index⟩ = none := by
  apply readRef_stale
  dsimp
  omega

-- A successful sequence telescopes the per-append credit inequality. This
-- allows arbitrary initial capacity; an empty buffer has zero initial credit.
inductive Appends (accept : α → Bool) : Buffer α → List α → Buffer α → Nat → Prop where
  | nil (b) : Appends accept b [] b 0
  | cons {b mid final values cost} (value : α) (r : Result α Unit)
      (run : append b accept true value = some r) (next : r.buffer = mid)
      (valid : b.Valid accept) (accepted : accept value = true)
      (room : b.items.length < b.limit)
      (tail : Appends accept mid values final cost) :
      Appends accept b (value :: values) final (r.work + cost)

theorem appends_work {accept : α → Bool} {b final : Buffer α} {values : List α} {cost : Nat}
    (runs : Appends accept b values final cost) :
    cost + potential final ≤ 5 * values.length + potential b := by
  induction runs with
  | nil => simp
  | cons value r run next valid accepted room tail ih =>
    obtain ⟨s, hs, _, _, _, _, amort, _, _⟩ := append_spec _ _ value valid accepted room
    have eq : s = r := Option.some.inj (hs.symm.trans run)
    subst s
    subst next
    simp only [List.length_cons]
    omega

theorem appends_exist (b : Buffer α) (accept : α → Bool) (values : List α)
    (valid : b.Valid accept) (accepted : values.all accept = true)
    (room : b.items.length + values.length ≤ b.limit) :
    ∃ final cost, Appends accept b values final cost ∧ final.Valid accept ∧
      final.items = b.items ++ values ∧ final.limit = b.limit := by
  induction values generalizing b with
  | nil => exact ⟨b, 0, Appends.nil b, valid, by simp, rfl⟩
  | cons value values ih =>
    simp only [List.all_cons, Bool.and_eq_true] at accepted
    have hv : accept value = true := accepted.1
    have ht : values.all accept = true := accepted.2
    have stepRoom : b.items.length < b.limit := by simp only [List.length_cons] at room; omega
    obtain ⟨r, run, rv, ri, _, rl, _, _, _⟩ := append_spec b accept value valid hv stepRoom
    have tailRoom : r.buffer.items.length + values.length ≤ r.buffer.limit := by
      rw [ri, rl]
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
    obtain ⟨final, cost, runs, fv, fi, fl⟩ := ih r.buffer rv ht tailRoom
    refine ⟨final, r.work + cost,
      Appends.cons value r run rfl valid hv stepRoom runs, fv, ?_, fl.trans rl⟩
    rw [fi, ri]
    simp [List.append_assoc]

theorem empty_appends_linear (b : Buffer α) (accept : α → Bool) (values : List α)
    (valid : b.Valid accept) (empty : b.items = []) (accepted : values.all accept = true)
    (room : values.length ≤ b.limit) :
    ∃ final cost, Appends accept b values final cost ∧ final.Valid accept ∧
      final.items = values ∧ cost ≤ 5 * values.length := by
  obtain ⟨final, cost, runs, fv, fi, _⟩ :=
    appends_exist b accept values valid accepted (by simpa [empty] using room)
  have bound := appends_work runs
  have credit : potential b = 0 := by simp [potential, empty]
  refine ⟨final, cost, runs, fv, by simpa [empty] using fi, ?_⟩
  omega

end Proofs.CppVectorGrowth
