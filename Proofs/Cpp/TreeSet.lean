import Proofs.Cpp.Gen.TreeSet
import Mathlib.Order.Basic

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def less [LT T] [DecidableLT T] (a b : T) : Bool := decide (a < b)

theorem constructed_empty {T : Type} (clock : Nat) :
    (cp.TreeSet.init (T := T)).run clock = some (⟨[]⟩, clock + 1) := rfl

theorem insert_run {T : Type} [LT T] [DecidableLT T] (s : cp.TreeSet T) (key : T) (clock : Nat) :
    (cp.TreeSet.add s key).run clock =
      some (⟨insertOrdered less key s.values⟩, clock + 1 + orderedSetLookupCost s.values.length) := by
  cases s
  rfl

theorem erase_run {T : Type} [LT T] [DecidableLT T] (s : cp.TreeSet T) (key : T) (clock : Nat) :
    (cp.TreeSet.remove s key).run clock =
      some (⟨eraseOrdered less key s.values⟩, clock + 1 + (orderedSetLookupCost s.values.length + 1)) := by
  cases s
  rfl

theorem lookup_run {T : Type} [LT T] [DecidableLT T] (s : cp.TreeSet T) (key : T) (clock : Nat) :
    (cp.TreeSet.find s key).run clock =
      some ((s.values.any (equivalentKey less key), s), clock + 1 + (orderedSetLookupCost s.values.length + 1)) := by
  cases s with
  | mk values =>
    change some ((decide ((if values.any (equivalentKey less key) then 1 else 0 : UInt64) ≠ 0), _), _) = _
    generalize values.any (equivalentKey less key) = b
    cases b <;> rfl

theorem min_run {T : Type} (s : cp.TreeSet T) (key : T) (hasKey : s.values.head? = some key)
    (clock : Nat) : (cp.TreeSet.min_ s).run clock = some ((key, s), clock + 2) := by
  cases s with
  | mk values =>
    simp only [cp.TreeSet.min_, orderedSetFirst, StateT.run_bind, tick, StateT.run_pure] at *
    rw [hasKey]
    rfl

theorem max_run {T : Type} (s : cp.TreeSet T) (key : T) (hasKey : s.values.getLast? = some key)
    (clock : Nat) : (cp.TreeSet.max_ s).run clock = some ((key, s), clock + 2) := by
  cases s with
  | mk values =>
    simp only [cp.TreeSet.max_, orderedSetLast, StateT.run_bind, tick, StateT.run_pure] at *
    rw [hasKey]
    rfl

theorem size_run {T : Type} (s : cp.TreeSet T) (fits : s.values.length < 2 ^ 31) (clock : Nat) :
    (cp.TreeSet.size_ s).run clock = some ((Int.ofNat s.values.length, s), clock + 1) := by
  cases s with
  | mk values =>
    change some ((Cpp.toSigned 32 (UInt64.ofNat values.length).toNat, _), _) = _
    change values.length < 2 ^ 31 at fits
    have fit64 : values.length < 2 ^ 64 := by omega
    have fit32 : values.length < 2 ^ 32 := by omega
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt fit64]
    simp [Cpp.toSigned, Nat.mod_eq_of_lt fit32, fits]

theorem insert_slots {T : Type} (lt : T → T → Bool) (key : T) (values : List T) :
    (insertOrdered lt key values).length ≤ values.length + 1 := by
  induction values with
  | nil => simp [insertOrdered]
  | cons head tail ih =>
    unfold insertOrdered
    split
    · simp
    · split <;> simp_all

theorem erase_slots {T : Type} (lt : T → T → Bool) (key : T) (values : List T) :
    (eraseOrdered lt key values).length ≤ values.length := List.length_filter_le ..

section Order

variable {T : Type} [LinearOrder T]

theorem equivalent_iff (a b : T) : equivalentKey less a b = true ↔ a = b := by
  simp only [equivalentKey, less, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · intro h
    exact le_antisymm (le_of_not_gt h.2) (le_of_not_gt h.1)
  · rintro rfl
    simp

theorem mem_insert (key x : T) (values : List T) :
    x ∈ insertOrdered less key values ↔ x = key ∨ x ∈ values := by
  induction values with
  | nil => simp [insertOrdered]
  | cons head tail ih =>
    by_cases first : key < head
    · simp [insertOrdered, less, first]
    · by_cases later : head < key
      · simp only [insertOrdered, less, first, decide_false, Bool.false_eq_true, ite_false, later, decide_true,
          ite_true, List.mem_cons, ih]
        exact or_left_comm
      · have eq : key = head := le_antisymm (le_of_not_gt later) (le_of_not_gt first)
        simp [insertOrdered, less, eq]

theorem mem_erase (key x : T) (values : List T) :
    x ∈ eraseOrdered less key values ↔ x ∈ values ∧ x ≠ key := by
  simp only [eraseOrdered, List.mem_filter, Bool.not_eq_true']
  rw [← Bool.not_eq_true, not_congr (equivalent_iff key x)]
  simp [eq_comm]

theorem insert_ordered (key : T) (values : List T) (ordered : values.Pairwise (· < ·)) :
    (insertOrdered less key values).Pairwise (· < ·) := by
  induction values with
  | nil => simp [insertOrdered]
  | cons head tail ih =>
    have relation := List.pairwise_cons.mp ordered
    by_cases first : key < head
    · simp only [insertOrdered, less, first, decide_true, ite_true, List.pairwise_cons]
      exact ⟨fun x h => (List.mem_cons.mp h).elim (fun eq => eq ▸ first)
        (fun mem => lt_trans first (relation.1 _ mem)), relation⟩
    · by_cases later : head < key
      · simp only [insertOrdered, less, first, decide_false, Bool.false_eq_true, ite_false,
          later, decide_true, ite_true, List.pairwise_cons]
        exact ⟨fun x h => (mem_insert key x tail).mp h |>.elim (fun eq => eq ▸ later)
          (fun mem => relation.1 _ mem), ih relation.2⟩
      · simpa [insertOrdered, less, first, later] using ordered

theorem erase_ordered (key : T) (values : List T) (ordered : values.Pairwise (· < ·)) :
    (eraseOrdered less key values).Pairwise (· < ·) :=
  ordered.sublist List.filter_sublist

theorem query_membership (s : cp.TreeSet T) (key : T) (clock : Nat) :
    (cp.TreeSet.find s key).run clock =
      some ((decide (key ∈ s.values), s), clock + 1 + (orderedSetLookupCost s.values.length + 1)) := by
  rw [lookup_run]
  have same : s.values.any (equivalentKey less key) = decide (key ∈ s.values) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq, equivalent_iff]
    constructor
    · rintro ⟨value, member, eq⟩
      rwa [eq]
    · exact fun member => ⟨key, member, rfl⟩
  rw [same]

theorem first_is_minimum (values : List T) (ordered : values.Pairwise (· < ·))
    (key : T) (first : values.head? = some key) :
    key ∈ values ∧ ∀ other ∈ values, key ≤ other := by
  cases values with
  | nil => simp at first
  | cons head tail =>
    simp only [List.head?_cons, Option.some.injEq] at first
    subst head
    refine ⟨List.mem_cons_self .., ?_⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | more
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp ordered).1 other more)

theorem last_is_maximum (values : List T) (ordered : values.Pairwise (· < ·))
    (key : T) (last : values.getLast? = some key) :
    key ∈ values ∧ ∀ other ∈ values, other ≤ key := by
  obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp last
  refine ⟨by simp, ?_⟩
  intro other member
  rcases List.mem_append.mp member with left | right
  · exact le_of_lt ((List.pairwise_append.mp ordered).2.2 other left key (by simp))
  · have eq : other = key := by simpa using right
    exact eq.le

theorem add_spec (s : cp.TreeSet T) (key : T) (sorted : s.values.Pairwise (· < ·)) (clock : Nat) :
    ∃ out, (cp.TreeSet.add s key).run clock =
        some (out, clock + 1 + orderedSetLookupCost s.values.length) ∧
      out.values.Pairwise (· < ·) ∧
      (∀ x, x ∈ out.values ↔ x = key ∨ x ∈ s.values) ∧
      out.values.length ≤ s.values.length + 1 := by
  exact ⟨⟨insertOrdered less key s.values⟩, insert_run s key clock, insert_ordered key s.values sorted,
    fun x => mem_insert key x s.values, insert_slots less key s.values⟩

theorem remove_spec (s : cp.TreeSet T) (key : T) (sorted : s.values.Pairwise (· < ·)) (clock : Nat) :
    ∃ out, (cp.TreeSet.remove s key).run clock =
        some (out, clock + 1 + (orderedSetLookupCost s.values.length + 1)) ∧
      out.values.Pairwise (· < ·) ∧
      (∀ x, x ∈ out.values ↔ x ∈ s.values ∧ x ≠ key) ∧
      out.values.length ≤ s.values.length := by
  exact ⟨⟨eraseOrdered less key s.values⟩, erase_run s key clock, erase_ordered key s.values sorted,
    fun x => mem_erase key x s.values, erase_slots less key s.values⟩

theorem min_spec (s : cp.TreeSet T) (sorted : s.values.Pairwise (· < ·)) (nonempty : s.values ≠ [])
    (clock : Nat) :
    ∃ key, (cp.TreeSet.min_ s).run clock = some ((key, s), clock + 2) ∧
      key ∈ s.values ∧ ∀ other ∈ s.values, key ≤ other := by
  cases s with
  | mk values =>
    cases values with
    | nil => exact False.elim (nonempty rfl)
    | cons head tail =>
      exact ⟨head, min_run _ _ rfl clock, first_is_minimum _ sorted _ rfl⟩

theorem max_spec (s : cp.TreeSet T) (sorted : s.values.Pairwise (· < ·)) (nonempty : s.values ≠ [])
    (clock : Nat) :
    ∃ key, (cp.TreeSet.max_ s).run clock = some ((key, s), clock + 2) ∧
      key ∈ s.values ∧ ∀ other ∈ s.values, other ≤ key := by
  let key := s.values.getLast nonempty
  have last : s.values.getLast? = some key := List.getLast?_eq_some_getLast nonempty
  exact ⟨key, max_run s key last clock, last_is_maximum _ sorted key last⟩

end Order
end Proofs.Cpp.TreeSet
