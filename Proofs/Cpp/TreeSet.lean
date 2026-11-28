import Proofs.Cpp.Gen.TreeSet
import Proofs.Cpp.TreeSet.Copy
import Proofs.Cpp.Lib.OrderedSet

open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def less [LT T] [DecidableLT T] (a b : T) : Bool := decide (a < b)

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

-- Preserve the direct LinearOrder projections in the existing list contracts.
attribute [local instance 2000] LinearOrder.toPartialOrder

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

end Order

theorem constructed_empty {K : Type} (clock : Nat) :
    (cp.TreeSet.init (T := K)).run clock = some (⟨List.toArray [], endIndex, endIndex⟩, clock + 3) := by
  exact generated_init clock

theorem add_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (tree : Tree K) (key : K) (used free : List Nat)
    (layout : Layout arena.slots arena.root tree used) (available : FreeChain arena.slots arena.free_head free)
    (balanced : tree.Balanced) (ordered : tree.Ordered) (fits : arena.slots.size < 2 ^ 63) (start : Nat) :
    ∃ next occupied remaining stop, (cp.TreeSet.add arena key).run start = some (next, stop) ∧
      stop ≤ start + 9 + 57 * (2 * (tree.size + 1).log2 + 1) ∧
      Layout next.slots next.root (tree.insert key) occupied ∧
      FreeChain next.slots next.free_head remaining ∧ next.slots.size ≤ arena.slots.size + 1 ∧
      (tree.insert key).Balanced ∧ (tree.insert key).Ordered ∧
      (∀ k, k ∈ (tree.insert key).keys ↔ k = key ∨ k ∈ tree.keys) := by
  exact generated_add_spec arena tree key used free layout available balanced ordered fits start

theorem remove_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (tree : Tree K) (key : K) (used free : List Nat)
    (layout : Layout arena.slots arena.root tree used) (available : FreeChain arena.slots arena.free_head free)
    (balanced : tree.Balanced) (ordered : tree.Ordered) (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ next occupied remaining stop, (cp.TreeSet.remove arena key).run start = some (next, stop) ∧
      stop ≤ start + 7 + 57 * (2 * (tree.size + 1).log2 + 1) ∧
      Layout next.slots next.root (tree.erase key) occupied ∧
      FreeChain next.slots next.free_head remaining ∧ next.slots.size = arena.slots.size ∧
      (tree.erase key).Balanced ∧ (tree.erase key).Ordered ∧
      (tree.erase key).keys = tree.keys.filter (fun k => decide (k ≠ key)) := by
  exact generated_remove_spec arena tree key used free layout available balanced ordered fits start

theorem find_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (key : K) (tree : Tree K) (used : List Nat)
    (layout : Layout arena.slots arena.root tree used) (fits : arena.slots.size ≤ 2 ^ 63)
    (balanced : tree.Balanced) (ordered : tree.Ordered) (start : Nat) :
    ∃ stop, (cp.TreeSet.find arena key).run start = some ((decide (key ∈ tree.keys), arena), stop) ∧
      stop ≤ start + 3 + 2 * (2 * (tree.size + 1).log2 + 1) := by
  exact generated_find_spec arena key tree used layout fits balanced ordered start

theorem rank_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (key : K) (tree : Tree K) (occupied : List Nat)
    (layout : Layout arena.slots arena.root tree occupied)
    (fits : tree.size < 2 ^ 31) (balanced : tree.Balanced) (ordered : tree.Ordered) (start : Nat) :
    ∃ result stop, (cp.TreeSet.rank arena key).run start = some (result, stop) ∧
      stop ≤ start + 3 + 4 * (2 * (tree.size + 1).log2 + 1) ∧
      result = if key ∈ tree.keys then rankBounds ((tree.keys.filter (fun k => decide (k < key))).length)
        else (-1, -1) := by
  exact generated_rank_spec arena key tree occupied layout fits balanced ordered start

theorem get_kth_spec {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (tree : Tree K) (used : List Nat) (position : UInt64)
    (layout : Layout arena.slots arena.root tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (valid : position.toNat < tree.size)
    (balanced : tree.Balanced) (start : Nat) :
    ∃ key stop, (cp.TreeSet.get_kth arena position).run start = some (key, stop) ∧
      stop ≤ start + 3 + 3 * (2 * (tree.size + 1).log2 + 1) ∧ tree.keys[position.toNat]? = some key := by
  exact generated_get_kth_spec arena tree used position layout fits valid balanced start

theorem neighbors_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (key : K) (tree : Tree K) (occupied : List Nat)
    (layout : Layout arena.slots arena.root tree occupied) (fits : tree.size < 2 ^ 31)
    (balanced : tree.Balanced) (ordered : tree.Ordered) (start : Nat) :
    let work := 5 + 2 * (2 * (tree.size + 1).log2 + 1)
    (∃ lowerStop, (cp.TreeSet.find_lower arena key).run start =
      some ((tree.keys.filter (fun k => decide (k ≤ key))).getLast?, lowerStop) ∧
      lowerStop ≤ start + work) ∧
    (∃ upperStop, (cp.TreeSet.find_upper arena key).run start =
      some ((tree.keys.filter (fun k => decide (key ≤ k))).head?, upperStop) ∧
      upperStop ≤ start + work) := by
  exact generated_neighbors_spec arena key tree occupied layout fits balanced ordered start

theorem extrema_spec {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (tree : Tree K) (used : List Nat) (layout : Layout arena.slots arena.root tree used)
    (nonempty : tree ≠ .empty) (start : Nat) :
    ∃ lo hi, tree.keys.head? = some lo ∧ tree.keys.getLast? = some hi ∧
      (cp.TreeSet.min_ arena).run start = some ((lo, arena), start + 2) ∧
      (cp.TreeSet.max_ arena).run start = some ((hi, arena), start + 2) := by
  exact generated_extrema_spec arena tree used layout nonempty start

theorem min_spec {K : Type} [Inhabited K] [LinearOrder K] (arena : cp.TreeSet K)
    (tree : Tree K) (used : List Nat) (layout : Layout arena.slots arena.root tree used)
    (nonempty : tree ≠ .empty) (ordered : tree.Ordered) (start : Nat) :
    ∃ minimum, (cp.TreeSet.min_ arena).run start = some ((minimum, arena), start + 2) ∧
      minimum ∈ tree.keys ∧ ∀ key ∈ tree.keys, minimum ≤ key := by
  obtain ⟨minimum, _, first, _, ran, _⟩ := extrema_spec arena tree used layout nonempty start
  exact ⟨minimum, ran, first_is_minimum tree.keys ordered minimum first⟩

theorem max_spec {K : Type} [Inhabited K] [LinearOrder K] (arena : cp.TreeSet K)
    (tree : Tree K) (used : List Nat) (layout : Layout arena.slots arena.root tree used)
    (nonempty : tree ≠ .empty) (ordered : tree.Ordered) (start : Nat) :
    ∃ maximum, (cp.TreeSet.max_ arena).run start = some ((maximum, arena), start + 2) ∧
      maximum ∈ tree.keys ∧ ∀ key ∈ tree.keys, key ≤ maximum := by
  obtain ⟨_, maximum, _, last, _, ran⟩ := extrema_spec arena tree used layout nonempty start
  exact ⟨maximum, ran, last_is_maximum tree.keys ordered maximum last⟩

theorem size_spec {K : Type} [Inhabited K] (arena : cp.TreeSet K)
    (tree : Tree K) (used : List Nat) (layout : Layout arena.slots arena.root tree used)
    (fits : tree.size < 2 ^ 31) (start : Nat) :
    (cp.TreeSet.size_ arena).run start = some (((tree.size : Int), arena), start + 3) := by
  exact generated_size_spec arena tree used layout fits start

theorem copy_spec {K : Type} [Inhabited K] (source : cp.TreeSet K)
    (fits : source.slots.size ≤ 2 ^ 63) (start : Nat) :
    (cp.TreeSet.init_copy source).run start = some (source, start + 5 + 2 * source.slots.size) := by
  exact generated_copy_spec source fits start

theorem move_spec {K : Type} (source : cp.TreeSet K) (start : Nat) :
    (cp.TreeSet.init_move source).run start =
      some ((source, ⟨(List.toArray []), endIndex, endIndex⟩), start + 4) := by
  exact generated_move_spec source start

theorem copy_assignment_spec {K : Type} [Inhabited K] (target source : cp.TreeSet K)
    (fits : source.slots.size ≤ 2 ^ 63) (start : Nat) :
    (cp.TreeSet.op_assign_copy target source).run start =
      some ((source, source), start + 8 + 2 * source.slots.size) := by
  exact generated_copy_assignment_spec target source fits start

theorem move_assignment_spec {K : Type} (target source : cp.TreeSet K) (start : Nat) :
    (cp.TreeSet.op_assign_move target source).run start = some ((source, target, source), start + 2) := by
  exact generated_move_assignment_spec target source start

end Proofs.Cpp.TreeSet
