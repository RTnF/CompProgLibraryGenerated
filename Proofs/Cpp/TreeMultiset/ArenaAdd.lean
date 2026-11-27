import Proofs.Cpp.TreeMultiset.InsertLayout

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

structure ArenaContents {K : Type} (arena : cp.TreeMultiSet K) (tree : Tree K) where
  live : List Nat
  free : List Nat
  treeLayout : Realizes (storageView arena) (decode arena.root) tree live
  freeLayout : FreeSlots (storageView arena) (decode arena.free_head) free
  covers : ∀ i, i < arena.slots.size → i ∈ live ++ free

private theorem free_shape {K : Type} {storage : Array (StoredNode K)} {head : Option Nat}
    {free : List Nat} (layout : FreeSlots storage head free) : free = [] ↔ head = none := by
  cases layout <;> simp

private theorem add_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena middle after : cp.TreeMultiSet K) (key : K) (count priority code root : UInt64)
    (start allocationStop stop : Nat)
    (allocate : (cp.TreeMultiSet.allocate arena key count priority).run (start + 1) =
      some ((code, middle), allocationStop))
    (insert : (cp.TreeMultiSet.insert middle middle.root code).run allocationStop = some ((root, after), stop)) :
    (cp.TreeMultiSet.add_distinct arena key count priority).run start =
      some ({after with root := root}, stop) := by
  cases arena
  cases middle
  cases after
  simp [cp.TreeMultiSet.add_distinct, Cpp.tick, allocate, insert]

theorem generated_init_spec {K : Type} (start : Nat) :
    ∃ arena : cp.TreeMultiSet K, (cp.TreeMultiSet.init (T := K)).run start = some (arena, start + 3) ∧
      arena.slots.size = 0 ∧ Nonempty (ArenaContents arena .empty) := by
  let arena : cp.TreeMultiSet K := ⟨(List.toArray []), endIndex, endIndex⟩
  have emptyCode : decode endIndex = none := (decode_none _).mpr rfl
  have root : Realizes (storageView arena) (decode endIndex) (.empty : Tree K) [] := emptyCode.symm ▸ .empty
  have free : FreeSlots (storageView arena) (decode endIndex) [] := emptyCode.symm ▸ .empty
  exact ⟨arena, rfl, rfl, ⟨⟨[], [], root, free, by intro i h; exact (Nat.not_lt_zero i h).elim⟩⟩⟩

private theorem fresh_allocation {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (tree : Tree K)
    (state : ArenaContents arena tree) (key : K) (count priority : UInt64)
    (fits : arena.slots.size < 2 ^ 63) (start : Nat) :
    ∃ code middle stop index free,
      (cp.TreeMultiSet.allocate arena key count priority).run start = some ((code, middle), stop) ∧ stop ≤ start + 6 ∧
      arena.slots.size ≤ middle.slots.size ∧ middle.slots.size ≤ arena.slots.size + 1 ∧ middle.slots.size ≤ 2 ^ 63 ∧
      (middle.slots.size > arena.slots.size → state.free = []) ∧
      Realizes (storageView middle) (decode middle.root) tree state.live ∧
      index ∉ state.live ∧
      Realizes (storageView middle) (decode code) (.node key priority count.toNat .empty .empty) [index] ∧
      FreeSlots (storageView middle) (decode middle.free_head) free ∧
      (∀ i, i < middle.slots.size → i ∈ (index :: state.live) ++ free) := by
  have liveBound (i : Nat) (mem : i ∈ state.live) : i < arena.slots.size := by
    simpa [storageView] using state.treeLayout.index_lt i mem
  cases freeEq : state.free with
  | nil =>
    have head := (decode_none _).mp ((free_shape state.freeLayout).mp freeEq)
    obtain ⟨code, middle, run, decoded, root, size, new, free, frame⟩ :=
      generated_allocate_append_spec arena key count priority head fits start
    have old : Realizes (storageView middle) (decode middle.root) tree state.live := by
      rw [root]
      exact state.treeLayout.frame fun i mem => frame i (liveBound i mem)
    refine ⟨code, middle, start + 6, arena.slots.size, [], run, le_rfl, by omega, by omega, by omega,
      fun _ => rfl, old, fun mem => (Nat.lt_irrefl _ (liveBound _ mem)), new, free, ?_⟩
    intro i mem
    by_cases equal : i = arena.slots.size
    · simp [equal]
    · have below : i < arena.slots.size := by omega
      have wasLive : i ∈ state.live := by simpa [freeEq] using state.covers i below
      exact List.mem_append_left _ (List.mem_cons_of_mem _ wasLive)
  | cons index rest =>
    have freeList : FreeSlots (storageView arena) (decode arena.free_head) (index :: rest) :=
      freeEq ▸ state.freeLayout
    obtain ⟨middle, run, root, size, new, free, frame⟩ :=
      generated_allocate_reuse_spec arena key count priority index rest freeList (by omega) start
    have absent : index ∉ state.live := freeList.disjoint_tree state.treeLayout (List.mem_cons_self ..)
    have old : Realizes (storageView middle) (decode middle.root) tree state.live := by
      rw [root]
      exact state.treeLayout.frame fun i mem => frame i fun same => absent (same ▸ mem)
    refine ⟨arena.free_head, middle, start + 4, index, rest, run, by omega, by omega, by omega, by omega,
      fun h => (Nat.not_lt_of_ge size.le h).elim, old, absent, new, free, ?_⟩
    intro i within
    have was := state.covers i (by rwa [size] at within)
    rw [freeEq, List.mem_append, List.mem_cons] at was
    simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using was

theorem generated_add_distinct_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeMultiSet K) (tree : Tree K) (state : ArenaContents arena tree)
    (key : K) (count priority : UInt64) (fits : arena.slots.size < 2 ^ 63)
    (weight : tree.weight + count.toNat < 2 ^ 64) (start : Nat) :
    ∃ out stop, (cp.TreeMultiSet.add_distinct arena key count priority).run start = some (out, stop) ∧
      stop ≤ start + 7 + 7 * (tree.height + 2) ∧
      arena.slots.size ≤ out.slots.size ∧ out.slots.size ≤ arena.slots.size + 1 ∧
      (out.slots.size > arena.slots.size → state.free = []) ∧
      Nonempty (ArenaContents out (tree.insert key priority count.toNat)) := by
  obtain ⟨code, middle, allocated, index, free, allocation, allocTime, monotone, capacity, middleFits, grows,
    oldTree, absent, newTree, freeLayout, coverBefore⟩ :=
    fresh_allocation arena tree state key count priority fits (start + 1)
  obtain ⟨root, result, stop, insert, insertTime, ⟨after⟩⟩ :=
    generated_insert_entry tree key priority count.toNat middle middle.root code state.live index
      oldTree newTree absent middleFits weight allocated
  let out := {result with root := root}
  refine ⟨out, stop, add_run arena middle result key count priority code root start allocated stop allocation insert,
    by omega, by change _ ≤ result.slots.size; rw [after.frame.size]; exact monotone,
    by change result.slots.size ≤ _; rw [after.frame.size]; exact capacity,
    fun h => grows (by change result.slots.size > _ at h; rwa [after.frame.size] at h), ?_⟩
  have apart := freeLayout.disjoint_tree oldTree
  have apartNew := freeLayout.disjoint_tree newTree
  have stableFree : FreeSlots (storageView out) (decode out.free_head) free := by
    change FreeSlots (storageView result) (decode result.free_head) free
    rw [after.frame.free]
    apply freeLayout.frame
    intro i vacant
    exact after.frame.outside i fun changed => (List.mem_cons.mp changed).elim
      (fun eq => apartNew vacant (by simp [eq])) (apart vacant)
  refine ⟨⟨after.slots, free, after.treeLayout, stableFree, ?_⟩⟩
  intro i h
  have was := coverBefore i (by change i < result.slots.size at h; rwa [after.frame.size] at h)
  rwa [List.mem_append, ← after.covers, ← List.mem_append] at was

end Proofs.Cpp.TreeMultiset
