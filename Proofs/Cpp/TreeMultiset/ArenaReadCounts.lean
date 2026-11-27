import Proofs.Cpp.TreeMultiset.CountLayout
import Proofs.Cpp.TreeMultiset.ArenaPriority

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

theorem generated_size_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (tree : Tree K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ result, (cp.TreeMultiSet.size_ arena).run start = some ((result, arena), start + 3) ∧ result.toNat = tree.weight := by
  obtain ⟨result, weightRun, size⟩ := generated_weight_spec arena arena.root tree used layout fits (start + 1)
  refine ⟨result, ?_, size⟩
  cases arena
  simp [cp.TreeMultiSet.size_, Cpp.tick, weightRun]

def readCount {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (code : UInt64) : UInt64 :=
  if code = endIndex then 0 else (modelCell arena code).count

theorem readCount_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (key : K) (used : List Nat)
    (code : UInt64) (count : Option Nat)
    (located : match count with | none => code = endIndex | some c => FoundAt arena key used code c) :
    (readCount arena code).toNat = count.getD 0 := by
  cases count with
  | none => simp [readCount, located]
  | some count =>
    obtain ⟨index, decoded, _, _, result⟩ := located
    have present := (decode_some code index decoded).1
    simp [readCount, present, result]

theorem generated_count_spec {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]
    (arena : cp.TreeMultiSet K) (tree : Tree K) (key : K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ result stop, (cp.TreeMultiSet.count arena key).run start = some ((result, arena), stop) ∧
      result.toNat = (tree.lookup key).getD 0 ∧ stop ≤ start + 2 * tree.height + 6 := by
  obtain ⟨found, searched, lookup, time, located⟩ :=
    generated_locate_spec arena tree key used layout fits (start + 1)
  refine ⟨readCount arena found, searched + 1, ?_,
    readCount_spec arena key used found (tree.lookup key) located, by omega⟩
  cases arena
  have noneRun : (cp.TreeMultiSet.none (T := K)).run searched = some (endIndex, searched + 1) := rfl
  simp [cp.TreeMultiSet.count, Cpp.tick, lookup, noneRun, readCount, modelCell]

theorem ArenaFrame.contents {K : Type} {before after : cp.TreeMultiSet K} {was now : Tree K} (state : ArenaContents before was)
    (frame : ArenaFrame before after state.live)
    (layout : Realizes (storageView after) (decode before.root) now state.live) :
    Nonempty (ArenaContents after now) := by
  have free : FreeSlots (storageView after) (decode after.free_head) state.free := by
    rw [frame.free]
    exact state.freeLayout.frame fun i mem => frame.outside i (state.freeLayout.disjoint_tree state.treeLayout mem)
  refine ⟨⟨state.live, state.free, frame.root.symm ▸ layout, free, ?_⟩⟩
  intro i h
  exact state.covers i (by rwa [frame.size] at h)

theorem EraseResult.contents {K : Type} {before after : cp.TreeMultiSet K} {was now : Tree K} {root : UInt64}
    (state : ArenaContents before was)
    (removed : EraseResult before after state.live state.free root now) :
    Nonempty (ArenaContents {after with root := root} now) := by
  refine ⟨⟨removed.slots, removed.removed :: state.free, removed.treeLayout, removed.freeLayout, ?_⟩⟩
  intro i present
  change i < after.slots.size at present
  rw [removed.sizePreserved] at present
  rcases List.mem_append.mp (state.covers i present) with live | free
  · rcases (removed.covers i).mpr live with rfl | member
    · exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_left _ member
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ free)

end Proofs.Cpp.TreeMultiset
