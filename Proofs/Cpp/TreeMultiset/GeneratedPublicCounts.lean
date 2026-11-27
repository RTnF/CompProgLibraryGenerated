import Proofs.Cpp.TreeMultiset.ArenaReadCounts

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

variable {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]

omit [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K] in
private theorem none_run (start : Nat) :
    (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl

theorem add_zero_run (arena : cp.TreeMultiSet K) (key : K) (found : UInt64) (globals : cp.GlobalState_ce115a401cd87c22)
    (start searched : Nat)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((found, arena), searched)) :
    (cp.TreeMultiSet.add arena key 0 globals).run start = some ((readCount arena found, arena, globals), searched + 1) := by
  cases arena
  cases globals
  simp [cp.TreeMultiSet.add, Cpp.tick, locate, none_run, readCount, modelCell]

theorem add_fresh_run (arena after : cp.TreeMultiSet K) (key : K) (n priority : UInt64)
    (globals next : cp.GlobalState_ce115a401cd87c22) (start searched stop : Nat)
    (nonzero : n ≠ 0)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((endIndex, arena), searched))
    (draw : (cp.multiset_next_priority globals).run (searched + 1) = some ((priority, next), searched + 2))
    (add : (cp.TreeMultiSet.add_distinct arena key n priority).run (searched + 2) = some (after, stop)) :
    (cp.TreeMultiSet.add arena key n globals).run start = some ((n, after, next), stop) := by
  cases arena
  cases after
  cases globals
  cases next
  simp [cp.TreeMultiSet.add, Cpp.tick, locate, none_run, nonzero, draw, add]

theorem add_known_run (arena after : cp.TreeMultiSet K) (key : K) (n found : UInt64)
    (globals : cp.GlobalState_ce115a401cd87c22) (start searched stop : Nat)
    (nonzero : n ≠ 0) (present : found ≠ endIndex)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((found, arena), searched))
    (update : (cp.TreeMultiSet.replace_count arena arena.root key ((modelCell arena found).count + n)).run (searched + 1) =
      some (after, stop)) :
    (cp.TreeMultiSet.add arena key n globals).run start = some (((modelCell arena found).count + n, after, globals), stop) := by
  cases arena
  cases after
  cases globals
  simp [cp.TreeMultiSet.add, Cpp.tick, locate, none_run, nonzero, present, modelCell] at update ⊢
  simp [update]

theorem remove_count_missing_run (arena : cp.TreeMultiSet K) (key : K) (n : UInt64) (start searched : Nat)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((endIndex, arena), searched)) :
    (cp.TreeMultiSet.remove arena key n).run start = some ((false, arena), searched + 1) := by
  cases arena
  simp [cp.TreeMultiSet.remove, Cpp.tick, locate, none_run]

theorem remove_count_too_many_run (arena : cp.TreeMultiSet K) (key : K) (n found : UInt64) (start searched : Nat)
    (present : found ≠ endIndex) (tooMany : (modelCell arena found).count < n)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((found, arena), searched)) :
    (cp.TreeMultiSet.remove arena key n).run start = some ((false, arena), searched + 1) := by
  cases arena
  dsimp only [modelCell] at tooMany
  simp [cp.TreeMultiSet.remove, Cpp.tick, locate, none_run, present, tooMany]

theorem remove_count_all_run (arena after : cp.TreeMultiSet K) (key : K) (n found root : UInt64) (start searched stop : Nat)
    (present : found ≠ endIndex) (equal : (modelCell arena found).count = n)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((found, arena), searched))
    (erase : (cp.TreeMultiSet.erase arena arena.root key).run (searched + 1) = some ((root, after), stop)) :
    (cp.TreeMultiSet.remove arena key n).run start = some ((true, {after with root := root}), stop) := by
  cases arena
  cases after
  dsimp only [modelCell] at equal
  simp [cp.TreeMultiSet.remove, Cpp.tick, locate, none_run, present, equal, erase]

theorem remove_count_some_run (arena after : cp.TreeMultiSet K) (key : K) (n found : UInt64) (start searched stop : Nat)
    (present : found ≠ endIndex) (less : n < (modelCell arena found).count)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((found, arena), searched))
    (update : (cp.TreeMultiSet.replace_count arena arena.root key ((modelCell arena found).count - n)).run (searched + 1) =
      some (after, stop)) :
    (cp.TreeMultiSet.remove arena key n).run start = some ((true, after), stop) := by
  have natural := UInt64.lt_iff_toNat_lt.mp less
  have different : (modelCell arena found).count ≠ n :=
    fun same => (Nat.ne_of_gt natural) (congrArg UInt64.toNat same)
  have atLeast : ¬ (modelCell arena found).count < n :=
    fun wrong => (Nat.not_lt_of_ge (Nat.le_of_lt natural)) (UInt64.lt_iff_toNat_lt.mp wrong)
  cases arena
  cases after
  dsimp only [modelCell] at update different atLeast
  simp [cp.TreeMultiSet.remove, Cpp.tick, locate, none_run, present, atLeast, different, update]

theorem remove_all_missing_run (arena : cp.TreeMultiSet K) (key : K) (start searched : Nat)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((endIndex, arena), searched)) :
    (cp.TreeMultiSet.remove_all arena key).run start = some ((0, arena), searched + 1) := by
  cases arena
  simp [cp.TreeMultiSet.remove_all, Cpp.tick, locate, none_run]

theorem remove_all_known_run (arena after : cp.TreeMultiSet K) (key : K) (found root : UInt64)
    (start searched stop : Nat) (present : found ≠ endIndex)
    (locate : (cp.TreeMultiSet.locate arena key).run (start + 1) = some ((found, arena), searched))
    (erase : (cp.TreeMultiSet.erase arena arena.root key).run (searched + 1) = some ((root, after), stop)) :
    (cp.TreeMultiSet.remove_all arena key).run start = some (((modelCell arena found).count, {after with root := root}), stop) := by
  cases arena
  cases after
  simp [cp.TreeMultiSet.remove_all, Cpp.tick, locate, none_run, present, erase, modelCell]

end Proofs.Cpp.TreeMultiset
