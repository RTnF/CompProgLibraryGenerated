import Proofs.Cpp.TreeMultiset.GeneratedPublicCounts

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

variable {K : Type} [Inhabited K] [LT K] [DecidableLT K] [DecidableEq K]

omit [Inhabited K] in
theorem Tree.lookup_le_weight (tree : Tree K) (key : K) (count : Nat)
    (found : tree.lookup key = some count) : count ≤ tree.weight := by
  induction tree with
  | empty => simp [Tree.lookup] at found
  | node old p n left right ihLeft ihRight =>
    simp only [Tree.lookup] at found
    by_cases same : key = old
    · simp only [ite_eq_left same, Option.some.injEq] at found
      simp only [Tree.weight]
      omega
    · simp only [ite_eq_right same] at found
      by_cases less : key < old
      · have bounded := ihLeft (by simpa only [ite_eq_left less] using found)
        simp only [Tree.weight]
        omega
      · have bounded := ihRight (by simpa only [ite_eq_right less] using found)
        simp only [Tree.weight]
        omega

def treeAfterAdd (tree : Tree K) (key : K) (n : Nat) (priority : UInt64) : Tree K :=
  if n = 0 then tree
  else match tree.lookup key with
  | none => tree.insert key priority n
  | some count => tree.changeCount key (fun _ => count + n)

def priorityAfterAdd (state : UInt64) (requested : Nat) (known : Option Nat) : UInt64 :=
  if requested = 0 ∨ known.isSome then state else xorshift state

theorem generated_add_spec (arena : cp.TreeMultiSet K) (tree : Tree K) (state : ArenaContents arena tree)
    (key : K) (n : UInt64) (globals : cp.GlobalState_ce115a401cd87c22)
    (fits : arena.slots.size < 2 ^ 63) (weight : tree.weight + n.toNat < 2 ^ 64) (start : Nat) :
    ∃ value after next stop,
      (cp.TreeMultiSet.add arena key n globals).run start = some ((value, after, next), stop) ∧
      value.toNat = (tree.lookup key).getD 0 + n.toNat ∧
      stop ≤ start + 9 * tree.height + 28 ∧
      priorityState next = priorityAfterAdd (priorityState globals) n.toNat (tree.lookup key) ∧
      Nonempty (ArenaContents after (treeAfterAdd tree key n.toNat (xorshift (priorityState globals)))) := by
  obtain ⟨found, searched, locate, time, check⟩ :=
    generated_locate_spec arena tree key state.live state.treeLayout (by omega) (start + 1)
  by_cases zero : n = 0
  · subst n
    refine ⟨readCount arena found, arena, globals, searched + 1, add_zero_run arena key found globals start searched locate,
      ?_, by omega, ?_, ?_⟩
    · simpa using readCount_spec arena key state.live found (tree.lookup key) check
    · simp [priorityAfterAdd]
    · simpa [treeAfterAdd] using (show Nonempty (ArenaContents arena tree) from ⟨state⟩)
  · have nonzero : n.toNat ≠ 0 := fun e => zero (UInt64.toNat_inj.mp (e.trans UInt64.toNat_zero.symm))
    cases known : tree.lookup key with
    | none =>
      rw [known] at check
      subst found
      obtain ⟨next, drawn, priority⟩ := generated_next_priority globals (searched + 1)
      obtain ⟨after, stop, add, cost, _, inserted⟩ :=
        generated_add_growth arena tree state key n (xorshift (priorityState globals)) fits weight (searched + 2)
      refine ⟨n, after, next, stop, add_fresh_run arena after key n _ globals next start searched stop zero locate drawn add,
        by simp, by omega, ?_, ?_⟩
      · simpa [priorityAfterAdd, nonzero] using priority
      · simpa [treeAfterAdd, nonzero, known] using inserted
    | some count =>
      rw [known] at check
      obtain ⟨index, decoded, _, _, countExact⟩ := check
      have present := (decode_some found index decoded).1
      let newCount := (modelCell arena found).count + n
      have oldBound := tree.lookup_le_weight key count known
      have word : newCount.toNat = count + n.toNat := by
        dsimp only [newCount]
        rw [UInt64.toNat_add, countExact, Nat.mod_eq_of_lt (by omega)]
      have newWeight := tree.change_count_weight key count newCount.toNat known
      have smaller : (tree.changeCount key (fun _ => newCount.toNat)).weight < 2 ^ 64 := by omega
      obtain ⟨after, stop, update, cost, layout, frame⟩ :=
        generated_count_entry tree key count newCount known arena arena.root state.live state.treeLayout
          (by omega) smaller (searched + 1)
      refine ⟨newCount, after, globals, stop,
        add_known_run arena after key n found globals start searched stop zero present locate update, word,
        by omega, ?_, ?_⟩
      · simp [priorityAfterAdd]
      · simpa only [treeAfterAdd, ite_eq_right nonzero, known, word] using frame.contents state layout

def treeAfterRemove (tree : Tree K) (key : K) (n : Nat) : Bool × Tree K :=
  match tree.lookup key with
  | none => (false, tree)
  | some count =>
    if count < n then (false, tree)
    else if count = n then (true, tree.erase key)
    else (true, tree.changeCount key (fun _ => count - n))

theorem generated_remove_count_spec (arena : cp.TreeMultiSet K) (tree : Tree K) (state : ArenaContents arena tree)
    (key : K) (n : UInt64) (fits : arena.slots.size ≤ 2 ^ 63)
    (weight : tree.weight < 2 ^ 64) (start : Nat) :
    ∃ success after stop, (cp.TreeMultiSet.remove arena key n).run start = some ((success, after), stop) ∧
      success = (treeAfterRemove tree key n.toNat).1 ∧
      stop ≤ start + 18 * tree.height + 11 ∧
      after.slots.size = arena.slots.size ∧
      Nonempty (ArenaContents after (treeAfterRemove tree key n.toNat).2) := by
  obtain ⟨found, searched, locate, searchTime, result⟩ :=
    generated_locate_spec arena tree key state.live state.treeLayout fits (start + 1)
  cases known : tree.lookup key with
  | none =>
    rw [known] at result
    subst found
    simpa only [treeAfterRemove, known] using
      (show ∃ ok after stop, (cp.TreeMultiSet.remove arena key n).run start = some ((ok, after), stop) ∧
          ok = false ∧ stop ≤ start + 18 * tree.height + 11 ∧ after.slots.size = arena.slots.size ∧
          Nonempty (ArenaContents after tree) from
        ⟨false, arena, searched + 1, remove_count_missing_run arena key n start searched locate,
          rfl, by omega, rfl, ⟨state⟩⟩)
  | some count =>
    rw [known] at result
    obtain ⟨index, decoded, _, _, countExact⟩ := result
    have present := (decode_some found index decoded).1
    by_cases more : count < n.toNat
    · have tooMany : (modelCell arena found).count < n := by
        rw [UInt64.lt_iff_toNat_lt, countExact]
        exact more
      refine ⟨false, arena, searched + 1,
        remove_count_too_many_run arena key n found start searched present tooMany locate,
        ?_, by omega, rfl, ?_⟩
      · simp [treeAfterRemove, known, more]
      · simpa [treeAfterRemove, known, more] using (show Nonempty (ArenaContents arena tree) from ⟨state⟩)
    · by_cases same : count = n.toNat
      · have equal : (modelCell arena found).count = n := UInt64.toNat_inj.mp (countExact.trans same)
        obtain ⟨root, result, stop, erase, cost, ⟨removal⟩⟩ :=
          generated_erase_entry tree key count known arena arena.root state.live state.free
            state.treeLayout state.freeLayout fits weight (searched + 1)
        refine ⟨true, {result with root := root}, stop,
          remove_count_all_run arena result key n found root start searched stop present equal locate erase,
          ?_, by omega, removal.sizePreserved, ?_⟩
        · simp [treeAfterRemove, known, same]
        · simpa only [treeAfterRemove, known, ite_eq_right more, ite_eq_left same] using removal.contents state
      · have less : n < (modelCell arena found).count := by
          rw [UInt64.lt_iff_toNat_lt, countExact]
          omega
        let newCount := (modelCell arena found).count - n
        have word : newCount.toNat = count - n.toNat := by
          dsimp only [newCount]
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp less))), countExact]
        have oldBound := tree.lookup_le_weight key count known
        have newWeight := tree.change_count_weight key count newCount.toNat known
        have smaller : (tree.changeCount key (fun _ => newCount.toNat)).weight < 2 ^ 64 := by omega
        obtain ⟨after, stop, update, cost, layout, frame⟩ :=
          generated_count_entry tree key count newCount known arena arena.root state.live state.treeLayout
            fits smaller (searched + 1)
        refine ⟨true, after, stop,
          remove_count_some_run arena after key n found start searched stop present less locate update,
          ?_, by omega, frame.size, ?_⟩
        · simp [treeAfterRemove, known, more, same]
        · simpa only [treeAfterRemove, known, ite_eq_right more, ite_eq_right same, word] using frame.contents state layout

theorem generated_remove_all_spec (arena : cp.TreeMultiSet K) (tree : Tree K) (state : ArenaContents arena tree)
    (key : K) (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64) (start : Nat) :
    ∃ count after stop, (cp.TreeMultiSet.remove_all arena key).run start = some ((count, after), stop) ∧
      count.toNat = (tree.lookup key).getD 0 ∧
      stop ≤ start + 18 * tree.height + 11 ∧ after.slots.size = arena.slots.size ∧
      match tree.lookup key with
      | none => after = arena
      | some n => (tree.erase key).weight + n = tree.weight ∧ Nonempty (ArenaContents after (tree.erase key)) := by
  obtain ⟨found, searched, locate, searchTime, result⟩ :=
    generated_locate_spec arena tree key state.live state.treeLayout fits (start + 1)
  cases known : tree.lookup key with
  | none =>
    rw [known] at result
    subst found
    exact ⟨0, arena, searched + 1, remove_all_missing_run arena key start searched locate,
      rfl, by omega, rfl, rfl⟩
  | some count =>
    rw [known] at result
    obtain ⟨index, decoded, _, _, countExact⟩ := result
    have present := (decode_some found index decoded).1
    obtain ⟨root, after, stop, erase, cost, ⟨removal⟩⟩ :=
      generated_erase_entry tree key count known arena arena.root state.live state.free
        state.treeLayout state.freeLayout fits weight (searched + 1)
    exact ⟨_, {after with root := root}, stop,
      remove_all_known_run arena after key found root start searched stop present locate erase,
      countExact, by omega, removal.sizePreserved, Tree.erase_weight tree key count known, removal.contents state⟩

end Proofs.Cpp.TreeMultiset
