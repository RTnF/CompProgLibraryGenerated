import Proofs.Cpp.TreeMultiset.ArenaNeighbors

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

private theorem tick_run (start : Nat) : Cpp.tick.run start = some ((), start + 1) := rfl

private theorem none_run (K : Type) (start : Nat) :
    (cp.TreeMultiSet.none (T := K)).run start = some (endIndex, start + 1) := rfl

private theorem some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

private theorem pure_run {A : Type} (value : A) (start : Nat) :
    (pure value : Cpp.M A).run start = some (value, start) := rfl

theorem generated_check_total {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (tree : Tree K)
    (code : UInt64) (used : List Nat) (layout : Realizes (storageView arena) (decode code) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64)
    (fuel start : Nat) (enough : tree.height < fuel) :
    (cp.TreeMultiSet.check_total_rec fuel arena code).run start =
      some (modelWeight arena code, start + 2 + 4 * tree.slots) := by
  induction tree generalizing code used fuel start with
  | empty =>
    have endCode := (decode_none _).mp (layout.empty_iff.mpr rfl)
    subst code
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      cases arena
      simp only [cp.TreeMultiSet.check_total_rec, StateT.run_bind, tick_run, none_run, some_bind, pure_run,
        decide_true, ite_true, modelWeight, Tree.slots, Nat.mul_zero, Nat.add_zero]
  | node key priority count left right ihLeft ihRight =>
    generalize decoded : decode code = index at layout
    cases layout with
    | @node slot _ _ _ _ _ lc rc ls rs reads ll rr lf rf sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨present, _⟩ := decode_some code slot decoded
        obtain ⟨_, _, view⟩ := modelCell_view arena code slot _ decoded reads fits
        let row := modelCell arena code
        have countEq : row.count.toNat = count := congrArg StoredNode.count view
        have leftEq : decode row.left = lc := congrArg StoredNode.left view
        have rightEq : decode row.right = rc := congrArg StoredNode.right view
        have totalEq : row.total.toNat = count + left.weight + right.weight := congrArg StoredNode.total view
        have leftLayout : Realizes (storageView arena) (decode row.left) left ls := leftEq.symm ▸ ll
        have rightLayout : Realizes (storageView arena) (decode row.right) right rs := rightEq.symm ▸ rr
        have leftNat := weight_from_layout arena row.left left ls leftLayout fits
        have rightNat := weight_from_layout arena row.right right rs rightLayout fits
        simp only [Tree.height, Tree.weight] at enough weight
        let middle := start + 2 + 2 + 4 * left.slots
        have leftRun := ihLeft row.left ls leftLayout (by omega) fuel (start + 2) (by omega)
        have rightRun := ihRight row.right rs rightLayout (by omega) fuel middle (by omega)
        have total : row.count + modelWeight arena row.left + modelWeight arena row.right = row.total := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, UInt64.toNat_add, countEq, leftNat, rightNat, totalEq]
          rw [Nat.mod_eq_of_lt (by omega : count + left.weight < 2 ^ 64), Nat.mod_eq_of_lt weight]
        have clock : middle + 2 + 4 * right.slots = start + 2 + 4 * (Tree.node key priority count left right).slots := by
          simp only [middle, Tree.slots]
          omega
        cases arena
        dsimp only [row, middle, modelCell] at leftRun rightRun total clock ⊢
        simp only [cp.TreeMultiSet.check_total_rec, StateT.run_bind, tick_run, none_run, some_bind,
          present, decide_false, Bool.false_eq_true, ite_false, leftRun, rightRun]
        rw [total]
        simp [Cpp.check, modelWeight, modelCell, present, clock]

theorem generated_verify_spec {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) (tree : Tree K)
    (used : List Nat) (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (fits : arena.slots.size ≤ 2 ^ 63) (weight : tree.weight < 2 ^ 64) (start : Nat) :
    ∃ stop, (cp.TreeMultiSet.verify arena).run start = some (arena, stop) ∧ stop ≤ start + 6 + 4 * tree.slots := by
  by_cases emptyCode : arena.root = endIndex
  · refine ⟨start + 2, ?_, by omega⟩
    cases arena
    dsimp only at emptyCode
    simp [cp.TreeMultiSet.verify, StateT.run_bind, tick_run, none_run, some_bind, emptyCode]
  · have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
    have height := tree.height_le_slots
    have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
    let middle := start + 2 + 2 + 4 * tree.slots
    have scan : (cp.TreeMultiSet.check_total arena arena.root).run (start + 2) =
        some (modelWeight arena arena.root, middle) :=
      generated_check_total arena tree arena.root used layout fits weight Cpp.fuel (start + 2) enough
    have weightRun : (cp.TreeMultiSet.weight arena arena.root).run middle =
        some (modelWeight arena arena.root, middle + 2) := generated_weight_run arena arena.root middle
    refine ⟨middle + 2, ?_, by simp [middle]; omega⟩
    cases arena
    simp [cp.TreeMultiSet.verify, StateT.run_bind, tick_run, none_run, some_bind, emptyCode, scan, weightRun, Cpp.check]

end Proofs.Cpp.TreeMultiset
