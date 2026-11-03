import Proofs.BeatsCtorMath
import Proofs.BeatsSums
namespace Proofs.BeatsRep
open Proofs.BeatsModel
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

def zeroNd : Nd := ⟨0, 0, 0, 0, 0, 0⟩

def isInnerAt (n j : Nat) : Prop := (rngOf n j).1 + 1 < (rngOf n j).2
def isLeafAt (n j : Nat) : Prop := (rngOf n j).1 < (rngOf n j).2 ∧ ¬ isInnerAt n j

instance (n j : Nat) : Decidable (isInnerAt n j) := by unfold isInnerAt; infer_instance
instance (n j : Nat) : Decidable (isLeafAt n j) := by unfold isLeafAt; infer_instance

/-- The heap right after the first loop of the constructor: the leaves are filled, everything else is zero. -/
def C0 (a : List Int) (n : Nat) : Heap := fun j =>
  if isLeafAt n j then (leafNd (a.getD (rngOf n j).1 0), noTag) else (zeroNd, noTag)

theorem skel_lt (n : Nat) (hn : 1 ≤ n) : ∀ j, (rngOf n j).1 < (rngOf n j).2 → j < 4 * n := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hj
    by_cases h0 : j = 0
    · subst h0; omega
    · have hp : (j - 1) / 2 < j := by omega
      have hpar : j = 2 * ((j - 1) / 2) + 1 ∨ j = 2 * ((j - 1) / 2) + 2 := by omega
      set p := (j - 1) / 2 with hpd
      have hpin : (rngOf n p).1 + 1 < (rngOf n p).2 := by
        rcases hpar with h | h
        · rw [h, rngOf_left] at hj
          by_cases hin : (rngOf n p).1 + 1 < (rngOf n p).2
          · exact hin
          · rw [if_neg hin] at hj; simp at hj
        · rw [h, rngOf_right] at hj
          by_cases hin : (rngOf n p).1 + 1 < (rngOf n p).2
          · exact hin
          · rw [if_neg hin] at hj; simp at hj
      have hidx := rngOf_index n p (by omega)
      have : 2 ≤ (rngOf n p).2 - (rngOf n p).1 := by omega
      have h3 : p + 2 ≤ 2 * n := by
        have h4 : (p + 2) * 1 ≤ (p + 2) * ((rngOf n p).2 - (rngOf n p).1 - 1) := Nat.mul_le_mul_left _ (by omega)
        omega
      omega

theorem leaf_cell (a : List Int) (n j : Nat) (hj : isLeafAt n j) :
    (C0 a n j).1 = nodeAt a n j := by
  unfold C0 nodeAt
  rw [if_pos hj]
  have hl : ¬ ((rngOf n j).1 + 1 < (rngOf n j).2) := hj.2
  rw [buildBT, if_neg hl]
  rfl

theorem nodeAt_inner (a : List Int) (n j : Nat) (hj : isInnerAt n j) :
    nodeAt a n j = mergeNd (nodeAt a n (2 * j + 1)) (nodeAt a n (2 * j + 2)) := by
  have hl := rngOf_left n j
  have hr := rngOf_right n j
  have hj' : (rngOf n j).1 + 1 < (rngOf n j).2 := hj
  rw [if_pos hj'] at hl hr
  unfold nodeAt
  rw [hl, hr]
  simp only
  rw [buildBT, if_pos hj']
  rfl

theorem child_skel (n j : Nat) (hj : isInnerAt n j) :
    (rngOf n (2 * j + 1)).1 < (rngOf n (2 * j + 1)).2 ∧ (rngOf n (2 * j + 2)).1 < (rngOf n (2 * j + 2)).2 := by
  have hl := rngOf_left n j
  have hr := rngOf_right n j
  have hj' : (rngOf n j).1 + 1 < (rngOf n j).2 := hj
  rw [if_pos hj'] at hl hr
  rw [hl, hr]
  unfold isInnerAt at hj
  simp only
  omega

/-- The inner nodes below `m`, in decreasing order. -/
def LLr (n : Nat) : Nat → List Nat
  | 0 => []
  | m + 1 => (if isInnerAt n m then [m] else []) ++ LLr n m

/-- The inner nodes in `[m, B)`, in decreasing order. -/
def XX (n B m : Nat) : List Nat :=
  if m < B then XX n B (m + 1) ++ (if isInnerAt n m then [m] else []) else []
termination_by B - m

theorem XX_lt (n B m : Nat) (h : m < B) : XX n B m = XX n B (m + 1) ++ (if isInnerAt n m then [m] else []) := by
  rw [XX, if_pos h]

theorem XX_ge (n B m : Nat) (h : B ≤ m) : XX n B m = [] := by
  rw [XX, if_neg (by omega)]

theorem XX_LLr (n B : Nat) : ∀ d m, m + d = B → XX n B m ++ LLr n m = LLr n B := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hmB : m = B := by omega
    subst hmB
    rw [XX_ge n m m (by omega)]
    rfl
  | succ d ih =>
    intro m hm
    rw [XX_lt n B m (by omega)]
    have := ih (m + 1) (by omega)
    rw [← this, LLr]
    simp [List.append_assoc]

/-- The finished cells of the tree: the nodes at or above the processed point, and the leaves. -/
theorem phase2 (a : List Int) (n : Nat) (hn : 1 ≤ n) :
    ∀ d m, m + d = 4 * n →
      (∀ j, ((upPhase (XX n (4 * n) m) (C0 a n)) j).2 = noTag) ∧
      ∀ j, (rngOf n j).1 < (rngOf n j).2 → (m ≤ j ∨ isLeafAt n j) →
        ((upPhase (XX n (4 * n) m) (C0 a n)) j).1 = nodeAt a n j := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hmB : m = 4 * n := by omega
    subst hmB
    rw [XX_ge n _ _ (le_refl _)]
    refine ⟨fun j => ?_, fun j hj hor => ?_⟩
    · show (C0 a n j).2 = noTag
      unfold C0; split <;> rfl
    · have hlt := skel_lt n hn j hj
      rcases hor with h | h
      · omega
      · exact leaf_cell a n j h
  | succ d ih =>
    intro m hm
    obtain ⟨iht, ihn⟩ := ih (m + 1) (by omega)
    rw [XX_lt n _ _ (by omega), upPhase_append]
    generalize hH : upPhase (XX n (4 * n) (m + 1)) (C0 a n) = H' at iht ihn ⊢
    by_cases hin : isInnerAt n m
    · rw [if_pos hin]
      have hu : upPhase [m] H' = updateH H' m := rfl
      rw [hu]
      refine ⟨fun j => ?_, fun j hj hor => ?_⟩
      · unfold updateH
        by_cases hjm : j = m
        · subst hjm; rw [Heap.set_eq]; exact iht j
        · rw [Heap.set_ne _ _ _ _ hjm]; exact iht j
      · unfold updateH
        by_cases hjm : j = m
        · subst hjm
          rw [Heap.set_eq]
          simp only
          obtain ⟨c1, c2⟩ := child_skel n j hin
          rw [ihn _ c1 (Or.inl (by omega)), ihn _ c2 (Or.inl (by omega))]
          exact (nodeAt_inner a n j hin).symm
        · rw [Heap.set_ne _ _ _ _ hjm]
          apply ihn j hj
          rcases hor with h | h
          · left; omega
          · right; exact h
    · rw [if_neg hin]
      have hu : upPhase [] H' = H' := rfl
      rw [hu]
      refine ⟨iht, fun j hj hor => ihn j hj ?_⟩
      rcases hor with h | h
      · by_cases hjm : j = m
        · subst hjm; right; exact ⟨hj, hin⟩
        · left; omega
      · right; exact h


theorem XX_zero (n B : Nat) : XX n B 0 = LLr n B := by
  have := XX_LLr n B B 0 (by omega)
  simpa [LLr] using this

theorem agree_final (a : List Int) (n : Nat) (hn : 1 ≤ n) :
    Agree (upPhase (LLr n (4 * n)) (C0 a n)) (buildBT a 0 n) 0 := by
  have h0 : rngOf n 0 = (0, n) := by simp [rngOf]
  obtain ⟨hT, hN⟩ := phase2 a n hn (4 * n) 0 (by omega)
  rw [XX_zero] at hT hN
  intro j nd otg hj
  obtain ⟨hs, hnd, hot⟩ := sub2_build a n (n - 0) 0 n 0 rfl (by omega) h0 j nd otg hj
  refine ⟨?_, fun tg htg => ?_⟩
  · rw [hnd]
    apply hN j hs
    exact Or.inl (Nat.zero_le _)
  · rw [hT j]
    rw [hot] at htg
    split at htg
    · exact Option.some.inj htg
    · cases htg


theorem LLr_length_le (n : Nat) : ∀ k, (LLr n k).length ≤ k := by
  intro k
  induction k with
  | zero => simp [LLr]
  | succ k ih =>
    unfold LLr
    split <;> simp <;> omega

theorem rngOf_lo_lt (n : Nat) (hn : 1 ≤ n) (j : Nat) : (rngOf n j).1 < n := by
  rcases rngOf_cases n j with h | h
  · have := (rngOf_le n j).2; omega
  · rw [h]; simp; omega


theorem desc_nodeAt (a : List Int) (n : Nat) (ha : InRange a) (hlen : a.length = n) (j : Nat) (hj : (rngOf n j).1 < (rngOf n j).2) :
    Desc (nodeAt a n j) ((a.drop (rngOf n j).1).take ((rngOf n j).2 - (rngOf n j).1)) := by
  have := (buildBT_spec a ha ((rngOf n j).2 - (rngOf n j).1) (rngOf n j).1 (rngOf n j).2 rfl hj (by have := (rngOf_le n j).2; omega)).1
  exact this.desc

theorem phase2_sums (a : List Int) (n : Nat) (hn : 1 ≤ n) (ha : InRange a) (hlen : a.length = n) (hnM : n < M31) :
    ∀ d m, m + d = 4 * n → SumsOK (XX n (4 * n) m) (C0 a n) := by
  intro d
  induction d with
  | zero =>
    intro m hm
    have hmB : m = 4 * n := by omega
    subst hmB
    rw [XX_ge n _ _ (le_refl _)]; trivial
  | succ d ih =>
    intro m hm
    have ih' := ih (m + 1) (by omega)
    rw [XX_lt n _ _ (by omega), SumsOK_append]
    refine ⟨ih', ?_⟩
    by_cases hin : isInnerAt n m
    · rw [if_pos hin]
      refine ⟨?_, trivial⟩
      obtain ⟨c1, c2⟩ := child_skel n m hin
      obtain ⟨hT, hN⟩ := phase2 a n hn d (m + 1) (by omega)
      have hl := rngOf_left n m
      have hr := rngOf_right n m
      have hin' : (rngOf n m).1 + 1 < (rngOf n m).2 := hin
      rw [if_pos hin'] at hl hr
      have hb := rngOf_le n m
      refine SumOK_of_desc _ m ((a.drop (rngOf n (2 * m + 1)).1).take ((rngOf n (2 * m + 1)).2 - (rngOf n (2 * m + 1)).1))
        ((a.drop (rngOf n (2 * m + 2)).1).take ((rngOf n (2 * m + 2)).2 - (rngOf n (2 * m + 2)).1)) ?_ ?_ ?_
      · rw [hN _ c1 (Or.inl (by omega))]; exact desc_nodeAt a n ha hlen _ c1
      · rw [hN _ c2 (Or.inl (by omega))]; exact desc_nodeAt a n ha hlen _ c2
      · simp only [List.length_take, List.length_drop, hl, hr]
        have : (2 : Nat) ≤ 2 := le_refl _
        have hM : M31 = 2147483648 := rfl
        omega
    · rw [if_neg hin]; trivial

end Proofs.BeatsRep
