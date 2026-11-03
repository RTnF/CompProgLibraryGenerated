import Proofs.BeatsApply0
import Proofs.BeatsCalcSpec
namespace Proofs.BeatsRep
open Proofs.BeatsModel

theorem trav_props (cls : Nd → Nat → Nat → Cls) (act : BT → BT) (hs : ∀ t, (act t).skel = t.skel)
    (hl : ∀ t, LeafOK t → LeafOK (act t)) :
    ∀ (h : Nat) (t : BT), t.height ≤ h → ∀ lo hi, LeafOK t →
      (travBT cls act t lo hi).skel = t.skel ∧ LeafOK (travBT cls act t lo hi) := by
  intro h
  induction h with
  | zero =>
    intro t ht lo hi hlf
    cases t with
    | leaf nd =>
      unfold travBT
      split
      · exact ⟨rfl, hlf⟩
      · exact ⟨hs _, hl _ hlf⟩
    | node nd tg l r => simp [BT.height] at ht
  | succ h ih =>
    intro t ht lo hi hlf
    cases t with
    | leaf nd =>
      unfold travBT
      split
      · exact ⟨rfl, hlf⟩
      · exact ⟨hs _, hl _ hlf⟩
    | node nd tg l r =>
      unfold travBT
      split
      · exact ⟨rfl, hlf⟩
      · exact ⟨hs _, hl _ hlf⟩
      · have hl' : LeafOK (applyTag tg nd l) := LeafOK_applyTag tg nd l hlf.1
        have hr' : LeafOK (applyTag tg nd r) := LeafOK_applyTag tg nd r hlf.2
        have hh1 : (applyTag tg nd l).height ≤ h := by rw [height_applyTag]; simp [BT.height] at ht; omega
        have hh2 : (applyTag tg nd r).height ≤ h := by rw [height_applyTag]; simp [BT.height] at ht; omega
        obtain ⟨a1, b1⟩ := ih (applyTag tg nd l) hh1 lo ((lo + hi) / 2) hl'
        obtain ⟨a2, b2⟩ := ih (applyTag tg nd r) hh2 ((lo + hi) / 2) hi hr'
        rw [skel_applyTag] at a1 a2
        refine ⟨?_, ?_⟩
        · show BT.skel (BT.node _ _ _ _) = _
          simp only [updateBT, BT.skel, a1, a2]
        · show LeafOK (BT.node _ _ _ _)
          exact ⟨b1, b2⟩

theorem calcMax_props (a b : Nat) :
    ∀ (h : Nat) (t : BT), t.height ≤ h → ∀ lo hi, LeafOK t →
      (calcMaxBT a b t lo hi).1.skel = t.skel ∧ LeafOK (calcMaxBT a b t lo hi).1 := by
  intro h
  induction h with
  | zero =>
    intro t ht lo hi hlf
    cases t with
    | leaf nd =>
      unfold calcMaxBT
      by_cases hc : b ≤ lo ∨ hi ≤ a
      · rw [if_pos hc]; exact ⟨rfl, hlf⟩
      · rw [if_neg hc]; exact ⟨rfl, hlf⟩
    | node nd tg l r => simp [BT.height] at ht
  | succ h ih =>
    intro t ht lo hi hlf
    cases t with
    | leaf nd =>
      unfold calcMaxBT
      by_cases hc : b ≤ lo ∨ hi ≤ a
      · rw [if_pos hc]; exact ⟨rfl, hlf⟩
      · rw [if_neg hc]; exact ⟨rfl, hlf⟩
    | node nd tg l r =>
      unfold calcMaxBT
      by_cases hc : b ≤ lo ∨ hi ≤ a
      · rw [if_pos hc]; exact ⟨rfl, hlf⟩
      · rw [if_neg hc]
        by_cases hc2 : a ≤ lo ∧ hi ≤ b
        · rw [if_pos hc2]; exact ⟨rfl, hlf⟩
        · rw [if_neg hc2]
          have hl' : LeafOK (applyTag tg nd l) := LeafOK_applyTag tg nd l hlf.1
          have hr' : LeafOK (applyTag tg nd r) := LeafOK_applyTag tg nd r hlf.2
          have hh1 : (applyTag tg nd l).height ≤ h := by rw [height_applyTag]; simp [BT.height] at ht; omega
          have hh2 : (applyTag tg nd r).height ≤ h := by rw [height_applyTag]; simp [BT.height] at ht; omega
          obtain ⟨a1, b1⟩ := ih (applyTag tg nd l) hh1 lo ((lo + hi) / 2) hl'
          obtain ⟨a2, b2⟩ := ih (applyTag tg nd r) hh2 ((lo + hi) / 2) hi hr'
          rw [skel_applyTag] at a1 a2
          exact ⟨by simp only [BT.skel, a1, a2], b1, b2⟩

theorem calcMin_props (a b : Nat) :
    ∀ (h : Nat) (t : BT), t.height ≤ h → ∀ lo hi, LeafOK t →
      (calcMinBT a b t lo hi).1.skel = t.skel ∧ LeafOK (calcMinBT a b t lo hi).1 := by
  intro h
  induction h with
  | zero =>
    intro t ht lo hi hlf
    cases t with
    | leaf nd =>
      unfold calcMinBT
      by_cases hc : b ≤ lo ∨ hi ≤ a
      · rw [if_pos hc]; exact ⟨rfl, hlf⟩
      · rw [if_neg hc]; exact ⟨rfl, hlf⟩
    | node nd tg l r => simp [BT.height] at ht
  | succ h ih =>
    intro t ht lo hi hlf
    cases t with
    | leaf nd =>
      unfold calcMinBT
      by_cases hc : b ≤ lo ∨ hi ≤ a
      · rw [if_pos hc]; exact ⟨rfl, hlf⟩
      · rw [if_neg hc]; exact ⟨rfl, hlf⟩
    | node nd tg l r =>
      unfold calcMinBT
      by_cases hc : b ≤ lo ∨ hi ≤ a
      · rw [if_pos hc]; exact ⟨rfl, hlf⟩
      · rw [if_neg hc]
        by_cases hc2 : a ≤ lo ∧ hi ≤ b
        · rw [if_pos hc2]; exact ⟨rfl, hlf⟩
        · rw [if_neg hc2]
          have hl' : LeafOK (applyTag tg nd l) := LeafOK_applyTag tg nd l hlf.1
          have hr' : LeafOK (applyTag tg nd r) := LeafOK_applyTag tg nd r hlf.2
          have hh1 : (applyTag tg nd l).height ≤ h := by rw [height_applyTag]; simp [BT.height] at ht; omega
          have hh2 : (applyTag tg nd r).height ≤ h := by rw [height_applyTag]; simp [BT.height] at ht; omega
          obtain ⟨a1, b1⟩ := ih (applyTag tg nd l) hh1 lo ((lo + hi) / 2) hl'
          obtain ⟨a2, b2⟩ := ih (applyTag tg nd r) hh2 ((lo + hi) / 2) hi hr'
          rw [skel_applyTag] at a1 a2
          exact ⟨by simp only [BT.skel, a1, a2], b1, b2⟩

end Proofs.BeatsRep
