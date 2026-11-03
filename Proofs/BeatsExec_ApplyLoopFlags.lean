import Proofs.BeatsRep
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.BellmanFordExec
set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem cls_flags0 (W1 W2 op qa qb : Nat) (Z3 Z4 Z5 Z6 x : Int) (X0 X1 X2 X3 X4 X5 X6 : Int) (hX0 : X0 = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0)) (hX1 : X1 = (if (((op : Int) = 0) ∧ (Z3 ≤ x)) then 1 else X0)) (hX2 : X2 = (if (((op : Int) = 1) ∧ (x ≤ Z5)) then 1 else X1)) (hX3 : X3 = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0)) (hX4 : X4 = (if (((op : Int) = 0) ∧ (x ≤ Z4)) then 0 else 1)) (hX5 : X5 = (if (((op : Int) = 1) ∧ (Z6 ≤ x)) then 0 else X4)) (hX6 : X6 = (if (((X2 = 0) ∧ (X3 = 1)) ∧ (X5 = 1)) then 1 else 0)) (hop : op = 0) :
    X2 = (if stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 then 1 else 0) ∧ X6 = (if (¬ stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 ∧ wholeP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2) then 1 else 0) := by
  subst hop
  rw [hX6, hX5, hX4, hX3, hX2, hX1, hX0]
  simp only [stopP, wholeP]
  by_cases h1 : (qb : Int) ≤ (W1 : Int) <;> by_cases h2 : (W2 : Int) ≤ (qa : Int) <;> by_cases h3 : Z3 ≤ x <;> by_cases h3' : x ≤ Z5 <;>
    by_cases h4 : (qa : Int) ≤ (W1 : Int) <;> by_cases h5 : (W2 : Int) ≤ (qb : Int) <;> by_cases h6 : Z4 < x <;> by_cases h6' : x < Z6 <;>
    simp [h1, h2, h3, h3', h4, h5, h6, h6'] <;> omega

set_option maxHeartbeats 0 in
theorem cls_flags1 (W1 W2 op qa qb : Nat) (Z3 Z4 Z5 Z6 x : Int) (X0 X1 X2 X3 X4 X5 X6 : Int) (hX0 : X0 = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0)) (hX1 : X1 = (if (((op : Int) = 0) ∧ (Z3 ≤ x)) then 1 else X0)) (hX2 : X2 = (if (((op : Int) = 1) ∧ (x ≤ Z5)) then 1 else X1)) (hX3 : X3 = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0)) (hX4 : X4 = (if (((op : Int) = 0) ∧ (x ≤ Z4)) then 0 else 1)) (hX5 : X5 = (if (((op : Int) = 1) ∧ (Z6 ≤ x)) then 0 else X4)) (hX6 : X6 = (if (((X2 = 0) ∧ (X3 = 1)) ∧ (X5 = 1)) then 1 else 0)) (hop : op = 1) :
    X2 = (if stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 then 1 else 0) ∧ X6 = (if (¬ stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 ∧ wholeP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2) then 1 else 0) := by
  subst hop
  rw [hX6, hX5, hX4, hX3, hX2, hX1, hX0]
  simp only [stopP, wholeP]
  by_cases h1 : (qb : Int) ≤ (W1 : Int) <;> by_cases h2 : (W2 : Int) ≤ (qa : Int) <;> by_cases h3 : Z3 ≤ x <;> by_cases h3' : x ≤ Z5 <;>
    by_cases h4 : (qa : Int) ≤ (W1 : Int) <;> by_cases h5 : (W2 : Int) ≤ (qb : Int) <;> by_cases h6 : Z4 < x <;> by_cases h6' : x < Z6 <;>
    simp [h1, h2, h3, h3', h4, h5, h6, h6'] <;> omega

set_option maxHeartbeats 0 in
theorem cls_flags2 (W1 W2 op qa qb : Nat) (Z3 Z4 Z5 Z6 x : Int) (X0 X1 X2 X3 X4 X5 X6 : Int) (hX0 : X0 = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0)) (hX1 : X1 = (if (((op : Int) = 0) ∧ (Z3 ≤ x)) then 1 else X0)) (hX2 : X2 = (if (((op : Int) = 1) ∧ (x ≤ Z5)) then 1 else X1)) (hX3 : X3 = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0)) (hX4 : X4 = (if (((op : Int) = 0) ∧ (x ≤ Z4)) then 0 else 1)) (hX5 : X5 = (if (((op : Int) = 1) ∧ (Z6 ≤ x)) then 0 else X4)) (hX6 : X6 = (if (((X2 = 0) ∧ (X3 = 1)) ∧ (X5 = 1)) then 1 else 0)) (hop : op = 2) :
    X2 = (if stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 then 1 else 0) ∧ X6 = (if (¬ stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 ∧ wholeP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2) then 1 else 0) := by
  subst hop
  rw [hX6, hX5, hX4, hX3, hX2, hX1, hX0]
  simp only [stopP, wholeP]
  by_cases h1 : (qb : Int) ≤ (W1 : Int) <;> by_cases h2 : (W2 : Int) ≤ (qa : Int) <;> by_cases h3 : Z3 ≤ x <;> by_cases h3' : x ≤ Z5 <;>
    by_cases h4 : (qa : Int) ≤ (W1 : Int) <;> by_cases h5 : (W2 : Int) ≤ (qb : Int) <;> by_cases h6 : Z4 < x <;> by_cases h6' : x < Z6 <;>
    simp [h1, h2, h3, h3', h4, h5, h6, h6'] <;> omega

set_option maxHeartbeats 0 in
theorem cls_flags3 (W1 W2 op qa qb : Nat) (Z3 Z4 Z5 Z6 x : Int) (X0 X1 X2 X3 X4 X5 X6 : Int) (hX0 : X0 = (if (((qb : Int) ≤ (W1 : Int)) ∨ ((W2 : Int) ≤ (qa : Int))) then 1 else 0)) (hX1 : X1 = (if (((op : Int) = 0) ∧ (Z3 ≤ x)) then 1 else X0)) (hX2 : X2 = (if (((op : Int) = 1) ∧ (x ≤ Z5)) then 1 else X1)) (hX3 : X3 = (if (((qa : Int) ≤ (W1 : Int)) ∧ ((W2 : Int) ≤ (qb : Int))) then 1 else 0)) (hX4 : X4 = (if (((op : Int) = 0) ∧ (x ≤ Z4)) then 0 else 1)) (hX5 : X5 = (if (((op : Int) = 1) ∧ (Z6 ≤ x)) then 0 else X4)) (hX6 : X6 = (if (((X2 = 0) ∧ (X3 = 1)) ∧ (X5 = 1)) then 1 else 0)) (hop : op = 3) :
    X2 = (if stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 then 1 else 0) ∧ X6 = (if (¬ stopP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2 ∧ wholeP op qa qb x ⟨Z3, Z4, 0, Z5, Z6, 0⟩ W1 W2) then 1 else 0) := by
  subst hop
  rw [hX6, hX5, hX4, hX3, hX2, hX1, hX0]
  simp only [stopP, wholeP]
  by_cases h1 : (qb : Int) ≤ (W1 : Int) <;> by_cases h2 : (W2 : Int) ≤ (qa : Int) <;> by_cases h3 : Z3 ≤ x <;> by_cases h3' : x ≤ Z5 <;>
    by_cases h4 : (qa : Int) ≤ (W1 : Int) <;> by_cases h5 : (W2 : Int) ≤ (qb : Int) <;> by_cases h6 : Z4 < x <;> by_cases h6' : x < Z6 <;>
    simp [h1, h2, h3, h3', h4, h5, h6, h6'] <;> omega

end Proofs.BeatsRep
