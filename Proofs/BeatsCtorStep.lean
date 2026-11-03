import Proofs.BeatsCtorInv
import Proofs.BeatsExec_CtLoop
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

def ctB (b : BS) (k ne : Nat) (X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 : Int) : BS :=
  uk12 (uk11 (uk10 (uk9 (uk8 (uk7 (uk6 (uk5 (uk4 (uk3 (uk2 (uk1 b k X3) k X4) k X5) k X6) k X7) k X8) k X9) (2 * k + 1) X10) (2 * k + 1) X11) (2 * k + 2) X12) (2 * k + 2) X13) ne (k : Int)

theorem getD_set2 (l : List Int) (i1 : Nat) (v1 : Int) (i2 : Nat) (v2 : Int) (h1 : i1 < l.length) (h2 : i2 < l.length) (j : Nat) :
    ((l.set i1 v1).set i2 v2).getD j 0 = if j = i2 then v2 else if j = i1 then v1 else l.getD j 0 := by
  rw [getD_set_ite _ _ _ (by simpa using h2), getD_set_ite _ _ _ h1]

theorem ct_step_inv (a : List Int) (n : Nat) (inf : Int) (hinfI : inf = INF) (b : BS) (k ne : Nat) (hI : CtInv a n inf b k ne)
    (hl8 : 2 * k + 2 < b.lo.length) (hl9 : 2 * k + 2 < b.hi.length) (hlen : k < b.len.length) (hmx : k < b.mxv.length)
    (hmn : k < b.mnv.length) (hsmx : k < b.smx.length) (hsmn : k < b.smn.length) (hmc : k < b.mxc.length) (hmnc : k < b.mnc.length)
    (hent : ne < b.ent.length)
    (W0 W1 : Nat) (hD_W0 : b.lo.getD k 0 = (W0 : Int)) (hD_W1 : b.hi.getD k 0 = (W1 : Int))
    (Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 : Int) (hD_Z2 : b.len.getD k 0 = Z2) (hD_Z3 : a.getD W0 0 = Z3) (hD_Z4 : b.mxv.getD k 0 = Z4)
    (hD_Z5 : b.mnv.getD k 0 = Z5) (hD_Z6 : b.smx.getD k 0 = Z6) (hD_Z7 : b.smn.getD k 0 = Z7) (hD_Z8 : b.mxc.getD k 0 = Z8)
    (hD_Z9 : b.mnc.getD k 0 = Z9)
    (W10 W11 W12 W13 : Nat) (hD_W10 : b.lo.getD (2 * k + 1) 0 = (W10 : Int)) (hD_W11 : b.hi.getD (2 * k + 1) 0 = (W11 : Int))
    (hD_W12 : b.lo.getD (2 * k + 2) 0 = (W12 : Int)) (hD_W13 : b.hi.getD (2 * k + 2) 0 = (W13 : Int))
    (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 : Int)
    (hX0 : X0 = (if ((W0 : Int) < (W1 : Int)) then 1 else 0))
    (hX1 : X1 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) = 1)) then 1 else 0))
    (hX2 : X2 = (if ((X0 = 1) ∧ (((W1 : Int) - (W0 : Int)) ≠ 1)) then 1 else 0))
    (hX3 : X3 = (if (X0 = 1) then ((W1 : Int) - (W0 : Int)) else Z2))
    (hX4 : X4 = (if (X1 = 1) then Z3 else Z4)) (hX5 : X5 = (if (X1 = 1) then Z3 else Z5))
    (hX6 : X6 = (if (X1 = 1) then (-inf) else Z6)) (hX7 : X7 = (if (X1 = 1) then inf else Z7))
    (hX8 : X8 = (if (X1 = 1) then 1 else Z8)) (hX9 : X9 = (if (X1 = 1) then 1 else Z9))
    (hX10 : X10 = (if (X2 = 1) then (W0 : Int) else (W10 : Int)))
    (hX11 : X11 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W11 : Int)))
    (hX12 : X12 = (if (X2 = 1) then (((W0 : Int) + (W1 : Int)) / 2) else (W12 : Int)))
    (hX13 : X13 = (if (X2 = 1) then (W1 : Int) else (W13 : Int))) :
    X2 = (if isInnerAt n k then 1 else 0) ∧
    CtInv a n inf (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13) (k + 1) (ne + (if isInnerAt n k then 1 else 0)) := by
  -- the values read at node `k`
  have eW0 : W0 = (rngOf n k).1 := by
    have := hI.hlo k; rw [hD_W0, if_pos (by omega)] at this; exact_mod_cast this
  have eW1 : W1 = (rngOf n k).2 := by
    have := hI.hhi k; rw [hD_W1, if_pos (by omega)] at this; exact_mod_cast this
  have eZ2 : Z2 = 0 := by have := hI.hlen k; rw [hD_Z2, if_neg (by omega)] at this; exact this
  have eZ4 : Z4 = 0 := by have := hI.hmx k; rw [hD_Z4, if_neg (by omega)] at this; exact this
  have eZ5 : Z5 = 0 := by have := hI.hmn k; rw [hD_Z5, if_neg (by omega)] at this; exact this
  have eZ6 : Z6 = 0 := by have := hI.hsmx k; rw [hD_Z6, if_neg (by omega)] at this; exact this
  have eZ7 : Z7 = 0 := by have := hI.hsmn k; rw [hD_Z7, if_neg (by omega)] at this; exact this
  have eZ8 : Z8 = 0 := by have := hI.hmc k; rw [hD_Z8, if_neg (by omega)] at this; exact this
  have eZ9 : Z9 = 0 := by have := hI.hmnc k; rw [hD_Z9, if_neg (by omega)] at this; exact this
  have eW10 : W10 = 0 := by have := hI.hlo (2 * k + 1); rw [hD_W10, if_neg (by omega)] at this; exact_mod_cast this
  have eW11 : W11 = 0 := by have := hI.hhi (2 * k + 1); rw [hD_W11, if_neg (by omega)] at this; exact_mod_cast this
  have eW12 : W12 = 0 := by have := hI.hlo (2 * k + 2); rw [hD_W12, if_neg (by omega)] at this; exact_mod_cast this
  have eW13 : W13 = 0 := by have := hI.hhi (2 * k + 2); rw [hD_W13, if_neg (by omega)] at this; exact_mod_cast this
  subst eZ2 eZ4 eZ5 eZ6 eZ7 eZ8 eZ9 eW10 eW11 eW12 eW13
  subst eW0 eW1
  have fLen : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).len.getD j 0 = if j = k then X3 else b.len.getD j 0 :=
    fun j => getD_set_ite _ _ _ hlen j
  have fMx : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).mxv.getD j 0 = if j = k then X4 else b.mxv.getD j 0 :=
    fun j => getD_set_ite _ _ _ hmx j
  have fMn : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).mnv.getD j 0 = if j = k then X5 else b.mnv.getD j 0 :=
    fun j => getD_set_ite _ _ _ hmn j
  have fSmx : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).smx.getD j 0 = if j = k then X6 else b.smx.getD j 0 :=
    fun j => getD_set_ite _ _ _ hsmx j
  have fSmn : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).smn.getD j 0 = if j = k then X7 else b.smn.getD j 0 :=
    fun j => getD_set_ite _ _ _ hsmn j
  have fMc : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).mxc.getD j 0 = if j = k then X8 else b.mxc.getD j 0 :=
    fun j => getD_set_ite _ _ _ hmc j
  have fMnc : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).mnc.getD j 0 = if j = k then X9 else b.mnc.getD j 0 :=
    fun j => getD_set_ite _ _ _ hmnc j
  have fLo : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).lo.getD j 0 = if j = 2 * k + 2 then X12 else if j = 2 * k + 1 then X10 else b.lo.getD j 0 :=
    fun j => getD_set2 _ _ _ _ _ (by omega) hl8 j
  have fHi : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).hi.getD j 0 = if j = 2 * k + 2 then X13 else if j = 2 * k + 1 then X11 else b.hi.getD j 0 :=
    fun j => getD_set2 _ _ _ _ _ (by omega) hl9 j
  have fEnt : ∀ j, (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).ent.getD j 0 = if j = ne then (k : Int) else b.ent.getD j 0 :=
    fun j => getD_set_ite _ _ _ hent j
  have fLadd : (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).ladd = b.ladd := rfl
  have fLval : (ctB b k ne X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13).lval = b.lval := rfl
  -- case analysis on the node
  have hL := rngOf_left n k
  have hR := rngOf_right n k
  have hnotin : ∀ (c : ¬ ((rngOf n k).1 + 1 < (rngOf n k).2)), (rngOf n (2 * k + 1) = (0, 0)) ∧ rngOf n (2 * k + 2) = (0, 0) := by
    intro c; rw [if_neg c] at hL hR; exact ⟨hL, hR⟩
  refine ?_
  rcases rngOf_cases n k with hlt | hz
  · by_cases hin : (rngOf n k).1 + 1 < (rngOf n k).2
    · -- inner node
      rw [if_pos hin] at hL hR
      have eX0 : X0 = 1 := by rw [hX0, if_pos (by exact_mod_cast hlt)]
      have eX1 : X1 = 0 := by
        rw [hX1, if_neg]; rintro ⟨_, h2⟩; omega
      have eX2 : X2 = 1 := by rw [hX2, if_pos ⟨eX0, by omega⟩]
      rw [eX0] at hX3
      rw [eX1] at hX4 hX5 hX6 hX7 hX8 hX9
      rw [eX2] at hX10 hX11 hX12 hX13
      simp only [if_true, if_false, one_ne_zero, zero_ne_one, ite_true, ite_false] at hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13
      have hinn : isInnerAt n k := hin
      refine ⟨by rw [eX2, if_pos hinn], ?_⟩
      have hLLr : LLr n (k + 1) = k :: LLr n k := by simp [LLr, hinn]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hLLr, if_pos hinn]
        exact EntRep_push b _ ne (LLr n k) k hI.hent (fun i hi => by rw [fEnt, if_neg (by have := hI.hent.1; omega)])
          (by rw [fEnt, if_pos rfl])
      · intro j
        rw [fLo j, hI.hlo j]
        by_cases h2 : j = 2 * k + 2
        · subst h2; rw [if_pos rfl, if_pos (show 2 * k + 2 ≤ 2 * (k + 1) by omega), hR, hX12]; (try simp only); (try omega)
        · by_cases h1 : j = 2 * k + 1
          · subst h1; rw [if_neg (by omega), if_pos rfl, if_pos (show 2 * k + 1 ≤ 2 * (k + 1) by omega), hL, hX10]; try simp only
          · rw [if_neg h2, if_neg h1]
            by_cases hj : j ≤ 2 * k
            · rw [if_pos hj, if_pos (by omega)]
            · rw [if_neg hj, if_neg (by omega)]
      · intro j
        rw [fHi j, hI.hhi j]
        by_cases h2 : j = 2 * k + 2
        · subst h2; rw [if_pos rfl, if_pos (show 2 * k + 2 ≤ 2 * (k + 1) by omega), hR, hX13]
        · by_cases h1 : j = 2 * k + 1
          · subst h1; rw [if_neg (by omega), if_pos rfl, if_pos (show 2 * k + 1 ≤ 2 * (k + 1) by omega), hL, hX11]; (try simp only); (try omega)
          · rw [if_neg h2, if_neg h1]
            by_cases hj : j ≤ 2 * k
            · rw [if_pos hj, if_pos (by omega)]
            · rw [if_neg hj, if_neg (by omega)]
      · intro j
        rw [fLen j, hI.hlen j]
        by_cases hj : j = k
        · subst hj; rw [if_pos rfl, if_pos (by omega), hX3]; omega
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · rw [if_pos hj2, if_pos (by omega)]
          · rw [if_neg hj2, if_neg (by omega)]
      · intro j
        rw [fMx j, hI.hmx j]
        by_cases hj : j = k
        · subst hj
          have : ¬ isLeafAt n j := fun hh => hh.2 hinn
          rw [if_pos rfl, if_neg (fun hh => this hh.2), hX4]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMn j, hI.hmn j]
        by_cases hj : j = k
        · subst hj
          have : ¬ isLeafAt n j := fun hh => hh.2 hinn
          rw [if_pos rfl, if_neg (fun hh => this hh.2), hX5]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fSmx j, hI.hsmx j]
        by_cases hj : j = k
        · subst hj
          have : ¬ isLeafAt n j := fun hh => hh.2 hinn
          rw [if_pos rfl, if_neg (fun hh => this hh.2), hX6]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fSmn j, hI.hsmn j]
        by_cases hj : j = k
        · subst hj
          have : ¬ isLeafAt n j := fun hh => hh.2 hinn
          rw [if_pos rfl, if_neg (fun hh => this hh.2), hX7]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMc j, hI.hmc j]
        by_cases hj : j = k
        · subst hj
          have : ¬ isLeafAt n j := fun hh => hh.2 hinn
          rw [if_pos rfl, if_neg (fun hh => this hh.2), hX8]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMnc j, hI.hmnc j]
        by_cases hj : j = k
        · subst hj
          have : ¬ isLeafAt n j := fun hh => hh.2 hinn
          rw [if_pos rfl, if_neg (fun hh => this hh.2), hX9]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j; rw [fLadd]; exact hI.hladd j
      · intro j; rw [fLval]; exact hI.hlval j
    · -- leaf
      have hleafk : isLeafAt n k := ⟨hlt, hin⟩
      have hinn : ¬ isInnerAt n k := hin
      have eX0 : X0 = 1 := by rw [hX0, if_pos (by exact_mod_cast hlt)]
      have eX1 : X1 = 1 := by rw [hX1, if_pos ⟨eX0, by omega⟩]
      have eX2 : X2 = 0 := by rw [hX2, if_neg]; rintro ⟨_, h2⟩; omega
      rw [eX0] at hX3
      rw [eX1] at hX4 hX5 hX6 hX7 hX8 hX9
      rw [eX2] at hX10 hX11 hX12 hX13
      simp only [if_true, if_false, one_ne_zero, zero_ne_one] at hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13
      refine ⟨by rw [eX2, if_neg hinn], ?_⟩
      have hLLr : LLr n (k + 1) = LLr n k := by simp [LLr, hinn]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hLLr, if_neg hinn, Nat.add_zero]
        exact EntRep_keep b _ ne (LLr n k) hI.hent (fun i hi => by rw [fEnt, if_neg (by have := hI.hent.1; omega)])
      · intro j
        rw [fLo j, hI.hlo j]
        by_cases h2 : j = 2 * k + 2
        · subst h2; rw [if_pos rfl, if_pos (show 2 * k + 2 ≤ 2 * (k + 1) by omega), (hnotin hin).2, hX12]
        · by_cases h1 : j = 2 * k + 1
          · subst h1; rw [if_neg (by omega), if_pos rfl, if_pos (show 2 * k + 1 ≤ 2 * (k + 1) by omega), (hnotin hin).1, hX10]
          · rw [if_neg h2, if_neg h1]
            by_cases hj : j ≤ 2 * k
            · rw [if_pos hj, if_pos (by omega)]
            · rw [if_neg hj, if_neg (by omega)]
      · intro j
        rw [fHi j, hI.hhi j]
        by_cases h2 : j = 2 * k + 2
        · subst h2; rw [if_pos rfl, if_pos (show 2 * k + 2 ≤ 2 * (k + 1) by omega), (hnotin hin).2, hX13]
        · by_cases h1 : j = 2 * k + 1
          · subst h1; rw [if_neg (by omega), if_pos rfl, if_pos (show 2 * k + 1 ≤ 2 * (k + 1) by omega), (hnotin hin).1, hX11]
          · rw [if_neg h2, if_neg h1]
            by_cases hj : j ≤ 2 * k
            · rw [if_pos hj, if_pos (by omega)]
            · rw [if_neg hj, if_neg (by omega)]
      · intro j
        rw [fLen j, hI.hlen j]
        by_cases hj : j = k
        · subst hj; rw [if_pos rfl, if_pos (by omega), hX3]; omega
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · rw [if_pos hj2, if_pos (by omega)]
          · rw [if_neg hj2, if_neg (by omega)]
      · intro j
        rw [fMx j, hI.hmx j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_pos ⟨by omega, hleafk⟩,  hX4]; exact hD_Z3.symm
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMn j, hI.hmn j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_pos ⟨by omega, hleafk⟩,  hX5]; exact hD_Z3.symm
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fSmx j, hI.hsmx j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_pos ⟨by omega, hleafk⟩,  hX6]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fSmn j, hI.hsmn j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_pos ⟨by omega, hleafk⟩,  hX7]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMc j, hI.hmc j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_pos ⟨by omega, hleafk⟩,  hX8]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMnc j, hI.hmnc j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_pos ⟨by omega, hleafk⟩,  hX9]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j; rw [fLadd]; exact hI.hladd j
      · intro j; rw [fLval]; exact hI.hlval j
  · -- unused
      have hz0 : (rngOf n k).1 = 0 := by simp [hz]
      have hz1 : (rngOf n k).2 = 0 := by simp [hz]
      have hin : ¬ ((rngOf n k).1 + 1 < (rngOf n k).2) := by omega
      have hnleafk : ¬ isLeafAt n k := fun hh => by have := hh.1; omega
      have hinn : ¬ isInnerAt n k := hin
      have eX0 : X0 = 0 := by rw [hX0, if_neg]; omega
      have eX1 : X1 = 0 := by rw [hX1, if_neg]; rintro ⟨h1, _⟩; omega
      have eX2 : X2 = 0 := by rw [hX2, if_neg]; rintro ⟨h1, _⟩; omega
      rw [eX0] at hX3
      rw [eX1] at hX4 hX5 hX6 hX7 hX8 hX9
      rw [eX2] at hX10 hX11 hX12 hX13
      simp only [if_true, if_false, one_ne_zero, zero_ne_one] at hX3 hX4 hX5 hX6 hX7 hX8 hX9 hX10 hX11 hX12 hX13
      refine ⟨by rw [eX2, if_neg hinn], ?_⟩
      have hLLr : LLr n (k + 1) = LLr n k := by simp [LLr, hinn]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hLLr, if_neg hinn, Nat.add_zero]
        exact EntRep_keep b _ ne (LLr n k) hI.hent (fun i hi => by rw [fEnt, if_neg (by have := hI.hent.1; omega)])
      · intro j
        rw [fLo j, hI.hlo j]
        by_cases h2 : j = 2 * k + 2
        · subst h2; rw [if_pos rfl, if_pos (show 2 * k + 2 ≤ 2 * (k + 1) by omega), (hnotin hin).2, hX12]
        · by_cases h1 : j = 2 * k + 1
          · subst h1; rw [if_neg (by omega), if_pos rfl, if_pos (show 2 * k + 1 ≤ 2 * (k + 1) by omega), (hnotin hin).1, hX10]
          · rw [if_neg h2, if_neg h1]
            by_cases hj : j ≤ 2 * k
            · rw [if_pos hj, if_pos (by omega)]
            · rw [if_neg hj, if_neg (by omega)]
      · intro j
        rw [fHi j, hI.hhi j]
        by_cases h2 : j = 2 * k + 2
        · subst h2; rw [if_pos rfl, if_pos (show 2 * k + 2 ≤ 2 * (k + 1) by omega), (hnotin hin).2, hX13]
        · by_cases h1 : j = 2 * k + 1
          · subst h1; rw [if_neg (by omega), if_pos rfl, if_pos (show 2 * k + 1 ≤ 2 * (k + 1) by omega), (hnotin hin).1, hX11]
          · rw [if_neg h2, if_neg h1]
            by_cases hj : j ≤ 2 * k
            · rw [if_pos hj, if_pos (by omega)]
            · rw [if_neg hj, if_neg (by omega)]
      · intro j
        rw [fLen j, hI.hlen j]
        by_cases hj : j = k
        · subst hj; rw [if_pos rfl, if_pos (by omega), hX3]; omega
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · rw [if_pos hj2, if_pos (by omega)]
          · rw [if_neg hj2, if_neg (by omega)]
      · intro j
        rw [fMx j, hI.hmx j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_neg (fun hh => hnleafk hh.2),  hX4]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMn j, hI.hmn j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_neg (fun hh => hnleafk hh.2),  hX5]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fSmx j, hI.hsmx j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_neg (fun hh => hnleafk hh.2),  hX6]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fSmn j, hI.hsmn j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_neg (fun hh => hnleafk hh.2),  hX7]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMc j, hI.hmc j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_neg (fun hh => hnleafk hh.2),  hX8]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j
        rw [fMnc j, hI.hmnc j]
        by_cases hj : j = k
        · subst hj
          rw [if_pos rfl, if_neg (fun hh => hnleafk hh.2),  hX9]
        · rw [if_neg hj]
          by_cases hj2 : j < k
          · simp [hj2, show j < k + 1 by omega]
          · simp [hj2, show ¬ j < k + 1 by omega]
      · intro j; rw [fLadd]; exact hI.hladd j
      · intro j; rw [fLval]; exact hI.hlval j


/-- The heap with the cells beyond the arrays as the arrays read them (`lval = 0`, i.e. a tag that sets the value 0). -/
def Hlift (L : Nat) (H : Heap) : Heap := fun i => if i < L then H i else (zeroNd, ⟨some 0, 0⟩)

theorem ct_hrel (a : List Int) (n : Nat) (inf : Int) (hinfI : inf = INF) (hn : 1 ≤ n) (b : BS) (nef : Nat)
    (hI : CtInv a n inf b (4 * n) nef) (hL : 4 * n ≤ b.lval.length) : HRel inf b (Hlift b.lval.length (C0 a n)) := by
  intro i
  have hnode : decNd b i = (Hlift b.lval.length (C0 a n) i).1 := by
    unfold decNd Hlift
    rw [hI.hmx i, hI.hsmx i, hI.hmc i, hI.hmn i, hI.hsmn i, hI.hmnc i]
    by_cases hl : isLeafAt n i
    · have hlt := skel_lt n hn i hl.1
      simp only [if_pos (show i < b.lval.length by omega)]
      unfold C0
      simp only [hlt, hl, and_self, if_true, leafNd, hinfI]
    · by_cases hi : i < b.lval.length
      · simp only [if_pos hi]; unfold C0; simp [hl, zeroNd]
      · simp [hi, hl, zeroNd]
  by_cases hi : i < b.lval.length
  · have htag : decTag inf b i = noTag := by
      unfold decTag
      rw [hI.hladd i, hI.hlval i hi, if_pos rfl]
      rfl
    have htag' : (Hlift b.lval.length (C0 a n) i).2 = noTag := by unfold Hlift C0; simp only [if_pos hi]; split <;> rfl
    exact ⟨hnode, fun _ => htag.trans htag'.symm, fun _ => htag⟩
  · have h0 : b.lval.getD i 0 = 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show b.lval.length ≤ i by omega)]
    have hl0 : b.len.getD i 0 ≠ 1 := by
      rw [hI.hlen i, if_neg (by omega)]; simp
    have htag : decTag inf b i = ⟨some 0, 0⟩ := by
      unfold decTag
      rw [hI.hladd i, h0, if_neg (by rw [hinfI]; unfold INF; omega)]
    have htag' : (Hlift b.lval.length (C0 a n) i).2 = ⟨some 0, 0⟩ := by unfold Hlift; simp [hi]
    exact ⟨hnode, fun _ => htag.trans htag'.symm, fun h => absurd h hl0⟩

end Proofs.BeatsRep
