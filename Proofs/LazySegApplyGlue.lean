import Proofs.LazySegApplyExec

namespace Proofs.LazySegApplyGlue
open Proofs.SegTreeMath Proofs.LazySegMath
open Proofs.LazySegChmin (chminMon mi)
open Proofs.LazySegRange
open Proofs.LazySegArith
open Proofs.LazySegBlocks (getD_dflt)
open Proofs.LazySegApplyMath
open Proofs.LazySegApplyLoop
open Proofs.LazySegApplyExec

/-- The array after `chmin f` has been applied on `[l, r)`. -/
def chminRange (A : List Int) (l r : Nat) (f : Int) : List Int :=
  (List.range A.length).map (fun i => if l ≤ i ∧ i < r then mi f (A.getD i 0) else A.getD i 0)

theorem chminRange_length (A : List Int) (l r : Nat) (f : Int) : (chminRange A l r f).length = A.length := by
  simp [chminRange]

theorem chminRange_getD (A : List Int) (l r : Nat) (f : Int) (i : Nat) (hi : i < A.length) :
    (chminRange A l r f).getD i 0 = if l ≤ i ∧ i < r then mi f (A.getD i 0) else A.getD i 0 := by
  simp [chminRange, List.getD_eq_getElem?_getD, hi]

theorem chminRange_allV (A : List Int) (l r : Nat) (f : Int) (hAV : AllV chminMon.toMon A) (hf : chminMon.Fv f) :
    AllV chminMon.toMon (chminRange A l r f) := by
  intro x hx
  simp only [chminRange, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hv : chminMon.V (A.getD i 0) := Proofs.SegTreeMath.getD_V _ A hAV i hi
  split
  · exact chminMon.mp_v _ _ hf hv
  · exact hv

theorem lf_chminRange (A : List Int) (nn l r : Nat) (f : Int) (hA : A.length = nn) :
    ∀ x, nn ≤ x → x < 2 * nn →
      lfA chminMon (chminRange A l r f) nn x = lfCv A nn f (fun x => l + nn ≤ x ∧ x < r + nn) x := by
  intro x hx1 hx2
  unfold lfCv
  unfold lfA
  have hlen : x - nn < (chminRange A l r f).length := by rw [chminRange_length]; omega
  rw [getD_dflt (chminRange A l r f) (x - nn) chminMon.e 0 hlen, chminRange_getD A l r f (x - nn) (by omega),
    getD_dflt A (x - nn) chminMon.e 0 (by omega)]
  by_cases hc : l ≤ x - nn ∧ x - nn < r
  · have hc' : l + nn ≤ x ∧ x < r + nn := by omega
    rw [if_pos hc, if_pos hc']
    rfl
  · have hc' : ¬ (l + nn ≤ x ∧ x < r + nn) := by omega
    rw [if_neg hc, if_neg hc']

/-- The invariant of the `all_apply` loop. -/
def QA (nn l0 r0 : Nat) (A : List Int) (f : Int) (h : Nat) (l r : Nat) (vv : Nat → List Int) : Prop :=
  ∃ j, l = ceilDiv l0 (2 ^ j) ∧ r = r0 / 2 ^ j ∧ l ≤ r ∧ AI nn A f (S2 h l0 r0 0) (cvj l0 r0 j l r) (vv 0) (vv 1)

theorem qa_init (nn l0 r0 : Nat) (A : List Int) (f : Int) (h : Nat) (hlr : l0 ≤ r0) (vv : Nat → List Int)
    (hR : Rep chminMon nn A (vv 0) (vv 1)) (hF : LzFid chminMon (S2 h l0 r0 0) (vv 1)) :
    QA nn l0 r0 A f h l0 r0 vv := by
  refine ⟨0, ?_, ?_, hlr, ai_init nn h l0 r0 A f (vv 0) (vv 1) hR hF⟩
  · simp [ceilDiv]
  · simp

theorem qa_step (nn h l0 r0 : Nat) (A : List Int) (f : Int) (hN : nn = 2 ^ h) (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn)
    (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn) (hf : chminMon.Fv f) (hAV : AllV chminMon.toMon A) (hA : A.length = nn)
    (l r : Nat) (vv : Nat → List Int) (hQ : QA nn l0 r0 A f h l r vv) (hlr : l < r) :
    QA nn l0 r0 A f h (Proofs.SegTreeMath.pl1 l / 2) (Proofs.SegTreeMath.pr1 r / 2) (stepVV nn f l r vv) := by
  obtain ⟨j, hlj, hrj, hle, hAI⟩ := hQ
  have hrN : r ≤ 2 * nn := by rw [hrj]; exact le_trans (Nat.div_le_self _ _) hr.2
  have hV : VOK nn vv := ⟨hAI.1, hAI.2.1, hAI.2.2.1, hAI.2.2.2.1⟩
  have hS := stepVV_ok nn f l r vv hV (fun _ => by omega) (fun _ => by omega) hf
  have hI := ai_iter nn h l0 r0 j l r A f (vv 0) (vv 1) hN hl hr hlj hrj hlr hf hAV hA hAI
  refine ⟨j + 1, ?_, ?_, ?_, ?_⟩
  · rw [ceil_step, ← hlj]; unfold Proofs.SegTreeMath.pl1; split <;> omega
  · rw [floor_step, ← hrj]; unfold Proofs.SegTreeMath.pr1; split <;> omega
  · unfold Proofs.SegTreeMath.pl1 Proofs.SegTreeMath.pr1; split <;> split <;> omega
  · rw [hS.2.1, hS.2.2.1]; exact hI

/-- When the loop has finished, the covered leaves are `[l0, r0)` and the final loop can start. -/
theorem qa_done (nn h l0 r0 : Nat) (A : List Int) (f : Int) (l r : Nat) (vv : Nat → List Int)
    (hQ : QA nn l0 r0 A f h l r vv) (hnlt : ¬ l < r) (l' r' : Nat) (hl' : l' + nn = l0) (hr' : r' + nn = r0)
    (hA : A.length = nn) :
    UI nn (chminRange A l' r' f) (S2 h l0 r0 0) (S2 h l0 r0 0) (vv 0) (vv 1) := by
  obtain ⟨j, hlj, hrj, hle, hAI⟩ := hQ
  have heq : l = r := by omega
  subst heq
  have hF := ai_final nn h l0 r0 j l A f (vv 0) (vv 1) hlj hrj hAI
  obtain ⟨hn, hl, hV, hFa, hS, hE⟩ := hF
  refine ⟨hn, hl, hV, hFa, hS, ?_⟩
  refine ext_congr chminMon _ _ nn _ _ _ (fun x hx1 hx2 => ?_) hE
  rw [lf_chminRange A nn l' r' f hA x hx1 hx2]
  unfold lfCv
  have : (fun x => l' + nn ≤ x ∧ x < r' + nn) = (fun x => l0 ≤ x ∧ x < r0) := by
    funext y; rw [hl', hr']
  rw [this]

theorem uf_step (nn h l0 r0 i : Nat) (A' : List Int) (vv : Nat → List Int) (hN : nn = 2 ^ h)
    (hl : nn ≤ l0 ∧ l0 ≤ 2 * nn) (hr : nn ≤ r0 ∧ r0 ≤ 2 * nn) (hi : 1 ≤ i) (hih : i ≤ h)
    (hU : UI nn A' (S2 h l0 r0 0) (S2 h l0 r0 (i - 1)) (vv 0) (vv 1)) :
    UI nn A' (S2 h l0 r0 0) (S2 h l0 r0 i) (stepUV nn l0 r0 (2 ^ i) vv 0) (stepUV nn l0 r0 (2 ^ i) vv 1) := by
  have hV : VOK nn vv := ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1⟩
  have hhalf : ∀ k, k < 2 ^ (h - i + 1) → 2 * k + 1 < 2 * nn := by
    intro k hk
    have : 2 ^ (h - i + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hV1 := cuVV_ok nn (l0 % 2 ^ i ≠ 0) (l0 / 2 ^ i) vv hV
    (fun hc' => hhalf _ (left_bounds nn h i l0 hN hi hih hl hc').2)
  have hV2 := cuVV_ok nn (r0 % 2 ^ i ≠ 0) ((r0 - 1) / 2 ^ i) _ hV1.1
    (fun hc' => hhalf _ (right_bounds nn h i r0 hN hi hih hr hc').2)
  have e0 : stepUV nn l0 r0 (2 ^ i) vv 0 = cu (r0 % 2 ^ i ≠ 0) (cu (l0 % 2 ^ i ≠ 0) (vv 0) (l0 / 2 ^ i)) ((r0 - 1) / 2 ^ i) := by
    unfold stepUV; rw [hV2.2.1, hV1.2.1]
  have e1 : stepUV nn l0 r0 (2 ^ i) vv 1 = vv 1 := by
    unfold stepUV; rw [hV2.2.2, hV1.2.2]
  rw [e0, e1]
  have hstep := ui_step nn h l0 r0 (i - 1) A' (vv 0) (vv 1) hN hl hr (by omega) hU
  have hi1 : i - 1 + 1 = i := by omega
  rw [hi1] at hstep
  exact hstep

theorem rep_of_uf (nn h l0 r0 : Nat) (A' : List Int) (node lz : List Int)
    (hU : UI nn A' (S2 h l0 r0 0) (S2 h l0 r0 h) node lz) (hA' : A'.length = nn) (hAV : AllV chminMon.toMon A') :
    Rep chminMon nn A' node lz := by
  obtain ⟨hn, hl, hV, hF, hS, hE⟩ := hU
  refine ⟨hn, hl, hA', hV, hF, hAV, ?_⟩
  exact ext_weaken chminMon _ nn _ _ _ _ (fun d _ _ ⟨t, h1, h2, _⟩ => absurd h2 (by omega)) hE

end Proofs.LazySegApplyGlue
