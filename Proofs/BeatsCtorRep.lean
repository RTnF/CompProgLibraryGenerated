import Proofs.BeatsOps
import Proofs.BeatsCtorTop
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

theorem innerS_eq {lo hi : Nat} {sk : Sk} (h : Shape lo hi sk) : innerS sk = hi - lo - 1 := by
  induction sk generalizing lo hi with
  | leaf => have : hi = lo + 1 := h; simp [innerS, this]
  | node l r ihl ihr =>
    obtain ⟨hin, hl, hr⟩ := h
    have a := ihl hl
    have b := ihr hr
    simp only [innerS]
    omega

theorem height_le_inner : ∀ (t : BT), t.height ≤ innerS t.skel
  | .leaf _ => by simp [BT.height, BT.skel, innerS]
  | .node _ _ l r => by
    have a := height_le_inner l
    have b := height_le_inner r
    simp only [BT.height, BT.skel, innerS]
    omega

theorem leafOK_build (a : List Int) : ∀ (n lo hi : Nat), hi - lo = n → LeafOK (buildBT a lo hi) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi hn
    unfold buildBT
    by_cases hc : lo + 1 < hi
    · rw [if_pos hc]
      have h1 := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl
      have h2 := ih (hi - (lo + hi) / 2) (by omega) ((lo + hi) / 2) hi rfl
      exact ⟨h1, h2⟩
    · rw [if_neg hc]
      exact ⟨rfl, rfl, rfl⟩


theorem new0_wf : Wf SegmentTreeBeats_new0.body = true := by decide
theorem new0_nb : Nb SegmentTreeBeats_new0.body ≤ 100 := by decide
theorem new0_body : SegmentTreeBeats_new0.body = CtorCmd 16 := rfl

set_option maxHeartbeats 64000000 in
theorem ctor_rep (mv : MV) (hnv : mv.nv = 16) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (a : List Int) (n L : Nat) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hLM : L < M31) (hAlen : a.length = n) (hAr : InRange a)
    (b0 : BS) (hV0 : ValidOK b0) (hLens0 : Lens b0 L) (hlo0 : L ≤ b0.lo.length) (hhi0 : L ≤ b0.hi.length)
    (h0 : ∀ j, b0.mxv.getD j 0 = 0) (h1 : ∀ j, b0.smx.getD j 0 = 0) (h2 : ∀ j, b0.mxc.getD j 0 = 0) (h3 : ∀ j, b0.mnv.getD j 0 = 0)
    (h4 : ∀ j, b0.smn.getD j 0 = 0) (h5 : ∀ j, b0.mnc.getD j 0 = 0) (h6 : ∀ j, b0.len.getD j 0 = 0) (h7 : ∀ j, b0.ladd.getD j 0 = 0)
    (h8 : ∀ j, j < b0.lval.length → b0.lval.getD j 0 = INF) (h9 : ∀ j, b0.lo.getD j 0 = 0) (h10 : ∀ j, b0.hi.getD j 0 = 0) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_new0.body (gS P []) (VVA a b0) = some r ∧ r.ret = none ∧
      r.ps = gS P (CtCells INF n 0 (4 * n)) ∧ r.vv = VVA a bf ∧
      r.cost ≤ 4 * n * 45414 + 100 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 * n * 18 + 10 ∧
      BRep n L a bf (buildBT a 0 n) Hf := by
  obtain ⟨bf, Hf, F, r, h1', h2', h3', h4', hH, hAg, hV, hLn, hlo, hhi, hLen, hc, hw⟩ :=
    ct_exec mv hnv [] hty hty32 hty15 P a n L hn hL8 hLM hAlen hAr b0 hV0 hLens0 hlo0 hhi0 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hT := buildBT_spec a hAr n 0 n (by omega) (by omega) (by omega)
  have h0rng : rngOf n 0 = (0, n) := by simp [rngOf]
  have hexec : pexecM mv F SegmentTreeBeats_new0.body (gS P []) (VVA a b0) = some r := by
    rw [new0_body]; simpa [hnv] using h1'
  have hnd := (cmd_need mv _ new0_wf F _ (VVA a b0) r hexec).1
  have hdrop : (a.drop 0).take (n - 0) = a := by simp; rw [← hAlen]; exact List.take_length
  refine ⟨bf, Hf, F, r, hexec, h2', h3', h4', hc, ?_, hw, ?_⟩
  · simp [szP, gS] at hnd; have := new0_nb; omega
  · have hsh : Shape 0 n (buildBT a 0 n).skel := hT.2
    have hin := innerS_eq hsh
    have hhl := height_le_inner (buildBT a 0 n)
    refine ⟨hAg, hsh, leafOK_build a n 0 n (by omega), by rw [hdrop] at hT; exact hT.1, hH, hV, hLn,
      idxOK_build n hn L hL8 _ 0 0 n hsh h0rng, hLen, ?_, ?_, ?_⟩
    · omega
    · unfold innerOf; omega
    · omega

end Proofs.BeatsRep
