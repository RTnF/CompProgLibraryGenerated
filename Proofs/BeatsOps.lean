import Proofs.BeatsRep2
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec (M31 cs)
set_option maxRecDepth 100000

theorem chmin_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15) (Ev : Env mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 0 qa qb x L) (hx : -INF < x ∧ x < INF)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRep n L ys b t H) (hsafe : chminSafe qa qb x t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_chmin.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 0 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧ BRep n L (rangeMin 0 qa qb x ys) bf (chminBT qa qb x t 0 n) Hf := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, hlen⟩ :=
    chmin_exec hnv Ev hx t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp
      (by have := R.ne; omega) hlh
  have htr := trav_props (clsMin qa qb x) (capMaxBT x) (skel_capMaxBT x) (LeafOK_capMaxBT x) t.height t (Nat.le_refl _) 0 n R.leaf
  rw [chminBT_eq]
  have hinv := Inv.chmin qa qb x hx.1 t 0 n ys R.inv R.shape hsafe
  rw [chminBT_eq] at hinv
  refine ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  exact BRep.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen

theorem chmax_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15) (Ev : Env mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 1 qa qb x L) (hx : -INF < x ∧ x < INF)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRep n L ys b t H) (hsafe : chmaxSafe qa qb x t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_chmax.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 1 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧ BRep n L (rangeMap (fun v => max v x) 0 qa qb ys) bf (chmaxBT qa qb x t 0 n) Hf := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, hlen⟩ :=
    chmax_exec hnv Ev hx t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp
      (by have := R.ne; omega) hlh
  have htr := trav_props (clsMax qa qb x) (capMinBT x) (skel_capMinBT x) (LeafOK_capMinBT x) t.height t (Nat.le_refl _) 0 n R.leaf
  rw [chmaxBT_eq]
  have hinv := Inv.chmax qa qb x hx.2 t 0 n ys R.inv R.shape hsafe
  rw [chmaxBT_eq] at hinv
  refine ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  exact BRep.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen

theorem add_val_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15) (Ev : Env mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 2 qa qb x L) (hx : -INF < x ∧ x < INF)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRep n L ys b t H) (hsafe : addSafeRec qa qb x t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_add_val.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 2 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧ BRep n L (rangeMap (fun v => v + x) 0 qa qb ys) bf (addRec qa qb x t 0 n) Hf := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, hlen⟩ :=
    add_val_exec hnv Ev hx t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp
      (by have := R.ne; omega) hlh
  have htr := trav_props (clsRange qa qb) (addBT x) (skel_addBT x) (LeafOK_addBT x) t.height t (Nat.le_refl _) 0 n R.leaf
  rw [addRec_eq]
  have hinv := Inv.add_range qa qb x t 0 n ys R.inv R.shape hsafe
  rw [addRec_eq] at hinv
  refine ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  exact BRep.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen

theorem update_val_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (hnv : mv.nv = 15) (Ev : Env mv [cs inf, ci n, ci qa, ci qb, cs x] P inf n 3 qa qb x L) (hx : -INF < x ∧ x < INF)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRep n L ys b t H) (hsafe : setSafeRec qa qb x t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_update_val.body (gS P [cs inf, ci n, ci qa, ci qb, cs x]) (VVB b) = some r ∧
      r.ret = none ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb, cs x] ++ LCells inf n 3 qa qb x 0 0) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 117614 + 4 + (innerOf t * 24794 + 4) + 3000 + 12 ∧ r.need ≤ P.length + 345 ∧
      r.wk ≤ nodesOf t * 47 + innerOf t * 6 + 3 ∧ BRep n L (rangeMap (fun _ => x) 0 qa qb ys) bf (setRec qa qb x t 0 n) Hf := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, hlen⟩ :=
    update_val_exec hnv Ev hx t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp
      (by have := R.ne; omega) hlh
  have htr := trav_props (clsRange qa qb) (setBT x) (skel_setBT x) (LeafOK_setBT x) t.height t (Nat.le_refl _) 0 n R.leaf
  rw [setRec_eq]
  have hinv := Inv.set_range qa qb x hx t 0 n ys R.inv R.shape hsafe
  rw [setRec_eq] at hinv
  refine ⟨bf, Hf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  exact BRep.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen

theorem calc_max_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {L : Nat}
    (hnv : mv.nv = 15) (Ev : Env mv [cs inf, ci n, ci qa, ci qb] P inf n 0 qa qb 0 L)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRep n L ys b t H) (hsafe : calcSafe qa qb t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_calc_max.body (gS P [cs inf, ci n, ci qa, ci qb]) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb] ++ (CCells inf n 0 qa qb xf 0 ++ [cs xf])) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 + 10 ∧ r.need ≤ P.length + 410 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      xf = max (-INF) (rangeMaxOf 0 qa qb ys) ∧ BRep n L ys bf (calcMaxBT qa qb t 0 n).1 Hf ∧ s64.valid xf = true := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, h12, hlen, hvx⟩ :=
    calc_max_exec hnv Ev t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp hlh
  have htr := calcMax_props qa qb t.height t (Nat.le_refl _) 0 n R.leaf
  obtain ⟨hinv, hval⟩ := Inv.calcMax qa qb t 0 n ys R.inv R.shape hsafe
  refine ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_, ?_, hvx⟩
  · rw [h12]; simp only [specMax]; rw [hval]
  · exact BRep.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen
theorem calc_min_rep {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {L : Nat}
    (hnv : mv.nv = 15) (Ev : Env mv [cs inf, ci n, ci qa, ci qb] P inf n 1 qa qb 0 L)
    {ys : List Int} {b : BS} {t : BT} {H : Heap} (R : BRep n L ys b t H) (hsafe : calcSafe qa qb t 0 n) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_calc_min.body (gS P [cs inf, ci n, ci qa, ci qb]) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb] ++ (CCells inf n 1 qa qb xf 0 ++ [cs xf])) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 + 10 ∧ r.need ≤ P.length + 410 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      xf = min INF (rangeMinOf 0 qa qb ys) ∧ BRep n L ys bf (calcMinBT qa qb t 0 n).1 Hf ∧ s64.valid xf = true := by
  have hlh : 0 ≤ n ∧ 2 * n < M31 := ⟨Nat.zero_le _, R.nM⟩
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hag, h12, hlen, hvx⟩ :=
    calc_min_exec hnv Ev t ys b H R.agree R.shape R.leaf R.inv hsafe (Ev.hinfI ▸ R.hrel) R.valid R.lens R.idx R.lenok R.sp hlh
  have htr := calcMin_props qa qb t.height t (Nat.le_refl _) 0 n R.leaf
  obtain ⟨hinv, hval⟩ := Inv.calcMin qa qb t 0 n ys R.inv R.shape hsafe
  refine ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, ?_, ?_, hvx⟩
  · rw [h12]; simp only [specMin]; rw [hval]
  · exact BRep.step R htr.1 htr.2 hinv hag (Ev.hinfI ▸ h8) h9 h10 hlen

end Proofs.BeatsRep
