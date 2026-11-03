import Proofs.BeatsExecS
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec

abbrev aRd (o v : Nat) : NExpr := .read s64 (.local v) (bIx o)
abbrev aRdAdd (o v : Nat) : NExpr := .binary s64 .add (aRd o v) (bX o)
abbrev aVar (c : Nat) : NExpr := .variable s64 c
abbrev aAsg (o c : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.assign c s64 (.binary s64 .add (aVar c) (bX o)))) Sk)) Sk
abbrev aDecl (e : NExpr) : Command := .primitive (.declare s64 true e)
abbrev AAt12 (o : Nat) : Command := .sequence (bW 8 (aVar (o + 6)) o) Sk
abbrev AAt11 (o : Nat) : Command := .sequence (bW 7 (aVar (o + 7)) o) (AAt12 o)
abbrev AAt10 (o : Nat) : Command :=
  .sequence (.branch (.binary bT .eq (aVar (o + 6)) (bInf o)) (aAsg o (o + 7)) (aAsg o (o + 6))) (AAt11 o)
abbrev AAt9 (o : Nat) : Command := .sequence (aDecl (aRd o 7)) (AAt10 o)
abbrev AAt8 (o : Nat) : Command := .sequence (aDecl (aRd o 8)) (AAt9 o)
abbrev AAt7 (o : Nat) : Command := .sequence (bW 4 (aVar (o + 5)) o) (AAt8 o)
abbrev AAt6 (o : Nat) : Command := .sequence (.branch (.binary bT .ne (aVar (o + 5)) (bInf o)) (aAsg o (o + 5)) Sk) (AAt7 o)
abbrev AAt5 (o : Nat) : Command := .sequence (aDecl (aRd o 4)) (AAt6 o)
abbrev AAt4 (o : Nat) : Command := .sequence (bW 3 (aRdAdd o 3) o) (AAt5 o)
abbrev AAt3 (o : Nat) : Command := .sequence (bW 1 (aVar (o + 4)) o) (AAt4 o)
abbrev AAt2 (o : Nat) : Command := .sequence (.branch (.binary bT .ne (aVar (o + 4)) (bNInf o)) (aAsg o (o + 4)) Sk) (AAt3 o)
abbrev AAt1 (o : Nat) : Command := .sequence (aDecl (aRd o 1)) (AAt2 o)
abbrev AA (o : Nat) : Command := .sequence (bW 0 (aRdAdd o 0) o) (AAt1 o)

/-- Denotations of the base cells `inf, n, k, x` (cells `o .. o+3` of the list `cl`). -/
theorem dens_base (mv : MV) (P cl : List Cell) (o : Nat) (inf x : Int) (k : Nat) (hk : k < M31)
    (h0 : cl[o]? = some (cs inf)) (h2 : cl[o + 2]? = some (ci k)) (h3 : cl[o + 3]? = some (cs x))
    (hinf : s64.valid inf = true) (hninf : s64.valid (-inf) = true) (hx : s64.valid x = true) (vv : Nat → List Int) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (bIx (mv.nv + o)) = some (k : Int) ∧
    vdenM mv vv (penvN mv.nv (gS P cl)) (bX (mv.nv + o)) = some x ∧
    vdenM mv vv (penvN mv.nv (gS P cl)) (bInf (mv.nv + o)) = some inf ∧
    vdenM mv vv (penvN mv.nv (gS P cl)) (bNInf (mv.nv + o)) = some (-inf) := by
  have E0 : penvN mv.nv (gS P cl) (mv.nv + o) s64 = some inf := by
    have := envs mv P cl o (cs inf) h0 hinf
    simpa using this
  have E2 := envs mv P cl (o + 2) (ci k) h2 (Proofs.BellmanFordExec.i32_valid_nat k hk)
  have E3 := envs mv P cl (o + 3) (cs x) h3 hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vdenM_scalar _ _ _ _ rfl]
    exact cidx_den _ (mv.nv + o + 2) k (by simpa [Nat.add_assoc] using E2) hk
  · rw [vdenM_scalar _ _ _ _ rfl, den_variable]
    simpa [Nat.add_assoc] using E3
  · rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0
  · rw [vdenM_scalar _ _ _ _ rfl, Proofs.BellmanFordPExec.den_unaryP, den_variable, E0, Option.bind_some]
    exact conv_signed s64 rfl rfl _ hninf


theorem set_app_last (l : List Cell) (c c' : Cell) : (l ++ [c]).set l.length c' = l ++ [c'] := by
  rw [List.set_append_right _ _ (by omega)]; simp

theorem set_app_idx (l1 l2 : List Cell) (j : Nat) (c : Cell) (hj : j < l2.length) :
    (l1 ++ l2).set (l1.length + j) c = l1 ++ l2.set j c := by
  rw [List.set_append_right _ _ (by omega)]; simp

def aaB (b : BS) (inf x : Int) (k : Nat) : BS :=
  { b with
    mxv := b.mxv.set k (b.mxv.getD k 0 + x)
    smx := b.smx.set k (if b.smx.getD k 0 ≠ -inf then b.smx.getD k 0 + x else b.smx.getD k 0)
    mnv := b.mnv.set k (b.mnv.getD k 0 + x)
    smn := b.smn.set k (if b.smn.getD k 0 ≠ inf then b.smn.getD k 0 + x else b.smn.getD k 0)
    ladd := b.ladd.set k (if b.lval.getD k 0 = inf then b.ladd.getD k 0 + x else b.ladd.getD k 0)
    lval := b.lval.set k (if b.lval.getD k 0 = inf then b.lval.getD k 0 else b.lval.getD k 0 + x) }


theorem base_lookup (pre ext : List Cell) (inf x : Int) (k n : Nat) :
    (pre ++ [cs inf, ci n, ci k, cs x] ++ ext)[pre.length]? = some (cs inf) ∧
    (pre ++ [cs inf, ci n, ci k, cs x] ++ ext)[pre.length + 2]? = some (ci k) ∧
    (pre ++ [cs inf, ci n, ci k, cs x] ++ ext)[pre.length + 3]? = some (cs x) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [List.getElem?_append_left (by simp)]
    simp [List.getElem?_append_right]

/-- The local `T v = e;` cell `j` of `L0 ++ ext` holds `ext[j]`. -/
theorem ext_lookup (L0 ext : List Cell) (j : Nat) (c : Cell) (h : ext[j]? = some c) :
    (L0 ++ ext)[L0.length + j]? = some c := by
  rw [List.getElem?_append_right (by omega)]
  simpa using h


theorem getD_mem_valid (l : List Int) (k : Nat) (hk : k < l.length) (h : ∀ w ∈ l, s64.valid w = true) :
    s64.valid (l.getD k 0) = true :=
  h _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _)

/-- A local cell variable `c = mv.nv + j` holding `v`. -/
theorem den_cellvar (mv : MV) (P L : List Cell) (j c : Nat) (hc : c = mv.nv + j) (v : Int) (h : L[j]? = some ⟨s64, v⟩)
    (hv : s64.valid v = true) (vv : Nat → List Int) :
    vdenM mv vv (penvN mv.nv (gS P L)) (aVar c) = some v := by
  rw [vdenM_scalar _ _ _ _ rfl, den_variable, hc]
  exact envs mv P L j ⟨s64, v⟩ h hv

/-- `v[k]` as a value. -/
theorem den_rd (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (v : Nat) (hv : v < mv.nv)
    (hty : mv.ty v = s64) (a : Int) (iE : NExpr) (hiS : iE.scalarOnly = true) (k : Nat) (hk : k < (vv v).length)
    (hvk : (vv v).getD k 0 = a) (hvlist : ∀ w ∈ vv v, s64.valid w = true) (hd : iE.denote env = some (k : Int)) :
    vdenM mv vv env (.read s64 (.local v) iE) = some a := by
  apply rdM_val mv vv env v hv s64 hty.symm iE hiS (by simp [NExpr.scalarOnly]) k hd a
  · rw [← hvk]; exact vec_getI (vv v) k hk
  · rw [hty, ← hvk]; exact getD_mem_valid (vv v) k hk hvlist

/-- Comparison of two scalar expressions with known values. -/
theorem den_cmp (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (op : Binary) (l r : NExpr) (a b : Int)
    (hl : vdenM mv vv env l = some a) (hr : vdenM mv vv env r = some b) (hls : l.scalarOnly = true) (hrs : r.scalarOnly = true) :
    vdenM mv vv env (.binary bT op l r) = bT.convert (binaryValue op a b) := by
  rw [vdenM_scalar _ _ _ _ (by simp [NExpr.scalarOnly, hls, hrs]), den_binary]
  rw [vdenM_scalar _ _ _ _ hls] at hl
  rw [vdenM_scalar _ _ _ _ hrs] at hr
  rw [hl, hr]; rfl

/-- `a + x` as a scalar expression. -/
theorem den_addsc (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (l r : NExpr) (a b : Int)
    (hl : vdenM mv vv env l = some a) (hr : vdenM mv vv env r = some b) (hls : l.scalarOnly = true) (hrs : r.scalarOnly = true)
    (hs : s64.valid (a + b) = true) : vdenM mv vv env (.binary s64 .add l r) = some (a + b) := by
  rw [vdenM_scalar _ _ _ _ (by simp [NExpr.scalarOnly, hls, hrs]), den_binary]
  rw [vdenM_scalar _ _ _ _ hls] at hl
  rw [vdenM_scalar _ _ _ _ hrs] at hr
  rw [hl, hr, Option.bind_some, Option.bind_some]
  exact conv_signed s64 rfl rfl _ hs

theorem cell_at (pre ext : List Cell) (inf x : Int) (j : Nat) (c : Cell) (h : ext[j]? = some c) (m n k : Nat)
    (hn : m = pre.length + 4 + j) :
    (pre ++ [cs inf, ci n, ci k, cs x] ++ ext)[m]? = some c := by
  have := ext_lookup (pre ++ [cs inf, ci n, ci k, cs x]) ext j c h
  rw [hn]; simpa [Nat.add_assoc] using this

def aa1 (b : BS) (k : Nat) (m0 m3 x SM SN LA LV : Int) : BS := { b with mxv := b.mxv.set k (m0 + x) }
def aa2 (b : BS) (k : Nat) (m0 m3 x SM SN LA LV : Int) : BS := { aa1 b k m0 m3 x SM SN LA LV with smx := b.smx.set k SM }
def aa3 (b : BS) (k : Nat) (m0 m3 x SM SN LA LV : Int) : BS := { aa2 b k m0 m3 x SM SN LA LV with mnv := b.mnv.set k (m3 + x) }
def aa4 (b : BS) (k : Nat) (m0 m3 x SM SN LA LV : Int) : BS := { aa3 b k m0 m3 x SM SN LA LV with smn := b.smn.set k SN }
def aa5 (b : BS) (k : Nat) (m0 m3 x SM SN LA LV : Int) : BS := { aa4 b k m0 m3 x SM SN LA LV with ladd := b.ladd.set k LA }
def aa6 (b : BS) (k : Nat) (m0 m3 x SM SN LA LV : Int) : BS := { aa5 b k m0 m3 x SM SN LA LV with lval := b.lval.set k LV }

set_option maxHeartbeats 0 in
theorem aa_exec (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (b : BS) (P : List Cell)
    (inf x : Int) (n k : Nat) (hk : k < M31) (hinf : s64.valid inf = true) (hninf : s64.valid (-inf) = true)
    (hx : s64.valid x = true) (hl0 : k < b.mxv.length) (hl1 : k < b.smx.length) (hl3 : k < b.mnv.length)
    (hl4 : k < b.smn.length) (hl7 : k < b.ladd.length) (hl8 : k < b.lval.length)
    (hv0 : ∀ w ∈ b.mxv, s64.valid w = true) (hv1 : ∀ w ∈ b.smx, s64.valid w = true) (hv3 : ∀ w ∈ b.mnv, s64.valid w = true)
    (hv4 : ∀ w ∈ b.smn, s64.valid w = true) (hv7 : ∀ w ∈ b.ladd, s64.valid w = true) (hv8 : ∀ w ∈ b.lval, s64.valid w = true)
    (hs0 : s64.valid (b.mxv.getD k 0 + x) = true) (hs3 : s64.valid (b.mnv.getD k 0 + x) = true)
    (hs1 : b.smx.getD k 0 ≠ -inf → s64.valid (b.smx.getD k 0 + x) = true)
    (hs4 : b.smn.getD k 0 ≠ inf → s64.valid (b.smn.getD k 0 + x) = true)
    (hs7 : b.lval.getD k 0 = inf → s64.valid (b.ladd.getD k 0 + x) = true)
    (hs8 : b.lval.getD k 0 ≠ inf → s64.valid (b.lval.getD k 0 + x) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (AA (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci k, cs x])) (VVB b) = some r ∧
      r.ret = none ∧ r.vv = VVB (aaB b inf x k) ∧ r.cost ≤ 3000 ∧ r.wk ≤ 6 := by
  classical
  have hm0 := getD_mem_valid b.mxv k hl0 hv0
  have hm1 := getD_mem_valid b.smx k hl1 hv1
  have hm3 := getD_mem_valid b.mnv k hl3 hv3
  have hm4 := getD_mem_valid b.smn k hl4 hv4
  have hm7 := getD_mem_valid b.ladd k hl7 hv7
  have hm8 := getD_mem_valid b.lval k hl8 hv8
  unfold aaB
  generalize hD0 : b.mxv.getD k 0 = m0 at *
  generalize hD1 : b.smx.getD k 0 = sm at *
  generalize hD3 : b.mnv.getD k 0 = m3 at *
  generalize hD4 : b.smn.getD k 0 = sn at *
  generalize hD7 : b.ladd.getD k 0 = la at *
  generalize hD8 : b.lval.getD k 0 = lv at *
  obtain ⟨SM, hSM⟩ : ∃ SM : Int, SM = (if sm ≠ -inf then sm + x else sm) := ⟨_, rfl⟩
  obtain ⟨SN, hSN⟩ : ∃ SN : Int, SN = (if sn ≠ inf then sn + x else sn) := ⟨_, rfl⟩
  obtain ⟨LV, hLV⟩ : ∃ LV : Int, LV = (if lv = inf then lv else lv + x) := ⟨_, rfl⟩
  obtain ⟨LA, hLA⟩ : ∃ LA : Int, LA = (if lv = inf then la + x else la) := ⟨_, rfl⟩
  rw [← hSM, ← hSN, ← hLV, ← hLA]
  have vSM : s64.valid SM = true := by
    rw [hSM]; by_cases h : sm ≠ -inf
    · rw [if_pos h]; exact hs1 h
    · rw [if_neg h]; exact hm1
  have vSN : s64.valid SN = true := by
    rw [hSN]; by_cases h : sn ≠ inf
    · rw [if_pos h]; exact hs4 h
    · rw [if_neg h]; exact hm4
  have vLV : s64.valid LV = true := by
    rw [hLV]; by_cases h : lv = inf
    · rw [if_pos h]; exact hm8
    · rw [if_neg h]; exact hs8 h
  have vLA : s64.valid LA = true := by
    rw [hLA]; by_cases h : lv = inf
    · rw [if_pos h]; exact hs7 h
    · rw [if_neg h]; exact hm7
  have db := fun (ext : List Cell) => dens_base mv P (pre ++ [cs inf, ci n, ci k, cs x] ++ ext) pre.length inf x k hk
    (base_lookup pre ext inf x k n).1 (base_lookup pre ext inf x k n).2.1 (base_lookup pre ext inf x k n).2.2 hinf hninf hx
  have hdn : ∀ (ext : List Cell) (vv : Nat → List Int), (bIx (mv.nv + pre.length)).denote (penvN mv.nv (gS P (pre ++ [cs inf, ci n, ci k, cs x] ++ ext))) = some (k : Int) := by
    intro ext vv
    have := (db ext vv).1
    rwa [vdenM_scalar _ _ _ _ rfl] at this
  have db0 := dens_base mv P (pre ++ [cs inf, ci n, ci k, cs x]) pre.length inf x k hk
    (by simpa using (base_lookup pre [] inf x k n).1) (by simpa using (base_lookup pre [] inf x k n).2.1)
    (by simpa using (base_lookup pre [] inf x k n).2.2) hinf hninf hx
  have hdn0 : ∀ (vv : Nat → List Int), (bIx (mv.nv + pre.length)).denote (penvN mv.nv (gS P (pre ++ [cs inf, ci n, ci k, cs x]))) = some (k : Int) := by
    intro vv
    have := (db0 vv).1
    rwa [vdenM_scalar _ _ _ _ rfl] at this
  -- S13: the end
  obtain ⟨r13, h13, hr13, hp13, hv13, hc13, hw13⟩ : ∃ r13 : PRM, pexecM mv fu Sk (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩])) (VVB (aa6 b k m0 m3 x SM SN LA LV)) = some r13 ∧
      r13.ret = none ∧ r13.ps = gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩]) ∧ r13.vv = VVB (aa6 b k m0 m3 x SM SN LA LV) ∧ r13.cost ≤ 0 ∧ r13.wk ≤ 0 :=
    ⟨_, pexecM_skip _ _ _ _, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  -- S12: lval[k] = LV
  obtain ⟨r12, h12, hr12, hp12, hv12, hc12, hn12, hw12⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩])) (VVB (aa5 b k m0 m3 x SM SN LA LV)) 8 (by omega) s64
    (hty 8 (by omega)) (bIx (mv.nv + pre.length)) (aVar (mv.nv + pre.length + 6)) LV k
    (den_cellvar mv P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩]) (pre.length + 6) _ (by omega) LV (cell_at pre [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩] inf x 2 _ rfl (pre.length + 6) n k (by omega)) vLV _)
    ((db [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩] _).1) (by rw [VVB_get8]; exact hl8) vLV Sk r13 (by rw [VVB_get8, VVB_upd8]; exact h13) hr13
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S11: ladd[k] = LA
  obtain ⟨r11, h11, hr11, hp11, hv11, hc11, hn11, hw11⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩])) (VVB (aa4 b k m0 m3 x SM SN LA LV)) 7 (by omega) s64
    (hty 7 (by omega)) (bIx (mv.nv + pre.length)) (aVar (mv.nv + pre.length + 7)) LA k
    (den_cellvar mv P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩]) (pre.length + 7) _ (by omega) LA (cell_at pre [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩] inf x 3 _ rfl (pre.length + 7) n k (by omega)) vLA _)
    ((db [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, LV⟩, ⟨s64, LA⟩] _).1) (by rw [VVB_get7]; exact hl7) vLA (AAt12 (mv.nv + pre.length)) r12 (by rw [VVB_get7, VVB_upd7]; exact h12) hr12
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S10: if (lv == inf) la += x else lv += x
  have e7 : (((pre ++ [cs inf, ci n, ci k, cs x]) ++ [(⟨s64, SM⟩ : Cell), (⟨s64, SN⟩ : Cell), (⟨s64, lv⟩ : Cell), (⟨s64, la⟩ : Cell)]).set (pre.length + 7) (⟨s64, if lv = inf then la + x else la⟩ : Cell)).set (pre.length + 6)
      (⟨s64, if lv = inf then lv else lv + x⟩ : Cell) = (pre ++ [cs inf, ci n, ci k, cs x]) ++ [(⟨s64, SM⟩ : Cell), (⟨s64, SN⟩ : Cell), (⟨s64, LV⟩ : Cell), (⟨s64, LA⟩ : Cell)] := by
    rw [hLA, hLV]
    have i7 : pre.length + 7 = (pre ++ [cs inf, ci n, ci k, cs x]).length + 3 := by simp
    have i6 : pre.length + 6 = (pre ++ [cs inf, ci n, ci k, cs x]).length + 2 := by simp
    rw [i7, set_app_idx (pre ++ [cs inf, ci n, ci k, cs x]) _ 3 _ (by simp), i6, set_app_idx (pre ++ [cs inf, ci n, ci k, cs x]) _ 2 _ (by simp)]
    simp
  obtain ⟨r10, h10, hr10, hp10, hv10, hc10, hn10, hw10⟩ := seq_sbranch_ite mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩]) (VVB (aa4 b k m0 m3 x SM SN LA LV)) (pre.length + 7) (pre.length + 6)
    (by omega) (by simp) (by simp) s64 (.binary bT .eq (aVar ((mv.nv + pre.length) + 6)) (bInf (mv.nv + pre.length))) (.binary s64 .add (aVar ((mv.nv + pre.length) + 7)) (bX (mv.nv + pre.length)))
    (.binary s64 .add (aVar ((mv.nv + pre.length) + 6)) (bX (mv.nv + pre.length))) (lv = inf) (la + x) (la + x) (lv + x) (lv + x) ⟨s64, la⟩ ⟨s64, lv⟩
    (by rw [den_cmp mv _ _ .eq _ _ lv inf (den_cellvar mv P _ (pre.length + 6) _ (by omega) lv (cell_at pre [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩] inf x 2 _ rfl (pre.length + 6) n k (by omega)) hm8 _) ((db [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩] _).2.2.1) rfl rfl]; exact Proofs.BellmanFordPExec.eq_convP _ _)
    (fun h => den_addsc mv _ _ _ _ la x (den_cellvar mv P _ (pre.length + 7) _ (by omega) la (cell_at pre [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩] inf x 3 _ rfl (pre.length + 7) n k (by omega)) hm7 _) ((db [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩] _).2.1) rfl rfl (hs7 h))
    (fun h => den_addsc mv _ _ _ _ lv x (den_cellvar mv P _ (pre.length + 6) _ (by omega) lv (cell_at pre [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩] inf x 2 _ rfl (pre.length + 6) n k (by omega)) hm8 _) ((db [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩] _).2.1) rfl rfl (hs8 h))
    (cell_at pre [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩] inf x 3 _ rfl (pre.length + 7) n k (by omega)) (cell_at pre [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩, ⟨s64, la⟩] inf x 2 _ rfl (pre.length + 6) n k (by omega))
    rfl rfl hm7 hm8 (fun h => conv_signed s64 rfl rfl _ (hs7 h)) (fun h => conv_signed s64 rfl rfl _ (hs8 h))
    (AAt11 (mv.nv + pre.length)) r11 (by rw [e7]; exact h11) hr11 200 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    (P.length + 2 * pre.length + 200) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S9: long long la = ladd[k]
  obtain ⟨r9, h9, hr9, hp9, hv9, hc9, hn9, hw9⟩ := seq_decl mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩]) (VVB (aa4 b k m0 m3 x SM SN LA LV)) s64 (aRd (mv.nv + pre.length) 7) la la
    (den_rd mv (VVB (aa4 b k m0 m3 x SM SN LA LV)) _ 7 (by omega) (hty 7 (by omega)) la (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get7]; exact hl7) (by rw [VVB_get7]; exact hD7) (by rw [VVB_get7]; exact hv7) (hdn [⟨s64, SM⟩, ⟨s64, SN⟩, ⟨s64, lv⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm7) (AAt10 (mv.nv + pre.length)) r10
    (by rw [List.append_assoc]; exact h10) hr10
  -- S8: long long lv = lval[k]
  obtain ⟨r8, h8, hr8, hp8, hv8, hc8, hn8, hw8⟩ := seq_decl mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩]) (VVB (aa4 b k m0 m3 x SM SN LA LV)) s64 (aRd (mv.nv + pre.length) 8) lv lv
    (den_rd mv (VVB (aa4 b k m0 m3 x SM SN LA LV)) _ 8 (by omega) (hty 8 (by omega)) lv (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get8]; exact hl8) (by rw [VVB_get8]; exact hD8) (by rw [VVB_get8]; exact hv8) (hdn [⟨s64, SM⟩, ⟨s64, SN⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm8) (AAt9 (mv.nv + pre.length)) r9
    (by rw [List.append_assoc]; exact h9) hr9
  -- S7: smn[k] = SN
  obtain ⟨r7, h7, hr7, hp7, hv7, hc7, hn7, hw7⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩])) (VVB (aa3 b k m0 m3 x SM SN LA LV)) 4 (by omega) s64
    (hty 4 (by omega)) (bIx (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 5)) SN k
    (den_cellvar mv P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, SN⟩]) (pre.length + 5) _ (by omega) SN (cell_at pre [⟨s64, SM⟩, ⟨s64, SN⟩] inf x 1 _ rfl (pre.length + 5) n k (by omega)) vSN _)
    ((db [⟨s64, SM⟩, ⟨s64, SN⟩] _).1) (by rw [VVB_get4]; exact hl4) vSN (AAt8 (mv.nv + pre.length)) r8 (by rw [VVB_get4, VVB_upd4]; exact h8) hr8
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S6: if (sn != inf) sn += x
  have e4 : ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [(⟨s64, SM⟩ : Cell), (⟨s64, sn⟩ : Cell)]).set (pre.length + 5) (⟨s64, if sn ≠ inf then sn + x else sn⟩ : Cell) = (pre ++ [cs inf, ci n, ci k, cs x]) ++ [(⟨s64, SM⟩ : Cell), (⟨s64, SN⟩ : Cell)] := by
    rw [hSN]
    have i5 : pre.length + 5 = (pre ++ [cs inf, ci n, ci k, cs x]).length + 1 := by simp
    rw [i5, set_app_idx (pre ++ [cs inf, ci n, ci k, cs x]) _ 1 _ (by simp)]
    simp
  obtain ⟨r6, h6, hr6, hp6, hv6, hc6, hn6, hw6⟩ := seq_sbranch2 mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩, ⟨s64, sn⟩]) (VVB (aa3 b k m0 m3 x SM SN LA LV)) (pre.length + 5) (by simp) s64
    (.binary bT .ne (aVar ((mv.nv + pre.length) + 5)) (bInf (mv.nv + pre.length))) (.binary s64 .add (aVar ((mv.nv + pre.length) + 5)) (bX (mv.nv + pre.length))) (sn ≠ inf) (sn + x) (sn + x) ⟨s64, sn⟩
    (by rw [den_cmp mv _ _ .ne _ _ sn inf (den_cellvar mv P _ (pre.length + 5) _ (by omega) sn (cell_at pre [⟨s64, SM⟩, ⟨s64, sn⟩] inf x 1 _ rfl (pre.length + 5) n k (by omega)) hm4 _) ((db [⟨s64, SM⟩, ⟨s64, sn⟩] _).2.2.1) rfl rfl]; exact ne_conv _ _)
    (fun h => den_addsc mv _ _ _ _ sn x (den_cellvar mv P _ (pre.length + 5) _ (by omega) sn (cell_at pre [⟨s64, SM⟩, ⟨s64, sn⟩] inf x 1 _ rfl (pre.length + 5) n k (by omega)) hm4 _) ((db [⟨s64, SM⟩, ⟨s64, sn⟩] _).2.1) rfl rfl (hs4 h))
    (cell_at pre [⟨s64, SM⟩, ⟨s64, sn⟩] inf x 1 _ rfl (pre.length + 5) n k (by omega)) rfl hm4 (fun h => conv_signed s64 rfl rfl _ (hs4 h))
    (AAt7 (mv.nv + pre.length)) r7 (by rw [e4]; exact h7) hr7 200 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    (P.length + 2 * pre.length + 200) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S5: long long sn = smn[k]
  obtain ⟨r5, h5, hr5, hp5, hv5, hc5, hn5, hw5⟩ := seq_decl mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩]) (VVB (aa3 b k m0 m3 x SM SN LA LV)) s64 (aRd (mv.nv + pre.length) 4) sn sn
    (den_rd mv (VVB (aa3 b k m0 m3 x SM SN LA LV)) _ 4 (by omega) (hty 4 (by omega)) sn (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get4]; exact hl4) (by rw [VVB_get4]; exact hD4) (by rw [VVB_get4]; exact hv4) (hdn [⟨s64, SM⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm4) (AAt6 (mv.nv + pre.length)) r6
    (by rw [List.append_assoc]; exact h6) hr6
  -- S4: mnv[k] = m3 + x
  obtain ⟨r4, h4, hr4, hp4, hv4, hc4, hn4, hw4⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩])) (VVB (aa2 b k m0 m3 x SM SN LA LV)) 3 (by omega) s64
    (hty 3 (by omega)) (bIx (mv.nv + pre.length)) (aRdAdd (mv.nv + pre.length) 3) (m3 + x) k
    (den_rdadd mv _ _ 3 (by omega) (hty 3 (by omega)) m3 x (bIx (mv.nv + pre.length)) (bX (mv.nv + pre.length)) rfl k (by rw [VVB_get3]; exact hl3) (by rw [VVB_get3]; exact hD3) (by rw [VVB_get3]; exact hv3) (hdn [⟨s64, SM⟩] (VVB b)) hk ((db [⟨s64, SM⟩] _).2.1) hs3 rfl)
    ((db [⟨s64, SM⟩] _).1) (by rw [VVB_get3]; exact hl3) hs3 (AAt5 (mv.nv + pre.length)) r5 (by rw [VVB_get3, VVB_upd3]; exact h5) hr5
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S3: smx[k] = SM
  obtain ⟨r3, h3, hr3, hp3, hv3, hc3, hn3, hw3⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩])) (VVB (aa1 b k m0 m3 x SM SN LA LV)) 1 (by omega) s64
    (hty 1 (by omega)) (bIx (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 4)) SM k
    (den_cellvar mv P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, SM⟩]) (pre.length + 4) _ (by omega) SM (cell_at pre [⟨s64, SM⟩] inf x 0 _ rfl (pre.length + 4) n k (by omega)) vSM _)
    ((db [⟨s64, SM⟩] _).1) (by rw [VVB_get1]; exact hl1) vSM (AAt4 (mv.nv + pre.length)) r4 (by rw [VVB_get1, VVB_upd1]; exact h4) hr4
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S2: if (sm != -inf) sm += x
  have e2 : ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [(⟨s64, sm⟩ : Cell)]).set (pre.length + 4) (⟨s64, if sm ≠ -inf then sm + x else sm⟩ : Cell) = (pre ++ [cs inf, ci n, ci k, cs x]) ++ [(⟨s64, SM⟩ : Cell)] := by
    rw [hSM]
    have i4 : pre.length + 4 = (pre ++ [cs inf, ci n, ci k, cs x]).length + 0 := by simp
    rw [i4, set_app_idx (pre ++ [cs inf, ci n, ci k, cs x]) _ 0 _ (by simp)]
    simp
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hn2, hw2⟩ := seq_sbranch2 mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, sm⟩]) (VVB (aa1 b k m0 m3 x SM SN LA LV)) (pre.length + 4) (by simp) s64
    (.binary bT .ne (aVar ((mv.nv + pre.length) + 4)) (bNInf (mv.nv + pre.length))) (.binary s64 .add (aVar ((mv.nv + pre.length) + 4)) (bX (mv.nv + pre.length))) (sm ≠ -inf) (sm + x) (sm + x) ⟨s64, sm⟩
    (by rw [den_cmp mv _ _ .ne _ _ sm (-inf) (den_cellvar mv P _ (pre.length + 4) _ (by omega) sm (cell_at pre [⟨s64, sm⟩] inf x 0 _ rfl (pre.length + 4) n k (by omega)) hm1 _) ((db [⟨s64, sm⟩] _).2.2.2) rfl rfl]; exact ne_conv _ _)
    (fun h => den_addsc mv _ _ _ _ sm x (den_cellvar mv P _ (pre.length + 4) _ (by omega) sm (cell_at pre [⟨s64, sm⟩] inf x 0 _ rfl (pre.length + 4) n k (by omega)) hm1 _) ((db [⟨s64, sm⟩] _).2.1) rfl rfl (hs1 h))
    (cell_at pre [⟨s64, sm⟩] inf x 0 _ rfl (pre.length + 4) n k (by omega)) rfl hm1 (fun h => conv_signed s64 rfl rfl _ (hs1 h))
    (AAt3 (mv.nv + pre.length)) r3 (by rw [e2]; exact h3) hr3 200 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    (P.length + 2 * pre.length + 200) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S1: long long sm = smx[k]
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hn1, hw1⟩ := seq_decl mv fu P (pre ++ [cs inf, ci n, ci k, cs x]) (VVB (aa1 b k m0 m3 x SM SN LA LV)) s64 (aRd (mv.nv + pre.length) 1) sm sm
    (den_rd mv (VVB (aa1 b k m0 m3 x SM SN LA LV)) _ 1 (by omega) (hty 1 (by omega)) sm (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get1]; exact hl1) (by rw [VVB_get1]; exact hD1) (by rw [VVB_get1]; exact hv1) (hdn0 (VVB b))) (conv_signed s64 rfl rfl _ hm1) (AAt2 (mv.nv + pre.length)) r2
    h2 hr2
  -- S0: mxv[k] = m0 + x
  obtain ⟨r0, h0, hr0, hp0, hv0', hc0, hn0, hw0⟩ := seq_write mv fu (gS P (pre ++ [cs inf, ci n, ci k, cs x])) (VVB b) 0 (by omega) s64
    (hty 0 (by omega)) (bIx (mv.nv + pre.length)) (aRdAdd (mv.nv + pre.length) 0) (m0 + x) k
    (den_rdadd mv _ _ 0 (by omega) (hty 0 (by omega)) m0 x (bIx (mv.nv + pre.length)) (bX (mv.nv + pre.length)) rfl k (by rw [VVB_get0]; exact hl0) (by rw [VVB_get0]; exact hD0) (by rw [VVB_get0]; exact hv0) (hdn0 (VVB b)) hk (db0 _).2.1 hs0 rfl)
    ((db0 _).1) (by rw [VVB_get0]; exact hl0) hs0 (AAt1 (mv.nv + pre.length)) r1 (by rw [VVB_get0, VVB_upd0]; exact h1) hr1
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  refine ⟨r0, h0, hr0, ?_, ?_, ?_⟩
  · rw [hv0', hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13]
    try rfl
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at *; omega
  · simp at *; omega

end Proofs.BeatsExec
