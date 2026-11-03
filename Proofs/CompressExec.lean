import Proofs.MatMulExec
import Proofs.SortVectorCall
import Proofs.DedupVectorCall
import Proofs.Generated.SortUtil

namespace Proofs.CompressExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.MatMulExec (vdenM_binary idx_lt n_small)
open Proofs.CppNestedVectorBindings (uniqAdj uniqAdj_length uniqAdj_mem)
open Proofs.LowerBoundIndexCall (LInv SortedL stepsL stepsL_succ stepsL_mono stepsL_log LInv_yes LInv_no)

/-- The contents of the three vectors of `compress`: the input `X`, the output `U` and the index vector `Y`. -/
def V3 (X U Y : List Int) : Nat → List Int := fun k =>
  if k = 0 then X else if k = 1 then U else if k = 2 then Y else []

theorem V3_get1 (X U Y : List Int) : V3 X U Y 1 = U := by simp [V3]
theorem V3_get0 (X U Y : List Int) : V3 X U Y 0 = X := by simp [V3]
theorem V3_get2 (X U Y : List Int) : V3 X U Y 2 = Y := by simp [V3]

theorem V3_upd1 (X U Y : List Int) (f : List Int → List Int) : upd (V3 X U Y) 1 (f U) = V3 X (f U) Y := by
  funext k
  unfold upd V3
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · simp [h0, h1]

theorem V3_upd2 (X U Y : List Int) (f : List Int → List Int) : upd (V3 X U Y) 2 (f Y) = V3 X U (f Y) := by
  funext k
  unfold upd V3
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h2 : k = 2
      · subst h2; simp
      · simp [h0, h1, h2]

theorem rdM_valI (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (k : Nat) (hk : k < mv.nv) (t : Ty)
    (hty : t = mv.ty k) (index : NExpr) (hs : index.scalarOnly = true)
    (hrc : (NExpr.read t (.local k) index).scalarOnly = false)
    (idx : Nat) (hd : index.denote env = some (idx : Int)) (x : Int) (hx : (vv k)[idx]? = some x)
    (hxv : (mv.ty k).valid x = true) :
    vdenM mv vv env (.read t (.local k) index) = some x := by
  rw [vdenM, if_neg (by rw [hrc]; decide), if_pos ⟨hk, hty, hs⟩, hd, Option.bind_some]
  unfold elemAtL
  rw [if_pos (Int.natCast_nonneg idx), Int.toNat_natCast, hx, Option.bind_some, if_pos hxv]

theorem pexecM_branch_true (mv : MV) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vv : Nat → List Int) (v : Int)
    (hv : vdenM mv vv (penvN mv.nv ps) c = some v) (hne : v ≠ 0) (r : PRM) (hr : pexecM mv fu y ps vv = some r) :
    pexecM mv fu (.branch c y n) ps vv =
      some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hv, hne, hr]

theorem pexecM_branch_false (mv : MV) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vv : Nat → List Int)
    (hv : vdenM mv vv (penvN mv.nv ps) c = some 0) (r : PRM) (hr : pexecM mv fu n ps vv = some r) :
    pexecM mv fu (.branch c y n) ps vv =
      some ⟨r.ps,r.vv,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecM]
  simp [hv, hr]

theorem idxC_den (env : Nat → Ty → Option Int) (slot t : Nat) (h : env slot i32 = some (t : Int)) (ht : t < 2147483648) :
    (NExpr.cast u64 (.variable i32 slot)).denote env = some (t : Int) := by
  rw [den_cast, den_variable, h, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-! ### The copy loop `for (i = 0; i < n; i++) unzip[i] = x[i];` -/

abbrev wr1 (nv : Nat) : NStmt :=
  .write (.local 1) s64 (.cast u64 (.variable i32 (nv + 1))) (.read s64 (.local 0) (.cast u64 (.variable i32 (nv + 1))))
abbrev B1 (nv : Nat) : Command := .sequence (.primitive (wr1 nv)) (.primitive .skip)

/-- `unzip` after the first `t` entries were overwritten by the entries of `x`. -/
def cpy (X U : List Int) : Nat → List Int
  | 0 => U
  | t + 1 => (cpy X U t).set t (X.getD t 0)

theorem cpy_length (X U : List Int) : ∀ t, (cpy X U t).length = U.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [cpy, ih]

theorem getD_setI {α : Type} (v : List α) (i : Nat) (x : α) (j : Nat) (d : α) :
    (v.set i x).getD j d = if j = i ∧ i < v.length then x else v.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < v.length
    · simp [hl]
    · simp [hl]
  · have : ¬ (j = i) := fun e => h e.symm
    simp [h, this]

theorem cpy_getD (X U : List Int) (hl : U.length = X.length) :
    ∀ t, t ≤ X.length → ∀ j, (cpy X U t).getD j 0 = if j < t then X.getD j 0 else U.getD j 0 := by
  intro t
  induction t with
  | zero => intro _ j; simp [cpy]
  | succ t ih =>
    intro ht j
    rw [cpy, getD_setI, cpy_length, ih (by omega) j]
    by_cases h : j = t
    · subst h
      rw [if_pos ⟨rfl, by omega⟩, if_pos (by omega)]
    · rw [if_neg (fun hh => h hh.1)]
      by_cases hj : j < t
      · rw [if_pos hj, if_pos (by omega)]
      · rw [if_neg hj, if_neg (by omega)]

theorem cpy_full (X U : List Int) (hl : U.length = X.length) : cpy X U X.length = X := by
  apply List.ext_getElem
  · rw [cpy_length, hl]
  · intro j h1 h2
    have := cpy_getD X U hl X.length (Nat.le_refl _) j
    rw [if_pos h2] at this
    simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem copy_body (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (X U Y : List Int)
    (hX : ∀ x ∈ X, s64.valid x = true) (P : List Cell) (n t : Nat) (ht : t < n) (hlX : X.length = n)
    (hlU : U.length = n) (hn : n < 2147483648) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (B1 mv.nv) (gS P ([ci n] ++ [ci t])) (V3 X U Y) = some r ∧ r.ret = none ∧
      r.ps = gS P ([ci n] ++ [ci t] ++ []) ∧ r.vv = V3 X (U.set t (X.getD t 0)) Y ∧
      r.cost ≤ 100 ∧ r.need ≤ P.length + 100 ∧ r.wk = 1 := by
  have E1 := gSM_env mv.nv P [ci n, ci t] 1 (ci t) rfl (validN t (by omega))
  have dI := idxC_den (penvN mv.nv (gS P [ci n, ci t])) (mv.nv + 1) t E1 (by omega)
  have xt : (V3 X U Y 0)[t]? = some (X.getD t 0) := by
    rw [V3_get0]; simp [List.getD_eq_getElem?_getD, show t < X.length by omega]
  have xv' : s64.valid (X.getD t 0) = true := by
    apply hX
    have : X.getD t 0 = X[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, show t < X.length by omega]
    rw [this]; exact List.getElem_mem _
  have xv : (mv.ty 0).valid (X.getD t 0) = true := by rw [hty0]; exact xv'
  have rd := rdM_valI mv (V3 X U Y) (penvN mv.nv (gS P [ci n, ci t])) 0 (by omega) s64 hty0.symm
    (.cast u64 (.variable i32 (mv.nv + 1))) rfl rfl t dI (X.getD t 0) xt xv
  have hp : vdenM mv (V3 X U Y) (penvN mv.nv (gS P [ci n, ci t])) (.cast u64 (.variable i32 (mv.nv + 1))) =
      some ((t : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact dI
  have w := pstmtM_write_ok mv (gS P [ci n, ci t]) (V3 X U Y) 1 (by omega) (.cast u64 (.variable i32 (mv.nv + 1)))
    (.read s64 (.local 0) (.cast u64 (.variable i32 (mv.nv + 1)))) (X.getD t 0) t rd hp
    (by rw [V3_get1]; omega) (by rw [hty1]; exact xv')
  rw [hty1] at w
  have a1 := (pexecM_prim mv fu (wr1 mv.nv) _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P [ci n, ci t]) (upd (V3 X U Y) 1 ((V3 X U Y 1).set t (X.getD t 0))))
  refine ⟨_, a2, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · show upd (V3 X U Y) 1 ((V3 X U Y 1).set t (X.getD t 0)) = _
    rw [V3_get1]
    exact V3_upd1 X U Y (fun l => l.set t (X.getD t 0))
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]

theorem copy_loop (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (X U Y : List Int)
    (hX : ∀ x ∈ X, s64.valid x = true) (P : List Cell) (n : Nat) (hlX : X.length = n)
    (hlU : U.length = n) (hn : n < 2147483647) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmt mv.nv 1 (B1 mv.nv)) (gS P [ci n]) (V3 X U Y) = some res ∧
      res.ps = gS P [ci n] ∧ res.vv = V3 X X Y ∧ res.ret = none ∧
      res.cost ≤ 120 * n + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ n := by
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runC mv P 1 n (by omega) hn (B1 mv.nv)
    (fun t vv C => C = [ci n] ∧ vv = V3 X (cpy X U t) Y) 100 100 1 0 (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨hC, hvv⟩ _
      subst hC; subst hvv
      have hb := copy_body mv hnv hty0 hty1 X (cpy X U t) Y hX P n t ht hlX (by rw [cpy_length]; exact hlU) (by omega) fu
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hb
      refine ⟨r, [], [ci n], hr, hret, hps, rfl, rfl, ⟨rfl, ?_⟩, hc, hnd, by omega⟩
      rw [hvv]; rfl)
    (V3 X U Y) [ci n] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hC, hvv⟩ := hI
  subst hC
  refine ⟨res, hr, hps, ?_, hret, ?_, hnd, ?_⟩
  · rw [hvv, ← hlX, cpy_full X U (by omega)]
  · omega
  · omega

theorem pstmt_sort1 (mv : MV) (hnv : mv.nv = 3) (hty1 : mv.ty 1 = s64) (ps : PS) (vv : Nat → List Int) :
    pstmtM mv (.sortVec (.local 1) s64) ps vv = some ⟨ps, upd vv 1 ((vv 1).mergeSort (fun x y => decide (x ≤ y))), none, 3,
      ps.mem.length + ps.bs.length + 3, Proofs.StlContracts.sortComparisons (vv 1).length + (vv 1).length⟩ := by
  rw [← hty1]
  simp [pstmtM, hnv]

theorem pstmt_dedup1 (mv : MV) (hnv : mv.nv = 3) (hty1 : mv.ty 1 = s64) (ps : PS) (vv : Nat → List Int) :
    pstmtM mv (.dedupVec (.local 1) s64) ps vv = some ⟨ps, upd vv 1 (uniqAdj (vv 1)), none, 3,
      ps.mem.length + ps.bs.length + 3, (vv 1).length + (vv 1).length⟩ := by
  rw [← hty1]
  simp [pstmtM, hnv]

theorem size_valM (mv : MV) (hnv : mv.nv = 3) (hty1 : mv.ty 1 = s64) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 1).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer s64) (.local 1))) = some ((vv 1).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer s64) (.local 1))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer s64) (.local 1)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer s64) (.local 1)) = some ((vv 1).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, hty1.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

/-! ### The binary search `lo`, `hi`, `mid` -/

abbrev loopCond (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 3)) (.variable i32 (nv + 4))
abbrev midE (nv : Nat) : NExpr := .binary i32 .add (.variable i32 (nv + 3))
  (.divrem i32 false (.binary i32 .sub (.variable i32 (nv + 4)) (.variable i32 (nv + 3))) (.literal i32 2))
abbrev declMid (nv : Nat) : NStmt := .declare i32 true (midE nv)
abbrev rdMid (nv : Nat) : NExpr := .read s64 (.local 1) (.cast u64 (.variable i32 (nv + 5)))
abbrev rdXi (nv : Nat) : NExpr := .read s64 (.local 0) (.cast u64 (.variable i32 (nv + 2)))
abbrev ltE (nv : Nat) : NExpr := .binary bT .lt (rdMid nv) (rdXi nv)
abbrev loE (nv : Nat) : NExpr := .binary i32 .add (.variable i32 (nv + 5)) (.literal i32 1)
abbrev setLo (nv : Nat) : NStmt := .assign (nv + 3) i32 (loE nv)
abbrev setHi (nv : Nat) : NStmt := .assign (nv + 4) i32 (.variable i32 (nv + 5))
abbrev yesC (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (setLo nv)) (.primitive .skip))) (.primitive .skip)
abbrev noC (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (setHi nv)) (.primitive .skip))) (.primitive .skip)
abbrev brC (nv : Nat) : Command := .branch (ltE nv) (yesC nv) (noC nv)
abbrev loopBodyC (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (declMid nv)) (.sequence (brC nv) (.primitive .skip)))) (.primitive .skip)
abbrev loopC (nv : Nat) : Command := .whileLoop (loopCond nv) (loopBodyC nv)

abbrev C5 (n m i lo hi : Nat) : List Cell := [ci n, ci m, ci i, ci lo, ci hi]
abbrev C6 (n m i lo hi mid : Nat) : List Cell := [ci n, ci m, ci i, ci lo, ci hi, ci mid]

theorem envC5 (mv : MV) (P : List Cell) (n m i lo hi : Nat) (hn : n < 2147483648) (hm : m < 2147483648)
    (hi' : i < 2147483648) (hlo : lo < 2147483648) (hhi : hi < 2147483648) :
    penvN mv.nv (gS P (C5 n m i lo hi)) (mv.nv + 2) i32 = some (i : Int) ∧
    penvN mv.nv (gS P (C5 n m i lo hi)) (mv.nv + 3) i32 = some (lo : Int) ∧
    penvN mv.nv (gS P (C5 n m i lo hi)) (mv.nv + 4) i32 = some (hi : Int) :=
  ⟨gSM_env mv.nv P _ 2 (ci i) rfl (validN i hi'), gSM_env mv.nv P _ 3 (ci lo) rfl (validN lo hlo),
   gSM_env mv.nv P _ 4 (ci hi) rfl (validN hi hhi)⟩

theorem envC6 (mv : MV) (P : List Cell) (n m i lo hi mid : Nat) (hn : n < 2147483648) (hm : m < 2147483648)
    (hi' : i < 2147483648) (hlo : lo < 2147483648) (hhi : hi < 2147483648) (hmid : mid < 2147483648) :
    penvN mv.nv (gS P (C6 n m i lo hi mid)) (mv.nv + 2) i32 = some (i : Int) ∧
    penvN mv.nv (gS P (C6 n m i lo hi mid)) (mv.nv + 3) i32 = some (lo : Int) ∧
    penvN mv.nv (gS P (C6 n m i lo hi mid)) (mv.nv + 4) i32 = some (hi : Int) ∧
    penvN mv.nv (gS P (C6 n m i lo hi mid)) (mv.nv + 5) i32 = some (mid : Int) :=
  ⟨gSM_env mv.nv P _ 2 (ci i) rfl (validN i hi'), gSM_env mv.nv P _ 3 (ci lo) rfl (validN lo hlo),
   gSM_env mv.nv P _ 4 (ci hi) rfl (validN hi hhi), gSM_env mv.nv P _ 5 (ci mid) rfl (validN mid hmid)⟩

theorem cond_valC (mv : MV) (vv : Nat → List Int) (P : List Cell) (n m i lo hi : Nat) (hn : n < 2147483648)
    (hm : m < 2147483648) (hi' : i < 2147483648) (hlo : lo < 2147483648) (hhi : hi < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (C5 n m i lo hi))) (loopCond mv.nv) = some (if lo < hi then 1 else 0) := by
  obtain ⟨E2, E3, E4⟩ := envC5 mv P n m i lo hi hn hm hi' hlo hhi
  have hs : (loopCond mv.nv).scalarOnly = true := rfl
  rw [vdenM_scalar _ _ _ _ hs, den_binary, den_variable, E3, Option.bind_some, den_variable, E4, Option.bind_some]
  have : binaryValue .lt (lo : Int) (hi : Int) = if lo < hi then 1 else 0 := by
    show (if (lo : Int) < (hi : Int) then 1 else 0) = _
    by_cases h : lo < hi
    · have : (lo : Int) < (hi : Int) := by omega
      simp [h]
    · have : ¬ ((lo : Int) < (hi : Int)) := by omega
      simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : lo < hi <;> simp [h]

set_option maxRecDepth 100000 in
theorem mid_valC (mv : MV) (vv : Nat → List Int) (P : List Cell) (n m i lo hi : Nat) (hn : n < 2147483648)
    (hm : m < 2147483648) (hi' : i < 2147483648) (hle : lo ≤ hi) (hhi : hi < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (C5 n m i lo hi))) (midE mv.nv) = some ((lo + (hi - lo) / 2 : Nat) : Int) := by
  have hlo : lo < 2147483648 := by omega
  obtain ⟨E2, E3, E4⟩ := envC5 mv P n m i lo hi hn hm hi' hlo hhi
  have hs : (midE mv.nv).scalarOnly = true := rfl
  rw [vdenM_scalar _ _ _ _ hs, den_binary, den_variable, E3, Option.bind_some, den_divrem,
    den_binary, den_variable, E4, Option.bind_some, den_variable, E3,
    Option.bind_some, den_literal, if_pos (show i32.valid 2 = true from rfl)]
  have hsub : binaryValue .sub (hi : Int) (lo : Int) = ((hi - lo : Nat) : Int) := by
    show (hi : Int) - (lo : Int) = _; omega
  have hv : i32.convert (binaryValue .sub (hi : Int) (lo : Int)) = some ((hi - lo : Nat) : Int) := by
    rw [hsub]; exact conv_signed i32 rfl rfl _ (validN _ (by omega))
  rw [hv, Option.bind_some, Option.bind_some]
  have hq : (((hi - lo : Nat) : Int)).tdiv 2 = (((hi - lo) / 2 : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  have hd : checkedDivRem i32 false ((hi - lo : Nat) : Int) 2 = some (((hi - lo) / 2 : Nat) : Int) := by
    unfold checkedDivRem
    rw [hq]
    have hvq : i32.valid (((hi - lo) / 2 : Nat) : Int) = true := validN _ (by omega)
    rw [if_neg (by decide), if_neg (by simp only [hvq, Bool.not_true]; decide)]
    exact conv_signed i32 rfl rfl _ hvq
  rw [hd, Option.bind_some]
  have hadd : binaryValue .add (lo : Int) (((hi - lo) / 2 : Nat) : Int) = ((lo + (hi - lo) / 2 : Nat) : Int) := by
    show (lo : Int) + _ = _; push_cast; rfl
  rw [hadd]
  exact conv_signed i32 rfl rfl _ (validN _ (by omega))

theorem ltE_valC (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (X Z Y : List Int)
    (P : List Cell) (n m i lo hi mid : Nat) (hn : n < 2147483648) (hm : m < 2147483648)
    (hi' : i < 2147483648) (hlo : lo < 2147483648) (hhi : hi < 2147483648) (hmid : mid < 2147483648)
    (z x : Int) (hz : Z[mid]? = some z) (hx : X[i]? = some x) (hzv : s64.valid z = true) (hxv : s64.valid x = true) :
    vdenM mv (V3 X Z Y) (penvN mv.nv (gS P (C6 n m i lo hi mid))) (ltE mv.nv) = some (if z < x then 1 else 0) := by
  obtain ⟨E2, E3, E4, E5⟩ := envC6 mv P n m i lo hi mid hn hm hi' hlo hhi hmid
  have hb : (ltE mv.nv).scalarOnly = false := rfl
  have r1 := rdM_valI mv (V3 X Z Y) (penvN mv.nv (gS P (C6 n m i lo hi mid))) 1 (by omega) s64 hty1.symm
    (.cast u64 (.variable i32 (mv.nv + 5))) rfl rfl mid (idxC_den _ _ _ E5 hmid) z (by rw [V3_get1]; exact hz)
    (by rw [hty1]; exact hzv)
  have r2 := rdM_valI mv (V3 X Z Y) (penvN mv.nv (gS P (C6 n m i lo hi mid))) 0 (by omega) s64 hty0.symm
    (.cast u64 (.variable i32 (mv.nv + 2))) rfl rfl i (idxC_den _ _ _ E2 hi') x (by rw [V3_get0]; exact hx)
    (by rw [hty0]; exact hxv)
  rw [vdenM_binary _ _ _ _ _ _ _ hb, r1, r2, Option.bind_some, Option.bind_some]
  have : binaryValue .lt z x = if z < x then 1 else 0 := rfl
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases hh : z < x <;> simp [hh]

theorem loE_valC (mv : MV) (vv : Nat → List Int) (P : List Cell) (n m i lo hi mid : Nat) (hn : n < 2147483648)
    (hm : m < 2147483648) (hi' : i < 2147483648) (hlo : lo < 2147483648) (hhi : hi < 2147483648)
    (h : mid + 1 < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (C6 n m i lo hi mid))) (loE mv.nv) = some ((mid + 1 : Nat) : Int) := by
  obtain ⟨E2, E3, E4, E5⟩ := envC6 mv P n m i lo hi mid hn hm hi' hlo hhi (by omega)
  have hs : (loE mv.nv).scalarOnly = true := rfl
  rw [vdenM_scalar _ _ _ _ hs, den_binary, den_variable, E5, Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .add (mid : Int) 1 = ((mid + 1 : Nat) : Int) := by
    show (mid : Int) + 1 = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ h)

theorem hiE_valC (mv : MV) (vv : Nat → List Int) (P : List Cell) (n m i lo hi mid : Nat) (hn : n < 2147483648)
    (hm : m < 2147483648) (hi' : i < 2147483648) (hlo : lo < 2147483648) (hhi : hi < 2147483648)
    (h : mid < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (C6 n m i lo hi mid))) (NExpr.variable i32 (mv.nv + 5)) = some (mid : Int) := by
  obtain ⟨E2, E3, E4, E5⟩ := envC6 mv P n m i lo hi mid hn hm hi' hlo hhi h
  rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E5

theorem iterYesC (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (X Z Y : List Int)
    (P : List Cell) (n m i lo hi : Nat) (hn : n < 2147483648) (hm : m < 2147483648) (hi' : i < 2147483648)
    (hlt : lo < hi) (hhi : hi < 2147483648) (x z : Int) (hx : X[i]? = some x) (hxv : s64.valid x = true)
    (hz : Z[lo + (hi - lo) / 2]? = some z) (hzv : s64.valid z = true) (hcmp : z < x) (fu : Nat) :
    ∃ r1 : PRM, pexecM mv fu (loopBodyC mv.nv) (gS P (C5 n m i lo hi)) (V3 X Z Y) = some r1 ∧
      r1.ps = gS P (C5 n m i (lo + (hi - lo) / 2 + 1) hi) ∧ r1.vv = V3 X Z Y ∧ r1.ret = none ∧ r1.cost ≤ 150 ∧
      r1.need ≤ P.length + 60 ∧ r1.wk = 0 := by
  have hmid : lo + (hi - lo) / 2 < hi := by omega
  have hv := mid_valC mv (V3 X Z Y) P n m i lo hi hn hm hi' (by omega) hhi
  have d1 := gSM_decl mv P (C5 n m i lo hi) (V3 X Z Y) i32 (midE mv.nv) _ ((lo + (hi - lo) / 2 : Nat) : Int) hv
    (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have e0 : C5 n m i lo hi ++ [(⟨i32,((lo + (hi - lo) / 2 : Nat) : Int)⟩ : Cell)] = C6 n m i lo hi (lo + (hi - lo) / 2) := rfl
  rw [e0] at d1
  have d1' := (pexecM_prim mv fu (declMid mv.nv) _ _).trans d1
  have cv := ltE_valC mv hnv hty0 hty1 X Z Y P n m i lo hi (lo + (hi - lo) / 2) hn hm hi' (by omega) hhi (by omega) z x hz hx hzv hxv
  rw [if_pos hcmp] at cv
  have lv := loE_valC mv (V3 X Z Y) P n m i lo hi (lo + (hi - lo) / 2) hn hm hi' (by omega) hhi (by omega)
  have stA := gSM_assign mv P (C6 n m i lo hi (lo + (hi - lo) / 2)) (V3 X Z Y) 3 (by simp) i32 (loE mv.nv) _ _ lv (ci lo) rfl rfl (validN lo (by omega)) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have e2 : (C6 n m i lo hi (lo + (hi - lo) / 2)).set 3 ⟨i32,((lo + (hi - lo) / 2 + 1 : Nat) : Int)⟩ =
      C6 n m i (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2) := rfl
  rw [e2] at stA
  have a1 := (pexecM_prim mv fu (setLo mv.nv) _ _).trans stA
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (C6 n m i (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2))) (V3 X Z Y))
  have a3 := pexecM_scope mv fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (gS P (C6 n m i lo hi (lo + (hi - lo) / 2)))
    (gS P (C6 n m i (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2))) (by simp [gS]) (by simp [gS])
  simp only [a4] at a3
  have a5 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (C6 n m i (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2))) (V3 X Z Y))
  have br := pexecM_branch_true mv fu (ltE mv.nv) (yesC mv.nv) (noC mv.nv) (gS P (C6 n m i lo hi (lo + (hi - lo) / 2))) (V3 X Z Y) 1 cv (by simp) _ a5
  have e1 := seqM_some br rfl (pexecM_skip mv fu _ _)
  have e2' := seqM_some d1' rfl e1
  have e3 := pexecM_scope mv fu _ _ _ _ e2'
  have tk : (⟨(gS P (C6 n m i (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2))).mem.take (gS P (C5 n m i lo hi)).mem.length,
      (gS P (C6 n m i (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2))).bs.take (gS P (C5 n m i lo hi)).bs.length⟩ : PS) =
      gS P (C5 n m i (lo + (hi - lo) / 2 + 1) hi) :=
    gS_takeC P (C5 n m i lo hi) (C5 n m i (lo + (hi - lo) / 2 + 1) hi) [ci (lo + (hi - lo) / 2)] (by simp)
  simp only [tk] at e3
  have c1 := seqM_some e3 rfl (pexecM_skip mv fu (gS P (C5 n m i (lo + (hi - lo) / 2 + 1) hi)) (V3 X Z Y))
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


theorem iterNoC (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (X Z Y : List Int)
    (P : List Cell) (n m i lo hi : Nat) (hn : n < 2147483648) (hm : m < 2147483648) (hi' : i < 2147483648)
    (hlt : lo < hi) (hhi : hi < 2147483648) (x z : Int) (hx : X[i]? = some x) (hxv : s64.valid x = true)
    (hz : Z[lo + (hi - lo) / 2]? = some z) (hzv : s64.valid z = true) (hcmp : ¬ z < x) (fu : Nat) :
    ∃ r1 : PRM, pexecM mv fu (loopBodyC mv.nv) (gS P (C5 n m i lo hi)) (V3 X Z Y) = some r1 ∧
      r1.ps = gS P (C5 n m i lo (lo + (hi - lo) / 2)) ∧ r1.vv = V3 X Z Y ∧ r1.ret = none ∧ r1.cost ≤ 150 ∧
      r1.need ≤ P.length + 60 ∧ r1.wk = 0 := by
  have hmid : lo + (hi - lo) / 2 < hi := by omega
  have hv := mid_valC mv (V3 X Z Y) P n m i lo hi hn hm hi' (by omega) hhi
  have d1 := gSM_decl mv P (C5 n m i lo hi) (V3 X Z Y) i32 (midE mv.nv) _ ((lo + (hi - lo) / 2 : Nat) : Int) hv
    (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have e0 : C5 n m i lo hi ++ [(⟨i32,((lo + (hi - lo) / 2 : Nat) : Int)⟩ : Cell)] = C6 n m i lo hi (lo + (hi - lo) / 2) := rfl
  rw [e0] at d1
  have d1' := (pexecM_prim mv fu (declMid mv.nv) _ _).trans d1
  have cv := ltE_valC mv hnv hty0 hty1 X Z Y P n m i lo hi (lo + (hi - lo) / 2) hn hm hi' (by omega) hhi (by omega) z x hz hx hzv hxv
  rw [if_neg hcmp] at cv
  have lv := hiE_valC mv (V3 X Z Y) P n m i lo hi (lo + (hi - lo) / 2) hn hm hi' (by omega) hhi (by omega)
  have stA := gSM_assign mv P (C6 n m i lo hi (lo + (hi - lo) / 2)) (V3 X Z Y) 4 (by simp) i32 (.variable i32 (mv.nv + 5)) _ _ lv (ci hi) rfl rfl (validN hi hhi) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have e2 : (C6 n m i lo hi (lo + (hi - lo) / 2)).set 4 ⟨i32,((lo + (hi - lo) / 2 : Nat) : Int)⟩ =
      C6 n m i lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2) := rfl
  rw [e2] at stA
  have a1 := (pexecM_prim mv fu (setHi mv.nv) _ _).trans stA
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (C6 n m i lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2))) (V3 X Z Y))
  have a3 := pexecM_scope mv fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (gS P (C6 n m i lo hi (lo + (hi - lo) / 2)))
    (gS P (C6 n m i lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2))) (by simp [gS]) (by simp [gS])
  simp only [a4] at a3
  have a5 := seqM_some a3 rfl (pexecM_skip mv fu (gS P (C6 n m i lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2))) (V3 X Z Y))
  have br := pexecM_branch_false mv fu (ltE mv.nv) (yesC mv.nv) (noC mv.nv) (gS P (C6 n m i lo hi (lo + (hi - lo) / 2))) (V3 X Z Y) cv _ a5
  have e1 := seqM_some br rfl (pexecM_skip mv fu _ _)
  have e2' := seqM_some d1' rfl e1
  have e3 := pexecM_scope mv fu _ _ _ _ e2'
  have tk : (⟨(gS P (C6 n m i lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2))).mem.take (gS P (C5 n m i lo hi)).mem.length,
      (gS P (C6 n m i lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2))).bs.take (gS P (C5 n m i lo hi)).bs.length⟩ : PS) =
      gS P (C5 n m i lo (lo + (hi - lo) / 2)) :=
    gS_takeC P (C5 n m i lo hi) (C5 n m i lo (lo + (hi - lo) / 2)) [ci (lo + (hi - lo) / 2)] (by simp)
  simp only [tk] at e3
  have c1 := seqM_some e3 rfl (pexecM_skip mv fu (gS P (C5 n m i lo (lo + (hi - lo) / 2))) (V3 X Z Y))
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp


theorem vwp_condC (nv : Nat) : vwp (loopCond nv) = (3, 3) := by simp [vwp, NExpr.nodes, NExpr.scalarOnly]

theorem loop_runC (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (X Z Y : List Int)
    (P : List Cell) (n m i : Nat) (hn : n < 2147483648) (hm : m < 2147483648) (hi' : i < 2147483648)
    (hZ : Z.length = m) (x : Int) (hx : X[i]? = some x) (hxv : s64.valid x = true)
    (hel : ∀ y ∈ Z, s64.valid y = true) (hs : SortedL Z) :
    ∀ (k lo hi : Nat), hi - lo = k → lo ≤ hi → hi ≤ m → LInv Z x lo hi → ∀ fu, stepsL k + 1 ≤ fu →
      ∃ (res : PRM) (r : Nat), pexecM mv fu (loopC mv.nv) (gS P (C5 n m i lo hi)) (V3 X Z Y) = some res ∧
        res.ps = gS P (C5 n m i r r) ∧ lo ≤ r ∧ r ≤ hi ∧ LInv Z x r r ∧ res.vv = V3 X Z Y ∧ res.ret = none ∧
        res.cost ≤ 157 * stepsL k + 7 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro lo hi hk hle hhi hinv fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_valC mv (V3 X Z Y) P n m i lo hi hn hm hi' (by omega) (by omega)
    by_cases hlt : lo < hi
    · rw [if_pos hlt] at hc
      have hmid : lo + (hi - lo) / 2 < hi := by omega
      obtain ⟨z, hz⟩ : ∃ y, Z[lo + (hi - lo) / 2]? = some y :=
        ⟨Z[lo + (hi - lo) / 2]'(by omega), by simp⟩
      have hzv := hel z (List.mem_of_getElem? hz)
      have hk' : stepsL k = 1 + stepsL (k / 2) := stepsL_succ k (by omega)
      by_cases hless : z < x
      · obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ :=
          iterYesC mv hnv hty0 hty1 X Z Y P n m i lo hi hn hm hi' hlt (by omega) x z hx hxv hz hzv hless (fu' + 1)
        have hinv' := LInv_yes Z x lo hi hs hinv _ z hz hless
        have hms := stepsL_mono (k / 2) (hi - (lo + (hi - lo) / 2 + 1)) (by omega)
        obtain ⟨r2, r, h2, p2, hlr, hrh, hinvr, v2, ret2, c2, n2, w2⟩ :=
          ih (hi - (lo + (hi - lo) / 2 + 1)) (by omega) (lo + (hi - lo) / 2 + 1) hi rfl (by omega) hhi hinv' fu'
            (by omega)
        rw [pexecM_while, hc]
        simp only [Bind.bind, Option.bind, h1, ret1, p1, v1, h2, vwp_condC]
        refine ⟨⟨r2.ps, r2.vv, r2.ret, 3 + 1 + r1.cost + r2.cost, max ((gS P (C5 n m i lo hi)).mem.length +
          (gS P (C5 n m i lo hi)).bs.length + 3 + 2) (max r1.need r2.need), r1.wk + r2.wk⟩, r, by simp, p2, by omega,
          hrh, hinvr, v2, ret2, ?_, ?_, ?_⟩
        · simp <;> omega
        · simp [gS_size, n1, n2] <;> omega
        · simp [w1, w2]
      · obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ :=
          iterNoC mv hnv hty0 hty1 X Z Y P n m i lo hi hn hm hi' hlt (by omega) x z hx hxv hz hzv hless (fu' + 1)
        have hinv' := LInv_no Z x lo hi hs hinv _ z hz hless
        have hms := stepsL_mono (k / 2) (lo + (hi - lo) / 2 - lo) (by omega)
        obtain ⟨r2, r, h2, p2, hlr, hrh, hinvr, v2, ret2, c2, n2, w2⟩ :=
          ih (lo + (hi - lo) / 2 - lo) (by omega) lo (lo + (hi - lo) / 2) rfl (by omega) (by omega) hinv' fu'
            (by omega)
        rw [pexecM_while, hc]
        simp only [Bind.bind, Option.bind, h1, ret1, p1, v1, h2, vwp_condC]
        refine ⟨⟨r2.ps, r2.vv, r2.ret, 3 + 1 + r1.cost + r2.cost, max ((gS P (C5 n m i lo hi)).mem.length +
          (gS P (C5 n m i lo hi)).bs.length + 3 + 2) (max r1.need r2.need), r1.wk + r2.wk⟩, r, by simp, p2, by omega,
          by omega, hinvr, v2, ret2, ?_, ?_, ?_⟩
        · simp <;> omega
        · simp [gS_size, n1, n2] <;> omega
        · simp [w1, w2]
    · rw [if_neg hlt] at hc
      have : lo = hi := by omega
      subst this
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_condC]
      refine ⟨_, lo, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, rfl, rfl, ?_, ?_, rfl⟩
      · exact hinv
      · simp
      · simp [gS_size]

abbrev declLo : NStmt := .declare i32 true (.literal i32 0)
abbrev declHi (nv : Nat) : NStmt := .declare i32 true (.variable i32 (nv + 1))
abbrev wrCmp (nv : Nat) : NStmt := .write (.local 2) i32 (.cast u64 (.variable i32 (nv + 2))) (.variable i32 (nv + 3))
abbrev B2 (nv : Nat) : Command :=
  .sequence (.primitive declLo) (.sequence (.primitive (declHi nv)) (.sequence (loopC nv)
    (.sequence (.primitive (wrCmp nv)) (.primitive .skip))))

theorem b2_exec (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = i32)
    (X Z Y : List Int) (hel : ∀ y ∈ Z, s64.valid y = true) (hs : SortedL Z) (P : List Cell) (n m i : Nat)
    (hn : n < 2147483648) (hm : m < 2147483648) (hi' : i < 2147483648) (hZ : Z.length = m) (hiY : i < Y.length)
    (x : Int) (hx : X[i]? = some x) (hxv : s64.valid x = true) (fu : Nat) (hfu : stepsL m + 1 ≤ fu) :
    ∃ (r : PRM) (q : Nat), pexecM mv fu (B2 mv.nv) (gS P ([ci n, ci m] ++ [ci i])) (V3 X Z Y) = some r ∧
      r.ret = none ∧ r.ps = gS P ([ci n, ci m] ++ [ci i] ++ [ci q, ci q]) ∧ r.vv = V3 X Z (Y.set i (q : Int)) ∧
      q ≤ m ∧ LInv Z x q q ∧ r.cost ≤ 157 * stepsL m + 100 ∧ r.need ≤ P.length + 100 ∧ r.wk = 1 := by
  have hv0 : vdenM mv (V3 X Z Y) (penvN mv.nv (gS P [ci n, ci m, ci i])) (.literal i32 0) = some 0 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
  have d1 := gSM_decl mv P [ci n, ci m, ci i] (V3 X Z Y) i32 _ 0 0 hv0 (conv_signed i32 rfl rfl _ rfl)
  have q1 := (pexecM_prim mv fu declLo _ _).trans d1
  have E1 := gSM_env mv.nv P [ci n, ci m, ci i, (⟨i32, (0 : Int)⟩ : Cell)] 1 (ci m) rfl (validN m hm)
  have hv1 : vdenM mv (V3 X Z Y) (penvN mv.nv (gS P [ci n, ci m, ci i, (⟨i32, (0 : Int)⟩ : Cell)]))
      (.variable i32 (mv.nv + 1)) = some (m : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E1
  have d2 := gSM_decl mv P [ci n, ci m, ci i, (⟨i32, (0 : Int)⟩ : Cell)] (V3 X Z Y) i32 _ (m : Int) (m : Int) hv1
    (conv_signed i32 rfl rfl _ (validN m hm))
  have q2 := (pexecM_prim mv fu (declHi mv.nv) _ _).trans d2
  have linv : LInv Z x 0 m := ⟨fun j hj => by omega, fun j hj y hy => by
    have := (List.getElem?_eq_some_iff.mp hy).1; omega⟩
  obtain ⟨res, q, hL, pL, hlq, hqh, hinvq, vL, retL, cL, nL, wL⟩ :=
    loop_runC mv hnv hty0 hty1 X Z Y P n m i hn hm hi' hZ x hx hxv hel hs (m - 0) 0 m rfl (by omega) (Nat.le_refl _)
      linv fu (by omega)
  obtain ⟨E2, E3, E4⟩ := envC5 mv P n m i q q hn hm hi' (by omega) (by omega)
  have hx3 : vdenM mv (V3 X Z Y) (penvN mv.nv (gS P (C5 n m i q q))) (.variable i32 (mv.nv + 3)) = some (q : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
  have hp : vdenM mv (V3 X Z Y) (penvN mv.nv (gS P (C5 n m i q q))) (.cast u64 (.variable i32 (mv.nv + 2))) =
      some ((i : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact idxC_den _ _ _ E2 hi'
  have w := pstmtM_write_ok mv (gS P (C5 n m i q q)) (V3 X Z Y) 2 (by omega) (.cast u64 (.variable i32 (mv.nv + 2)))
    (.variable i32 (mv.nv + 3)) (q : Int) i hx3 hp (by rw [V3_get2]; exact hiY)
    (by rw [hty2]; exact validN q (by omega))
  rw [hty2] at w
  have a1 := (pexecM_prim mv fu (wrCmp mv.nv) _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (C5 n m i q q)) (upd (V3 X Z Y) 2 ((V3 X Z Y 2).set i (q : Int))))
  have b1 := seqM_some (a := loopC mv.nv) (b := .sequence (.primitive (wrCmp mv.nv)) (.primitive .skip)) hL retL
    (by rw [pL, vL]; exact a2)
  have b2 := seqM_some q2 rfl b1
  have b3 := seqM_some q1 rfl b2
  refine ⟨_, q, b3, rfl, rfl, ?_, hqh, hinvq, ?_, ?_, ?_⟩
  · show upd (V3 X Z Y) 2 ((V3 X Z Y 2).set i (q : Int)) = _
    rw [V3_get2]
    exact V3_upd2 X Z Y (fun l => l.set i (q : Int))
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at *
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
    omega
  · simp [wL]

theorem search_loop (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = i32)
    (X Z Y : List Int) (hel : ∀ y ∈ Z, s64.valid y = true) (hs : SortedL Z) (hX : ∀ x ∈ X, s64.valid x = true)
    (P : List Cell) (n m : Nat) (hn : n < 2147483647) (hm : m < 2147483648) (hZ : Z.length = m)
    (hlX : X.length = n) (hlY : Y.length = n) (fu : Nat) (hfu : stepsL m + 1 + n + 1 ≤ fu) :
    ∃ (res : PRM) (Yf : List Int), pexecM mv fu (forStmt mv.nv 2 (B2 mv.nv)) (gS P [ci n, ci m]) (V3 X Z Y) = some res ∧
      res.ps = gS P [ci n, ci m] ∧ res.vv = V3 X Z Yf ∧ Yf.length = n ∧
      (∀ j, j < n → ∃ r : Nat, Yf[j]? = some (r : Int) ∧ r ≤ m ∧ LInv Z (X.getD j 0) r r) ∧ res.ret = none ∧
      res.cost ≤ (157 * stepsL m + 120) * n + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ n := by
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runC mv P 2 n (by omega) hn (B2 mv.nv)
    (fun t vv C => C = [ci n, ci m] ∧ ∃ Yt : List Int, vv = V3 X Z Yt ∧ Yt.length = n ∧
      ∀ j, j < t → ∃ r : Nat, Yt[j]? = some (r : Int) ∧ r ≤ m ∧ LInv Z (X.getD j 0) r r)
    (157 * stepsL m + 100) 100 1 (stepsL m + 1) (by omega)
    (by
      intro t vv C fu ht hCl hC0 ⟨hC, Yt, hvv, hlYt, hj⟩ hfu'
      subst hC; subst hvv
      have hxt : X[t]? = some (X.getD t 0) := by
        simp [List.getD_eq_getElem?_getD, show t < X.length by omega]
      have hxv : s64.valid (X.getD t 0) = true := by
        apply hX
        have : X.getD t 0 = X[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, show t < X.length by omega]
        rw [this]; exact List.getElem_mem _
      obtain ⟨r, q, hr, hret, hps, hvv, hq, hinv, hc, hnd, hwk⟩ :=
        b2_exec mv hnv hty0 hty1 hty2 X Z Yt hel hs P n m t (by omega) hm (by omega) hZ (by omega) (X.getD t 0) hxt hxv
          fu hfu'
      refine ⟨r, [ci q, ci q], [ci n, ci m], hr, hret, hps, rfl, rfl, ⟨rfl, Yt.set t (q : Int), hvv, ?_, ?_⟩, hc, hnd,
        by omega⟩
      · simp [hlYt]
      · intro j hjt
        by_cases hjt' : j = t
        · subst hjt'
          exact ⟨q, by rw [List.getElem?_set_self (by omega)], hq, hinv⟩
        · obtain ⟨r', h1, h2, h3⟩ := hj j (by omega)
          exact ⟨r', by rw [List.getElem?_set_ne (by omega)]; exact h1, h2, h3⟩)
    (V3 X Z Y) [ci n, ci m] rfl rfl ⟨rfl, Y, rfl, hlY, fun j hj => by omega⟩ fu (by omega)
  obtain ⟨hC, Yf, hvv, hlYf, hj⟩ := hI
  subst hC
  exact ⟨res, Yf, hr, hps, hvv, hlYf, hj, hret, hc, hnd, by omega⟩

abbrev declN : NStmt := .declare i32 true (.cast i32 (.size (.integer s64) (.local 0)))
abbrev sortS : NStmt := .sortVec (.local 1) s64
abbrev dedupS : NStmt := .dedupVec (.local 1) s64
abbrev declM : NStmt := .declare i32 true (.cast i32 (.size (.integer s64) (.local 1)))
abbrev bodyCmp (nv : Nat) : Command :=
  .sequence (.primitive declN) (.sequence (forStmt nv 1 (B1 nv)) (.sequence (.primitive sortS)
    (.sequence (.primitive dedupS) (.sequence (.primitive declM) (.sequence (forStmt nv 2 (B2 nv)) (.primitive .skip))))))

theorem body_eqCmp : Proofs.SortUtilInstance.compress_std_vector_long_long.body = bodyCmp 3 := rfl

/-- The vector `compress` leaves in `unzip`. -/
def zipped (X : List Int) : List Int := uniqAdj (X.mergeSort (fun a b => decide (a ≤ b)))

theorem zipped_length (X : List Int) : (zipped X).length ≤ X.length := by
  have := uniqAdj_length (X.mergeSort (fun a b => decide (a ≤ b)))
  rw [List.length_mergeSort] at this
  exact this

theorem zipped_spec (X : List Int) : (zipped X).Pairwise (fun a b => a < b) ∧ ∀ x, x ∈ zipped X ↔ x ∈ X := by
  obtain ⟨h1, h2⟩ := Proofs.SortVectorCall.sorted_result_spec X
  obtain ⟨h3, h4⟩ := Proofs.DedupVectorCall.uniqAdj_sorted_spec _ h1
  refine ⟨h3, fun x => ?_⟩
  unfold zipped
  rw [h4 x]
  exact h2.mem_iff

theorem sortedL_of_lt (Z : List Int) (h : Z.Pairwise (fun a b => a < b)) : SortedL Z := by
  intro i j hij a b ha hb
  rw [List.pairwise_iff_getElem] at h
  have hi := (List.getElem?_eq_some_iff.mp ha).1
  have hj := (List.getElem?_eq_some_iff.mp hb).1
  have ea : Z[i] = a := (List.getElem?_eq_some_iff.mp ha).2
  have eb : Z[j] = b := (List.getElem?_eq_some_iff.mp hb).2
  by_cases e : i = j
  · subst e; rw [← ea, ← eb]
  · have := h i j hi hj (by omega)
    rw [ea, eb] at this
    omega

def costCmp (n : Nat) : Nat := (157 * stepsL n + 120) * n + 120 * n + 300

theorem size_valMk (mv : MV) (k : Nat) (hk : k < mv.nv) (hty : mv.ty k = s64) (vv : Nat → List Int)
    (env : Nat → Ty → Option Int) (hn : (vv k).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer s64) (.local k))) = some ((vv k).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer s64) (.local k))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer s64) (.local k)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer s64) (.local k)) = some ((vv k).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨hk, hty.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

theorem exec_sortdedup (mv : MV) (hnv : mv.nv = 3) (hty1 : mv.ty 1 = s64) (X Y : List Int) (ps : PS) (rest : Command)
    (fu : Nat) (r : PRM) (h : pexecM mv fu rest ps (V3 X (zipped X) Y) = some r) :
    pexecM mv fu (.sequence (.primitive sortS) (.sequence (.primitive dedupS) rest)) ps (V3 X X Y) =
      some ⟨r.ps, r.vv, r.ret, 3 + (3 + r.cost),
        max (ps.mem.length + ps.bs.length + 3) (max (ps.mem.length + ps.bs.length + 3) r.need),
        (Proofs.StlContracts.sortComparisons X.length + X.length) + (X.length + X.length + r.wk)⟩ := by
  have e1 : upd (V3 X X Y) 1 (X.mergeSort (fun x y => decide (x ≤ y))) =
      V3 X (X.mergeSort (fun x y => decide (x ≤ y))) Y := V3_upd1 X X Y (fun l => l.mergeSort (fun x y => decide (x ≤ y)))
  have e2 : upd (V3 X (X.mergeSort (fun x y => decide (x ≤ y))) Y) 1 (uniqAdj (X.mergeSort (fun x y => decide (x ≤ y)))) =
      V3 X (zipped X) Y := V3_upd1 X _ Y (fun l => uniqAdj l)
  have p1 : pexecM mv fu (.primitive sortS) ps (V3 X X Y) = some ⟨ps, V3 X (X.mergeSort (fun x y => decide (x ≤ y))) Y, none, 3,
      ps.mem.length + ps.bs.length + 3, Proofs.StlContracts.sortComparisons X.length + X.length⟩ := by
    rw [pexecM_prim, pstmt_sort1 mv hnv hty1, V3_get1, e1]
  have p2 : pexecM mv fu (.primitive dedupS) ps (V3 X (X.mergeSort (fun x y => decide (x ≤ y))) Y) =
      some ⟨ps, V3 X (zipped X) Y, none, 3, ps.mem.length + ps.bs.length + 3, X.length + X.length⟩ := by
    rw [pexecM_prim, pstmt_dedup1 mv hnv hty1, V3_get1, e2, List.length_mergeSort]
  have t1 := seqM_some p2 rfl h
  have t2 := seqM_some p1 rfl t1
  exact t2

theorem body_execCmp (mv : MV) (hnv : mv.nv = 3) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = i32)
    (X U Y : List Int) (hX : ∀ x ∈ X, s64.valid x = true) (P : List Cell) (n : Nat) (hlX : X.length = n)
    (hlU : U.length = n) (hlY : Y.length = n) (hn : n < 2147483647) (fu : Nat) (hfu : stepsL n + 2 * n + 3 ≤ fu) :
    ∃ (r : PRM) (Yf : List Int), pexecM mv fu (bodyCmp mv.nv) (gS P []) (V3 X U Y) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, ci (zipped X).length] ∧ r.vv = V3 X (zipped X) Yf ∧ Yf.length = n ∧
      (∀ j, j < n → ∃ q : Nat, Yf[j]? = some (q : Int) ∧ q ≤ (zipped X).length ∧
        LInv (zipped X) (X.getD j 0) q q) ∧
      r.cost ≤ costCmp n ∧ r.need ≤ P.length + 100 ∧
      r.wk ≤ Proofs.StlContracts.sortComparisons n + 5 * n := by
  have hZs := zipped_spec X
  have hZlen : (zipped X).length ≤ n := by rw [← hlX]; exact zipped_length X
  have hZv : ∀ y ∈ zipped X, s64.valid y = true := fun y hy => hX y ((hZs.2 y).mp hy)
  have hsorted : SortedL (zipped X) := sortedL_of_lt _ hZs.1
  -- n = x.size()
  have hv0 : vdenM mv (V3 X U Y) (penvN mv.nv (gS P [])) (.cast i32 (.size (.integer s64) (.local 0))) = some (n : Int) := by
    rw [size_valMk mv 0 (by omega) hty0 _ _ (by rw [V3_get0]; omega), V3_get0, hlX]
  have d0 := gSM_decl mv P [] (V3 X U Y) i32 _ (n : Int) (n : Int) hv0 (conv_signed i32 rfl rfl _ (validN n (by omega)))
  have q0 := (pexecM_prim mv fu declN _ _).trans d0
  obtain ⟨r1, hr1, hps1, hvv1, hret1, hc1, hnd1, hw1⟩ :=
    copy_loop mv hnv hty0 hty1 X U Y hX P n hlX hlU hn fu (by omega)
  -- m = unzip.size()
  have hv2 : vdenM mv (V3 X (zipped X) Y) (penvN mv.nv (gS P [ci n])) (.cast i32 (.size (.integer s64) (.local 1))) =
      some ((zipped X).length : Int) := by
    rw [size_valMk mv 1 (by omega) hty1 _ _ (by rw [V3_get1]; omega), V3_get1]
  have d2 := gSM_decl mv P [ci n] (V3 X (zipped X) Y) i32 _ ((zipped X).length : Int) ((zipped X).length : Int) hv2
    (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have q2 := (pexecM_prim mv fu declM _ _).trans d2
  obtain ⟨rs, Yf, hrs, hpsS, hvvS, hlYf, hjf, hretS, hcS, hndS, hwS⟩ :=
    search_loop mv hnv hty0 hty1 hty2 X (zipped X) Y hZv hsorted hX P n (zipped X).length hn (by omega) rfl hlX hlY fu
      (by have := stepsL_mono n (zipped X).length hZlen; omega)
  have c1 := seqM_some hrs hretS (by rw [hpsS, hvvS]; exact pexecM_skip mv fu _ _)
  have c2 := seqM_some q2 rfl c1
  have c3 := exec_sortdedup mv hnv hty1 X Y (gS P [ci n]) _ fu _ c2
  have c4 := seqM_some hr1 hret1 (by rw [hps1, hvv1]; exact c3)
  have c5 := seqM_some q0 rfl c4
  have hmul : (157 * stepsL (zipped X).length + 120) * n ≤ (157 * stepsL n + 120) * n :=
    Nat.mul_le_mul_right n (by have := stepsL_mono n (zipped X).length hZlen; omega)
  refine ⟨_, Yf, c5, ?_, ?_, ?_, hlYf, hjf, ?_, ?_, ?_⟩
  · simp [hretS]
  · simp [hpsS]
  · simp [hvvS]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, costCmp] at *
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
    omega
  · simp [hlX] at *
    omega

/-- The index found by the search is the position of `x` in the strictly ascending list `Z` that contains it. -/
theorem lb_pos (Z : List Int) (hZ : Z.Pairwise (fun a b => a < b)) (x : Int) (hx : x ∈ Z) (q : Nat)
    (hinv : LInv Z x q q) : Z[q]? = some x := by
  obtain ⟨idx, hidx, hxe⟩ := List.getElem_of_mem hx
  have hget : Z[idx]? = some x := by simp [hidx, hxe]
  rw [List.pairwise_iff_getElem] at hZ
  by_cases h1 : idx < q
  · have := hinv.1 idx h1 x hget
    omega
  · by_cases h2 : idx = q
    · subst h2; exact hget
    · have hq : q < Z.length := by omega
      have hw : Z[q]? = some (Z[q]'hq) := by simp [hq]
      have h3 := hinv.2 q (Nat.le_refl _) _ hw
      have h4 := hZ q idx hq hidx (by omega)
      rw [hxe] at h4
      exact absurd h4 h3

end Proofs.CompressExec
