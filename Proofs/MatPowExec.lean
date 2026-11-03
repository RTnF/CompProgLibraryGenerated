import Proofs.MatPowBody
import Proofs.MatPowMath

namespace Proofs.MatPowExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.MatMulExec (M64 cu u64v u64_conv_nat vec_getM)
open Proofs.MatMulGen (upd_upd_same getq mIdxG_den)
open Proofs.MatPowBody

/-- The contents of the four vectors `a`, `r`, `y`, `t`. -/
def VP (a r y t : List Nat) : Nat → List Int := fun k =>
  if k = 0 then a.map (fun x : Nat => (x : Int)) else if k = 1 then r.map (fun x : Nat => (x : Int))
  else if k = 2 then y.map (fun x : Nat => (x : Int)) else if k = 3 then t.map (fun x : Nat => (x : Int)) else []

theorem VP_get0 (a r y t : List Nat) : VP a r y t 0 = a.map (fun x : Nat => (x : Int)) := by simp [VP]
theorem VP_get1 (a r y t : List Nat) : VP a r y t 1 = r.map (fun x : Nat => (x : Int)) := by simp [VP]
theorem VP_get2 (a r y t : List Nat) : VP a r y t 2 = y.map (fun x : Nat => (x : Int)) := by simp [VP]
theorem VP_get3 (a r y t : List Nat) : VP a r y t 3 = t.map (fun x : Nat => (x : Int)) := by simp [VP]
theorem VP_upd1 (a r y t r' : List Nat) : upd (VP a r y t) 1 (r'.map (fun x : Nat => (x : Int))) = VP a r' y t := by
  funext k; unfold upd VP; by_cases h : k = 1 <;> simp [h]
theorem VP_upd2 (a r y t y' : List Nat) : upd (VP a r y t) 2 (y'.map (fun x : Nat => (x : Int))) = VP a r y' t := by
  funext k; unfold upd VP; by_cases h : k = 2 <;> simp [h]
theorem VP_upd3 (a r y t t' : List Nat) : upd (VP a r y t) 3 (t'.map (fun x : Nat => (x : Int))) = VP a r y t' := by
  funext k; unfold upd VP; by_cases h : k = 3 <;> simp [h]

/-! ### The single-statement loops -/

/-- `d` with its first `t` entries replaced by those of `s`. -/
def copyL (d s : List Nat) : Nat → List Nat
  | 0 => d
  | t + 1 => (copyL d s t).set t (s.getD t 0)

theorem copyL_len (d s : List Nat) : ∀ t, (copyL d s t).length = d.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [copyL, ih]

theorem copyL_get (d s : List Nat) : ∀ t idx, (copyL d s t).getD idx 0 = if idx < t ∧ idx < d.length then s.getD idx 0 else d.getD idx 0 := by
  intro t
  induction t with
  | zero => intro idx; simp [copyL]
  | succ t ih =>
    intro idx
    rw [copyL, Proofs.MatMulExec.getD_setM, ih, copyL_len]
    by_cases h1 : idx = t ∧ t < d.length
    · rw [if_pos h1]
      rw [if_pos (by omega)]
      rw [h1.1]
    · rw [if_neg h1]
      by_cases h2 : idx < t ∧ idx < d.length
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem list_ext_getD (l1 l2 : List Nat) (hl : l1.length = l2.length) (h : ∀ idx, idx < l1.length → l1.getD idx 0 = l2.getD idx 0) :
    l1 = l2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i h1
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem copyL_full (d s : List Nat) (m : Nat) (hd : d.length = m) (hs : s.length = m) : copyL d s m = s := by
  apply list_ext_getD
  · rw [copyL_len]; omega
  · intro idx hidx
    rw [copyL_get, if_pos (by rw [copyL_len] at hidx; omega)]

open Proofs.BellmanFordExec (cidx_den envs pexecM_branch_true pexecM_branch_false)

theorem idx_val (mv : MV) (vv : Nat → List Int) (P C : List Cell) (p t : Nat) (hC : C.length = p) (ht : t < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (C ++ [ci t]))) (ixC mv.nv p) = some (t : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  exact cidx_den _ _ t (envs mv P (C ++ [ci t]) p (ci t) (by rw [List.getElem?_append_right (by omega)]; simp [hC]) (validN t ht)) ht

theorem copy_iter (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (dst src : Nat) (hdst : dst < mv.nv)
    (hsrc : src < mv.nv) (d s : List Nat) (hvd : vv dst = d.map (fun x : Nat => (x : Int)))
    (hvs : vv src = s.map (fun x : Nat => (x : Int))) (hsM : ∀ x ∈ s, x < M64) (P C : List Cell) (p t m : Nat)
    (hCp : C.length = p) (ht : t < m) (hm : m < 2147483647) (hld : d.length = m) (hls : s.length = m) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (.write (.local dst) u64 (ixC mv.nv p) (.read u64 (.local src) (ixC mv.nv p))))
        (.primitive .skip)) (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧ r.ps = gS P (C ++ [ci t]) ∧
      r.vv = upd vv dst ((vv dst).set t ((s.getD t 0 : Nat) : Int)) ∧ r.cost ≤ 100 ∧ r.need ≤ P.length + 2 * p + 30 ∧ r.wk ≤ 1 := by
  have hsl : t < (vv src).length := by rw [hvs]; simp [hls]; omega
  have hdl : t < (vv dst).length := by rw [hvd]; simp [hld]; omega
  have hidx := idx_val mv vv P C p t hCp (by omega)
  have hgs : s.getD t 0 < M64 := by
    have : s.getD t 0 = s[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hls, ht]
    rw [this]; exact hsM _ (List.getElem_mem _)
  have hrd : vdenM mv vv (penvN mv.nv (gS P (C ++ [ci t]))) (.read u64 (.local src) (ixC mv.nv p)) = some ((s.getD t 0 : Nat) : Int) := by
    refine Proofs.BellmanFordExec.rdM_val mv vv _ src hsrc u64 (hty src).symm (ixC mv.nv p) rfl rfl t ?_ _ ?_ ?_
    · rw [vdenM_scalar _ _ _ _ rfl] at hidx; exact hidx
    · rw [hvs]; exact vec_getM s t (by omega)
    · rw [hty]; exact u64v _ hgs
  have w := pstmtM_write_ok mv (gS P (C ++ [ci t])) vv dst hdst (ixC mv.nv p) (.read u64 (.local src) (ixC mv.nv p))
    ((s.getD t 0 : Nat) : Int) t hrd hidx hdl (by rw [hty]; exact u64v _ hgs)
  rw [hty dst] at w
  have a1 := (pexecM_prim mv fu _ _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (C ++ [ci t])) (upd vv dst ((vv dst).set t ((s.getD t 0 : Nat) : Int))))
  refine ⟨_, a2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hCp] at *
    omega
  · simp

theorem copy_loop (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (dst src : Nat) (hdst : dst < mv.nv)
    (hsrc : src < mv.nv) (hne : dst ≠ src) (d s : List Nat) (hvd : vv dst = d.map (fun x : Nat => (x : Int)))
    (hvs : vv src = s.map (fun x : Nat => (x : Int))) (hsM : ∀ x ∈ s, x < M64) (P C : List Cell) (p bnd m : Nat)
    (hb : bnd < p) (hCp : C.length = p) (hCb : C[bnd]? = some (ci m)) (hm : m < 2147483647)
    (hld : d.length = m) (hls : s.length = m) (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (copyF mv.nv p bnd dst src) (gS P C) vv = some res ∧ res.ps = gS P C ∧
      res.vv = upd vv dst (s.map (fun x : Nat => (x : Int))) ∧ res.ret = none ∧ res.cost ≤ 120 * m + 30 ∧
      res.need ≤ P.length + 2 * p + 30 ∧ res.wk ≤ m := by
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P p bnd m hb hm
    (.sequence (.primitive (.write (.local dst) u64 (ixC mv.nv p) (.read u64 (.local src) (ixC mv.nv p)))) (.primitive .skip))
    (fun t vv' C' => vv' = upd vv dst ((copyL d s t).map (fun x : Nat => (x : Int))) ∧ C' = C)
    100 (2 * p + 30) 1 0 (by omega)
    (by
      intro t vv' C' fu ht hCl hC0 ⟨hvv, hC'⟩ _
      subst hvv; subst hC'
      have hk := copy_iter mv hty (upd vv dst ((copyL d s t).map (fun x : Nat => (x : Int)))) dst src hdst hsrc (copyL d s t) s
        (by rw [upd_self]) (by rw [upd_other _ _ _ _ (Ne.symm hne)]; exact hvs) hsM P C' p t m hCl ht hm
        (by rw [copyL_len]; exact hld) hls fu
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [], C', hr, hret, ?_, hCl, hC0, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      · simpa using hps
      · rw [hvv, upd_upd_same, upd_self, ← List.map_set]
        rfl)
    vv C hCp hCb ⟨by rw [copyL]; funext k; unfold upd; split <;> simp_all, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC'⟩ := hI
  subst hC'
  refine ⟨res, hr, hps, ?_, hret, by omega, hnd, by omega⟩
  rw [hvv, copyL_full d s m hld hls]

def zeroL (d : List Nat) : Nat → List Nat
  | 0 => d
  | t + 1 => (zeroL d t).set t 0

theorem zeroL_len (d : List Nat) : ∀ t, (zeroL d t).length = d.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [zeroL, ih]

theorem zeroL_get (d : List Nat) : ∀ t idx, (zeroL d t).getD idx 0 = if idx < t ∧ idx < d.length then 0 else d.getD idx 0 := by
  intro t
  induction t with
  | zero => intro idx; simp [zeroL]
  | succ t ih =>
    intro idx
    rw [zeroL, Proofs.MatMulExec.getD_setM, ih, zeroL_len]
    by_cases h1 : idx = t ∧ t < d.length
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : idx < t ∧ idx < d.length
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem one_u64 (mv : MV) (vv : Nat → List Int) (ps : PS) :
    vdenM mv vv (penvN mv.nv ps) (.cast u64 (.literal i32 1)) = some 1 := by
  rw [vdenM_scalar _ _ _ _ rfl, den_cast, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  rfl

theorem zero_iter (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (dst : Nat) (hdst : dst < mv.nv) (d : List Nat)
    (hvd : vv dst = d.map (fun x : Nat => (x : Int))) (P C : List Cell) (p t m : Nat)
    (hCp : C.length = p) (ht : t < m) (hm : m < 2147483647) (hld : d.length = m) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (.write (.local dst) u64 (ixC mv.nv p) (.cast u64 (.literal i32 0))))
        (.primitive .skip)) (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧ r.ps = gS P (C ++ [ci t]) ∧
      r.vv = upd vv dst ((vv dst).set t ((0 : Nat) : Int)) ∧ r.cost ≤ 100 ∧ r.need ≤ P.length + 2 * p + 30 ∧ r.wk ≤ 1 := by
  have hdl : t < (vv dst).length := by rw [hvd]; simp [hld]; omega
  have hidx := idx_val mv vv P C p t hCp (by omega)
  have w := pstmtM_write_ok mv (gS P (C ++ [ci t])) vv dst hdst (ixC mv.nv p) (.cast u64 (.literal i32 0))
    ((0 : Nat) : Int) t (Proofs.MatMulExec.zero_u64 mv vv _) hidx hdl (by rw [hty]; exact u64v _ (by decide))
  rw [hty dst] at w
  have a1 := (pexecM_prim mv fu _ _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (C ++ [ci t])) (upd vv dst ((vv dst).set t ((0 : Nat) : Int))))
  refine ⟨_, a2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hCp] at *
    omega
  · simp

theorem zero_loop (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (dst : Nat) (hdst : dst < mv.nv)
    (d : List Nat) (hvd : vv dst = d.map (fun x : Nat => (x : Int))) (P C : List Cell) (p bnd m : Nat)
    (hb : bnd < p) (hCp : C.length = p) (hCb : C[bnd]? = some (ci m)) (hm : m < 2147483647)
    (hld : d.length = m) (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (zeroF mv.nv p bnd dst) (gS P C) vv = some res ∧ res.ps = gS P C ∧
      res.vv = upd vv dst ((zeroL d m).map (fun x : Nat => (x : Int))) ∧ res.ret = none ∧ res.cost ≤ 120 * m + 30 ∧
      res.need ≤ P.length + 2 * p + 30 ∧ res.wk ≤ m := by
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P p bnd m hb hm
    (.sequence (.primitive (.write (.local dst) u64 (ixC mv.nv p) (.cast u64 (.literal i32 0)))) (.primitive .skip))
    (fun t vv' C' => vv' = upd vv dst ((zeroL d t).map (fun x : Nat => (x : Int))) ∧ C' = C)
    100 (2 * p + 30) 1 0 (by omega)
    (by
      intro t vv' C' fu ht hCl hC0 ⟨hvv, hC'⟩ _
      subst hvv; subst hC'
      have hk := zero_iter mv hty (upd vv dst ((zeroL d t).map (fun x : Nat => (x : Int)))) dst hdst (zeroL d t)
        (by rw [upd_self]) P C' p t m hCl ht hm (by rw [zeroL_len]; exact hld) fu
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [], C', hr, hret, ?_, hCl, hC0, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      · simpa using hps
      · rw [hvv, upd_upd_same, upd_self, ← List.map_set]
        rfl)
    vv C hCp hCb ⟨by rw [zeroL]; funext k; unfold upd; split <;> simp_all, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC'⟩ := hI
  subst hC'
  exact ⟨res, hr, hps, hvv, hret, by omega, hnd, by omega⟩

def diagL (d : List Nat) (n : Nat) : Nat → List Nat
  | 0 => d
  | t + 1 => (diagL d n t).set (t * n + t) 1

theorem diagL_len (d : List Nat) (n : Nat) : ∀ t, (diagL d n t).length = d.length := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [diagL, ih]

theorem diagL_get (d : List Nat) (n : Nat) : ∀ t idx, (diagL d n t).getD idx 0 =
    if (∃ u, u < t ∧ idx = u * n + u) ∧ idx < d.length then 1 else d.getD idx 0 := by
  intro t
  induction t with
  | zero => intro idx; simp [diagL]
  | succ t ih =>
    intro idx
    rw [diagL, Proofs.MatMulExec.getD_setM, ih, diagL_len]
    by_cases h1 : idx = t * n + t ∧ t * n + t < d.length
    · rw [if_pos h1, if_pos ⟨⟨t, by omega, h1.1⟩, by omega⟩]
    · rw [if_neg h1]
      by_cases h2 : (∃ u, u < t ∧ idx = u * n + u) ∧ idx < d.length
      · rw [if_pos h2, if_pos]
        obtain ⟨⟨u, hu, hu2⟩, hl⟩ := h2
        exact ⟨⟨u, by omega, hu2⟩, hl⟩
      · rw [if_neg h2, if_neg]
        rintro ⟨⟨u, hu, hu2⟩, hl⟩
        by_cases hut : u = t
        · subst hut; exact h1 ⟨hu2, by omega⟩
        · exact h2 ⟨⟨u, by omega, hu2⟩, hl⟩

theorem diag_iter (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (dst : Nat) (hdst : dst < mv.nv) (d : List Nat)
    (hvd : vv dst = d.map (fun x : Nat => (x : Int))) (P C : List Cell) (p bnd n t : Nat)
    (hCp : C.length = p) (hb : bnd < p) (hCb : C[bnd]? = some (ci n)) (ht : t < n) (hnn : n * n < 2147483648)
    (hld : d.length = n * n) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (.write (.local dst) u64
        (.cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 (mv.nv + p)) (.variable i32 (mv.nv + bnd))) (.variable i32 (mv.nv + p))))
        (.cast u64 (.literal i32 1)))) (.primitive .skip)) (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C ++ [ci t]) ∧ r.vv = upd vv dst ((vv dst).set (t * n + t) ((1 : Nat) : Int)) ∧ r.cost ≤ 100 ∧
      r.need ≤ P.length + 2 * p + 30 ∧ r.wk ≤ 1 := by
  have hn32 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hlt : t * n + t < n * n := Proofs.MatMulExec.idx_lt n t t ht ht
  have hdl : t * n + t < (vv dst).length := by rw [hvd]; simp [hld]; exact hlt
  have E1 : penvN mv.nv (gS P (C ++ [ci t])) (mv.nv + p) i32 = some (t : Int) :=
    envs mv P (C ++ [ci t]) p (ci t) (by rw [List.getElem?_append_right (by omega)]; simp [hCp]) (validN t (by omega))
  have E0 : penvN mv.nv (gS P (C ++ [ci t])) (mv.nv + bnd) i32 = some (n : Int) :=
    envs mv P (C ++ [ci t]) bnd (ci n) (by rw [List.getElem?_append_left (by omega)]; exact hCb) (validN n hn32)
  have hidx : vdenM mv vv (penvN mv.nv (gS P (C ++ [ci t])))
      (.cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 (mv.nv + p)) (.variable i32 (mv.nv + bnd))) (.variable i32 (mv.nv + p)))) =
      some ((t * n + t : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact mIdxG_den _ mv.nv bnd p p t t n E0 E1 E1 (by omega)
  have w := pstmtM_write_ok mv (gS P (C ++ [ci t])) vv dst hdst _ (.cast u64 (.literal i32 1))
    ((1 : Nat) : Int) (t * n + t) (one_u64 mv vv _) hidx hdl (by rw [hty]; exact u64v _ (by decide))
  rw [hty dst] at w
  have a1 := (pexecM_prim mv fu _ _ _).trans w
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu (gS P (C ++ [ci t])) (upd vv dst ((vv dst).set (t * n + t) ((1 : Nat) : Int))))
  refine ⟨_, a2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hCp] at *
    omega
  · simp

theorem diag_loop (mv : MV) (hty : ∀ k, mv.ty k = u64) (vv : Nat → List Int) (dst : Nat) (hdst : dst < mv.nv)
    (d : List Nat) (hvd : vv dst = d.map (fun x : Nat => (x : Int))) (P C : List Cell) (p bnd n : Nat)
    (hb : bnd < p) (hCp : C.length = p) (hCb : C[bnd]? = some (ci n)) (hnn : n * n < 2147483648)
    (hld : d.length = n * n) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (diagF mv.nv p bnd dst) (gS P C) vv = some res ∧ res.ps = gS P C ∧
      res.vv = upd vv dst ((diagL d n n).map (fun x : Nat => (x : Int))) ∧ res.ret = none ∧ res.cost ≤ 120 * n + 30 ∧
      res.need ≤ P.length + 2 * p + 30 ∧ res.wk ≤ n := by
  have hn32 : n < 2147483647 := Proofs.MatMulExec.n_small n hnn
  obtain ⟨res, C2, hr, hps, hC2, hI, hret, hc, hnd, hw⟩ := for_stmt_runB mv P p bnd n hb hn32
    (.sequence (.primitive (.write (.local dst) u64
      (.cast u64 (.binary i32 .add (.binary i32 .mul (.variable i32 (mv.nv + p)) (.variable i32 (mv.nv + bnd))) (.variable i32 (mv.nv + p))))
      (.cast u64 (.literal i32 1)))) (.primitive .skip))
    (fun t vv' C' => vv' = upd vv dst ((diagL d n t).map (fun x : Nat => (x : Int))) ∧ C' = C)
    100 (2 * p + 30) 1 0 (by omega)
    (by
      intro t vv' C' fu ht hCl hC0 ⟨hvv, hC'⟩ _
      subst hvv; subst hC'
      have hk := diag_iter mv hty (upd vv dst ((diagL d n t).map (fun x : Nat => (x : Int)))) dst hdst (diagL d n t)
        (by rw [upd_self]) P C' p bnd n t hCl hb hC0 ht hnn (by rw [diagL_len]; exact hld) fu
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := hk
      refine ⟨r, [], C', hr, hret, ?_, hCl, hC0, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      · simpa using hps
      · rw [hvv, upd_upd_same, upd_self, ← List.map_set]
        rfl)
    vv C hCp hCb ⟨by rw [diagL]; funext k; unfold upd; split <;> simp_all, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC'⟩ := hI
  subst hC'
  exact ⟨res, hr, hps, hvv, hret, by omega, hnd, by omega⟩

/-- After the three setup loops, `r` holds the identity matrix. -/
theorem init_identity (r0 : List Nat) (n : Nat) (hl : r0.length = n * n) :
    (diagL (zeroL r0 (n * n)) n n).length = n * n ∧
    ∀ i j, i < n → j < n → (diagL (zeroL r0 (n * n)) n n).getD (i * n + j) 0 = Proofs.MatPowMath.Idm i j := by
  refine ⟨by rw [diagL_len, zeroL_len, hl], ?_⟩
  intro i j hi hj
  have hij : i * n + j < n * n := Proofs.MatMulExec.idx_lt n i j hi hj
  rw [diagL_get, zeroL_len, hl, zeroL_get, hl]
  unfold Proofs.MatPowMath.Idm
  by_cases h : i = j
  · subst h
    rw [if_pos (show i = i from rfl), if_pos ⟨⟨i, hi, rfl⟩, hij⟩]
  · rw [if_neg h, if_neg]
    · rw [if_pos ⟨hij, hij⟩]
    · rintro ⟨⟨u, hu, hu2⟩, _⟩
      -- i * n + j = u * n + u with j, u < n forces i = u = j
      have h1 : (i * n + j) / n = (u * n + u) / n := by rw [hu2]
      have h2 : (i * n + j) % n = (u * n + u) % n := by rw [hu2]
      have d1 : (i * n + j) / n = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj]; omega
      have d2 : (u * n + u) / n = u := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu]; omega
      have m1 : (i * n + j) % n = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      have m2 : (u * n + u) % n = u := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
      omega

/-! ### Scalars and the product lists -/

abbrev twoU : NExpr := .cast u64 (.literal i32 2)
abbrev zeroU : NExpr := .cast u64 (.literal i32 0)
abbrev oneU : NExpr := .cast u64 (.literal i32 1)

theorem twoU_den (env : Nat → Ty → Option Int) : twoU.denote env = some 2 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, convert_u64]
  rfl

theorem zeroU_den (env : Nat → Ty → Option Int) : zeroU.denote env = some 0 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some, convert_u64]
  rfl

theorem oneU_den (env : Nat → Ty → Option Int) : oneU.denote env = some 1 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some, convert_u64]
  rfl

abbrev CE (n e m : Nat) : List Cell := [ci n, cu e, ci m]

theorem e_env (mv : MV) (P : List Cell) (n e m : Nat) (he : e < M64) :
    penvN mv.nv (gS P (CE n e m)) (mv.nv + 1) u64 = some (e : Int) :=
  envs mv P (CE n e m) 1 (cu e) rfl (u64v e he)

theorem ne_val (mv : MV) (vv : Nat → List Int) (P : List Cell) (n e m : Nat) (he : e < M64) :
    vdenM mv vv (penvN mv.nv (gS P (CE n e m))) (.binary bT .ne (.variable u64 (mv.nv + 1)) zeroU) =
      some (if e ≠ 0 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e_env mv P n e m he, Option.bind_some, zeroU_den, Option.bind_some]
  by_cases h : e = 0
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : (e : Int) ≠ 0 := by omega
    simp [binaryValue, Ty.convert, bT, Ty.valid, h, this]

theorem odd_val (mv : MV) (vv : Nat → List Int) (P : List Cell) (n e m : Nat) (he : e < M64) :
    vdenM mv vv (penvN mv.nv (gS P (CE n e m))) (oddCond mv.nv) = some (if e % 2 = 1 then 1 else 0) := by
  have hr : checkedDivRem u64 true (e : Int) 2 = some ((e % 2 : Nat) : Int) := Proofs.PowModStep.rem_value e 2 (by omega) he
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_divrem, den_variable, e_env mv P n e m he, Option.bind_some, twoU_den,
    Option.bind_some, hr, Option.bind_some, oneU_den, Option.bind_some]
  by_cases h : e % 2 = 1
  · simp [binaryValue, Ty.convert, bT, Ty.valid, h]
  · have : ((e % 2 : Nat) : Int) ≠ 1 := by omega
    simp [binaryValue, Ty.convert, bT, Ty.valid, h, this]
    omega

theorem halve_val (mv : MV) (vv : Nat → List Int) (P : List Cell) (cl : List Cell) (n e m : Nat) (he : e < M64)
    (hcl : cl = CE n e m ++ [ci n]) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.divrem u64 false (.variable u64 (mv.nv + 1)) twoU) = some ((e / 2 : Nat) : Int) := by
  have hd : checkedDivRem u64 false (e : Int) 2 = some ((e / 2 : Nat) : Int) := div_value e 2 (by omega) he
  have E : penvN mv.nv (gS P cl) (mv.nv + 1) u64 = some (e : Int) :=
    envs mv P cl 1 (cu e) (by rw [hcl]; rfl) (u64v e he)
  rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, E, Option.bind_some, twoU_den, Option.bind_some, hd]

theorem dsum_eq_Sum (a b : List Nat) (n i j : Nat) : ∀ m, Proofs.MatMulExec.dsum a b n i j m =
    Proofs.MatPowMath.Sum m (fun t => a.getD (i * n + t) 0 * b.getD (t * n + j) 0) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [Proofs.MatMulExec.dsum, Proofs.MatPowMath.Sum_succ, ih]; rfl

/-- The flat list as a matrix function. -/
def toF (n : Nat) (l : List Nat) : Nat → Nat → Nat := fun i j => l.getD (i * n + j) 0

theorem matC_toF (a b c : List Nat) (n : Nat) (hlc : c.length = n * n) :
    (Proofs.MatMulExec.matC a b n c n).length = n * n ∧
    Proofs.MatPowMath.EqOn n (toF n (Proofs.MatMulExec.matC a b n c n)) (Proofs.MatPowMath.mulF n (toF n a) (toF n b)) := by
  obtain ⟨hl, hg⟩ := Proofs.MatMulExec.matC_spec a b n c hlc
  refine ⟨hl, ?_⟩
  intro i j hi hj
  have hij : i * n + j < n * n := Proofs.MatMulExec.idx_lt n i j hi hj
  unfold toF
  rw [hg _ hij]
  unfold Proofs.MatMulExec.Fm Proofs.MatPowMath.mulF
  have d1 : (i * n + j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj]; omega
  have m1 : (i * n + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [d1, m1, dsum_eq_Sum]

theorem matC_lt (a b c : List Nat) (n : Nat) (hlc : c.length = n * n) : ∀ x ∈ Proofs.MatMulExec.matC a b n c n, x < M64 := by
  intro x hx
  obtain ⟨hl, hg⟩ := Proofs.MatMulExec.matC_spec a b n c hlc
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hx
  have hidx' : idx < n * n := by omega
  have : (Proofs.MatMulExec.matC a b n c n).getD idx 0 = (Proofs.MatMulExec.matC a b n c n)[idx] := by
    simp [List.getD_eq_getElem?_getD, hidx]
  rw [← this, hg _ hidx']
  exact Nat.mod_lt _ (by decide)

/-! ### The two halves of an iteration -/

open Proofs.MatMulGen (i_loopG cIG BiG)
open Proofs.MatMulExec (matC matC_length)

theorem n_decl (mv : MV) (vv : Nat → List Int) (P : List Cell) (n e m : Nat) (hn : n < 2147483648) :
    pstmtM mv (.declare i32 true (.variable i32 (mv.nv + 0))) (gS P (CE n e m)) vv =
      some ⟨gS P (CE n e m ++ [ci n]), vv, none, (vwp (.variable i32 (mv.nv + 0))).1 + 1,
        P.length + 2 * (CE n e m).length + (vwp (.variable i32 (mv.nv + 0))).2 + 4, 0⟩ := by
  have hv : vdenM mv vv (penvN mv.nv (gS P (CE n e m))) (.variable i32 (mv.nv + 0)) = some (n : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]
    exact envs mv P (CE n e m) 0 (ci n) rfl (validN n hn)
  exact gSM_decl mv P (CE n e m) vv i32 _ (n : Int) (n : Int) hv (conv_signed i32 rfl rfl _ (validN n hn))

set_option maxHeartbeats 16000000 in
/-- The `then` part: `r = r * y` through the scratch `t`. -/
theorem then_part (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = u64) (P : List Cell) (fu : Nat) (a r y t : List Nat)
    (n e m : Nat) (hm : m = n * n) (hnn : n * n < 2147483647) (hla : a.length = n * n) (hlr : r.length = n * n)
    (hly : y.length = n * n) (hlt : t.length = n * n) (hrM : ∀ x ∈ r, x < M64) (hyM : ∀ x ∈ y, x < M64)
    (hfu : 3 * n + 4 ≤ fu) (hfu2 : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (mulCopy mv.nv 1 2 3 1 Sk) (gS P (CE n e m)) (VP a r y t) = some res ∧ res.ret = none ∧
      res.ps = gS P (CE n e m ++ [ci n]) ∧ res.vv = VP a (matC r y n t n) y (matC r y n t n) ∧
      res.cost ≤ cIG n + 120 * m + 200 ∧ res.need ≤ P.length + 2 * 4 + 100 ∧ res.wk ≤ n * n + m := by
  have hn32 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hm' : m < 2147483647 := by omega
  have d := n_decl mv (VP a r y t) P n e m hn32
  have a1 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 0))) _ _).trans d
  obtain ⟨⟨mps, mvv, mret, mcost, mneed, mwk⟩, hmr, hmps, hmvv, hmret, hmc, hmnd, hmw⟩ :=
    i_loopG mv hty (VP a r y t) 1 2 3 (by omega) (by omega) (by omega) (by decide) (by decide) r y t
      (VP_get1 _ _ _ _) (VP_get2 _ _ _ _) (VP_get3 _ _ _ _) hrM hyM P (CE n e m) 3 rfl n (by omega) hlr hly hlt fu hfu
  simp only at hmps hmvv hmret hmc hmnd hmw
  subst hmps hmvv hmret
  rw [VP_upd3] at hmr
  obtain ⟨⟨cps, cvv, cret, ccost, cneed, cwk⟩, hcr, hcps, hcvv, hcret, hcc, hcnd, hcw⟩ :=
    copy_loop mv hty (VP a r (y) (matC r y n t n)) 1 3 (by omega) (by omega) (by decide) r (matC r y n t n)
      (VP_get1 _ _ _ _) (VP_get3 _ _ _ _) (matC_lt r y t n hlt) P (CE n e m ++ [ci n]) 4 2 m (by omega) (by simp)
      (by simp) hm' (by omega) (by rw [matC_length]; omega) fu hfu2
  simp only at hcps hcvv hcret hcc hcnd hcw
  subst hcps hcvv hcret
  rw [VP_upd1] at hcr
  have b1 := seqM_some hcr rfl (pexecM_skip mv fu _ _)
  have b2 := seqM_some hmr rfl b1
  have b3 := seqM_some a1 rfl b2
  refine ⟨_, b3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hmc hcc ⊢
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, gS_mem_len, gS_bs_len] at hmnd hcnd ⊢
    omega
  · simp at hmw hcw ⊢
    omega

abbrev restCmd (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 (nv + 0))))
    (.sequence (forStmtB nv 4 3 (BiG nv 3 2 2 3)) (.sequence (copyF nv 4 2 2 3) (.sequence (.primitive (halveE nv)) Sk)))

set_option maxHeartbeats 16000000 in
/-- The part executed in every iteration: `y = y * y` through `t`, then `e /= 2`. -/
theorem rest_part (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = u64) (P : List Cell) (fu : Nat) (a r y t : List Nat)
    (n e m : Nat) (hm : m = n * n) (hnn : n * n < 2147483647) (he : e < M64) (hla : a.length = n * n)
    (hlr : r.length = n * n) (hly : y.length = n * n) (hlt : t.length = n * n) (hyM : ∀ x ∈ y, x < M64)
    (hfu : 3 * n + 4 ≤ fu) (hfu2 : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (restCmd mv.nv) (gS P (CE n e m)) (VP a r y t) = some res ∧ res.ret = none ∧
      res.ps = gS P (CE n (e / 2) m ++ [ci n]) ∧ res.vv = VP a r (matC y y n t n) (matC y y n t n) ∧
      res.cost ≤ cIG n + 120 * m + 300 ∧ res.need ≤ P.length + 2 * 4 + 100 ∧ res.wk ≤ n * n + m := by
  have hn32 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have hm' : m < 2147483647 := by omega
  have d := n_decl mv (VP a r y t) P n e m hn32
  have a1 := (pexecM_prim mv fu (.declare i32 true (.variable i32 (mv.nv + 0))) _ _).trans d
  obtain ⟨⟨mps, mvv, mret, mcost, mneed, mwk⟩, hmr, hmps, hmvv, hmret, hmc, hmnd, hmw⟩ :=
    i_loopG mv hty (VP a r y t) 2 2 3 (by omega) (by omega) (by omega) (by decide) (by decide) y y t
      (VP_get2 _ _ _ _) (VP_get2 _ _ _ _) (VP_get3 _ _ _ _) hyM hyM P (CE n e m) 3 rfl n (by omega) hly hly hlt fu hfu
  simp only at hmps hmvv hmret hmc hmnd hmw
  subst hmps hmvv hmret
  rw [VP_upd3] at hmr
  obtain ⟨⟨cps, cvv, cret, ccost, cneed, cwk⟩, hcr, hcps, hcvv, hcret, hcc, hcnd, hcw⟩ :=
    copy_loop mv hty (VP a r y (matC y y n t n)) 2 3 (by omega) (by omega) (by decide) y (matC y y n t n)
      (VP_get2 _ _ _ _) (VP_get3 _ _ _ _) (matC_lt y y t n hlt) P (CE n e m ++ [ci n]) 4 2 m (by omega) (by simp)
      (by simp) hm' (by omega) (by rw [matC_length]; omega) fu hfu2
  simp only at hcps hcvv hcret hcc hcnd hcw
  subst hcps hcvv hcret
  rw [VP_upd2] at hcr
  have hq : e / 2 < M64 := by omega
  have hq' : u64.valid ((e / 2 : Nat) : Int) = true := u64v _ hq
  have hv := halve_val mv (VP a r (matC y y n t n) (matC y y n t n)) P (CE n e m ++ [ci n]) n e m he rfl
  have s3 := gSM_assign mv P (CE n e m ++ [ci n]) (VP a r (matC y y n t n) (matC y y n t n)) 1 (by simp) u64 _ _ _ hv (cu e)
    (by simp) rfl (u64v e he) (Ty.convert_of_valid _ _ hq')
  have a3 := (pexecM_prim mv fu (halveE mv.nv) _ _).trans s3
  have b3 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
  have b2 := seqM_some hcr rfl b3
  have b1 := seqM_some hmr rfl b2
  have b0 := seqM_some a1 rfl b1
  refine ⟨_, b0, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hmc hcc ⊢
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, gS_mem_len, gS_bs_len] at hmnd hcnd ⊢
    omega
  · simp at hmw hcw ⊢
    omega

def rOf (r y t : List Nat) (n e : Nat) : List Nat := if e % 2 = 1 then matC r y n t n else r
def tOf (r y t : List Nat) (n e : Nat) : List Nat := if e % 2 = 1 then matC r y n t n else t
def yOf (r y t : List Nat) (n e : Nat) : List Nat := matC y y n (tOf r y t n e) n

set_option maxHeartbeats 64000000 in
/-- One iteration of the `while (e != 0)` loop. -/
theorem loop_body (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = u64) (P : List Cell) (fu : Nat) (a r y t : List Nat)
    (n e m : Nat) (hm : m = n * n) (hnn : n * n < 2147483647) (he : e < M64) (hne : e ≠ 0) (hla : a.length = n * n)
    (hlr : r.length = n * n) (hly : y.length = n * n) (hlt : t.length = n * n) (hrM : ∀ x ∈ r, x < M64)
    (hyM : ∀ x ∈ y, x < M64) (hfu : 3 * n + 4 ≤ fu) (hfu2 : m + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (powLoopBody mv.nv) (gS P (CE n e m)) (VP a r y t) = some res ∧ res.ret = none ∧
      res.ps = gS P (CE n (e / 2) m) ∧
      res.vv = VP a (rOf r y t n e) (yOf r y t n e) (yOf r y t n e) ∧
      res.cost ≤ 2 * (cIG n + 120 * m + 300) + 400 ∧ res.need ≤ P.length + 2 * 4 + 200 ∧ res.wk ≤ 2 * (n * n + m) := by
  have hc := odd_val mv (VP a r y t) P n e m he
  have tk : (⟨(gS P (CE n e m ++ [ci n])).mem.take (gS P (CE n e m)).mem.length,
      (gS P (CE n e m ++ [ci n])).bs.take (gS P (CE n e m)).bs.length⟩ : PS) = gS P (CE n e m) :=
    gS_takeC P (CE n e m) (CE n e m) [ci n] rfl
  have tk2 : (⟨(gS P (CE n (e / 2) m ++ [ci n])).mem.take (gS P (CE n e m)).mem.length,
      (gS P (CE n (e / 2) m ++ [ci n])).bs.take (gS P (CE n e m)).bs.length⟩ : PS) = gS P (CE n (e / 2) m) :=
    gS_takeC P (CE n e m) (CE n (e / 2) m) [ci n] rfl
  by_cases hodd : e % 2 = 1
  · rw [if_pos hodd] at hc
    obtain ⟨⟨tps, tvv, tret, tcost, tneed, twk⟩, htr, htret, htps, htvv, htc, htnd, htw⟩ :=
      then_part mv hnv hty P fu a r y t n e m hm hnn hla hlr hly hlt hrM hyM hfu hfu2
    have hMl : (matC r y n t n).length = n * n := by rw [matC_length]; exact hlt
    have hM : ∀ x ∈ matC r y n t n, x < M64 := matC_lt r y t n hlt
    obtain ⟨⟨rps, rvv, rret, rcost, rneed, rwk⟩, hrr, hrret, hrps, hrvv, hrc, hrnd, hrw⟩ :=
      rest_part mv hnv hty P fu a (matC r y n t n) y (matC r y n t n) n e m hm hnn he hla hMl hly hMl hyM hfu hfu2
    simp only at htret htps htvv htc htnd htw hrret hrps hrvv hrc hrnd hrw
    subst htret htps htvv hrret hrps hrvv
    -- the branch
    have t1 := pexecM_scope mv fu _ _ _ _ htr
    simp only [tk] at t1
    have t2 := seqM_some t1 (by simp) (pexecM_skip mv fu _ _)
    have t3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ t2
    have t4 := seqM_some t3 (by simp) hrr
    have t5 := pexecM_scope mv fu _ _ _ _ t4
    simp only [tk2] at t5
    have t6 := seqM_some t5 (by simp) (pexecM_skip mv fu _ _)
    refine ⟨_, t6, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [rOf, yOf, tOf, hodd]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at htc hrc ⊢
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, gS_mem_len, gS_bs_len] at htnd hrnd ⊢
      omega
    · simp at htw hrw ⊢
      omega
  · rw [if_neg hodd] at hc
    obtain ⟨⟨rps, rvv, rret, rcost, rneed, rwk⟩, hrr, hrret, hrps, hrvv, hrc, hrnd, hrw⟩ :=
      rest_part mv hnv hty P fu a r y t n e m hm hnn he hla hlr hly hlt hyM hfu hfu2
    simp only at hrret hrps hrvv hrc hrnd hrw
    subst hrret hrps hrvv
    have t3 := pexecM_branch_false mv fu _ (.sequence (.scope (mulCopy mv.nv 1 2 3 1 Sk)) Sk) Sk _ _ hc _ (pexecM_skip mv fu _ _)
    have t4 := seqM_some t3 rfl hrr
    have t5 := pexecM_scope mv fu _ _ _ _ t4
    simp only [tk2] at t5
    have t6 := seqM_some t5 (by simp) (pexecM_skip mv fu _ _)
    refine ⟨_, t6, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [rOf, yOf, tOf, hodd]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hrc ⊢
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, gS_mem_len, gS_bs_len] at hrnd ⊢
      omega
    · simp at hrw ⊢
      omega

def stepP (n : Nat) (s : List Nat × List Nat × List Nat) (e : Nat) : List Nat × List Nat × List Nat :=
  (rOf s.1 s.2.1 s.2.2 n e, yOf s.1 s.2.1 s.2.2 n e, yOf s.1 s.2.1 s.2.2 n e)

def powRun (n : Nat) : Nat → List Nat × List Nat × List Nat → Nat → List Nat × List Nat × List Nat
  | 0, s, _ => s
  | k + 1, s, e => if e = 0 then s else powRun n k (stepP n s e) (e / 2)

def CBW (n m : Nat) : Nat := 2 * (cIG n + 120 * m + 300) + 500

set_option maxHeartbeats 128000000 in
/-- The loop `while (e != 0)`. -/
theorem pow_while (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = u64) (P : List Cell) (a : List Nat)
    (n m : Nat) (hm : m = n * n) (hnn : n * n < 2147483647) (hla : a.length = n * n) :
    ∀ (k e : Nat) (r y t : List Nat) (fu : Nat), e < 2 ^ k → e < M64 → r.length = n * n → y.length = n * n →
      t.length = n * n → (∀ x ∈ r, x < M64) → (∀ x ∈ y, x < M64) → k + (3 * n + 4 + m + 2) ≤ fu →
      ∃ res : PRM, pexecM mv fu (.whileLoop (.binary bT .ne (.variable u64 (mv.nv + 1)) zeroU) (powLoopBody mv.nv))
          (gS P (CE n e m)) (VP a r y t) = some res ∧ res.ret = none ∧ res.ps = gS P (CE n 0 m) ∧
        res.vv = VP a (powRun n k (r, y, t) e).1 (powRun n k (r, y, t) e).2.1 (powRun n k (r, y, t) e).2.2 ∧
        res.cost ≤ k * CBW n m + 50 ∧ res.need ≤ P.length + 2 * 4 + 200 ∧ res.wk ≤ k * (2 * (n * n + m)) := by
  intro k
  induction k with
  | zero =>
    intro e r y t fu he0 he hlr hly hlt hrM hyM hfu
    have he' : e = 0 := by simpa using he0
    subst he'
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := ne_val mv (VP a r y t) P n 0 m he
    rw [if_neg (by simp)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, powRun]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ k ih =>
    intro e r y t fu he0 he hlr hly hlt hrM hyM hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    by_cases hz : e = 0
    · subst hz
      have hc := ne_val mv (VP a r y t) P n 0 m he
      rw [if_neg (by simp)] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [powRun]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, powRun]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
      · simp
    · have hc := ne_val mv (VP a r y t) P n e m he
      rw [if_pos hz] at hc
      obtain ⟨res1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := loop_body mv hnv hty P (fu' + 1) a r y t n e m hm hnn he hz hla hlr hly hlt hrM hyM
        (by omega) (by omega)
      have hlr1 : (rOf r y t n e).length = n * n := by
        unfold rOf; split
        · rw [matC_length]; exact hlt
        · exact hlr
      have hlt1 : (tOf r y t n e).length = n * n := by
        unfold tOf; split
        · rw [matC_length]; exact hlt
        · exact hlt
      have hly1 : (yOf r y t n e).length = n * n := by
        unfold yOf; rw [matC_length]; exact hlt1
      have hrM1 : ∀ x ∈ rOf r y t n e, x < M64 := by
        unfold rOf; split
        · exact matC_lt r y t n hlt
        · exact hrM
      have hyM1 : ∀ x ∈ yOf r y t n e, x < M64 := by
        unfold yOf; exact matC_lt y y (tOf r y t n e) n hlt1
      obtain ⟨res2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih (e / 2) (rOf r y t n e) (yOf r y t n e) (yOf r y t n e) fu'
        (by
          have : e < 2 ^ (k + 1) := he0
          rw [Nat.pow_succ] at this
          omega) (by omega) hlr1 hly1 hly1 hrM1 hyM1 (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
      rw [h1]
      simp only [ret1, ps1, vv1]
      rw [h2]
      simp only
      refine ⟨_, rfl, ret2, ps2, ?_, ?_, ?_, ?_⟩
      · rw [vv2]
        simp [powRun, hz, stepP]
      · rw [Nat.succ_mul]
        simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, CBW] at c1 c2 ⊢
        omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢
        omega
      · rw [Nat.succ_mul]
        simp at w1 w2 ⊢
        omega

/-! ### What the loop computes -/

open Proofs.MatPowMath (PW mulF EqOn Bd Idm PW_add PW_bd mulF_congr mulF_one_left)

theorem mul_two_aux (ky q : Nat) : (ky + ky) * q = ky * (2 * q) := by
  rw [Nat.add_mul, Nat.two_mul, Nat.mul_add]

theorem powRun_spec (n : Nat) (A : Nat → Nat → Nat) (E : Nat) :
    ∀ (k e : Nat) (r y t : List Nat) (kr ky : Nat), e < 2 ^ k → r.length = n * n → y.length = n * n → t.length = n * n →
      (∀ x ∈ r, x < M64) → (∀ x ∈ y, x < M64) → EqOn n (toF n r) (PW n A kr) → EqOn n (toF n y) (PW n A ky) →
      kr + ky * e = E →
      (powRun n k (r, y, t) e).1.length = n * n ∧ (∀ x ∈ (powRun n k (r, y, t) e).1, x < M64) ∧
        EqOn n (toF n (powRun n k (r, y, t) e).1) (PW n A E) := by
  intro k
  induction k with
  | zero =>
    intro e r y t kr ky he hlr hly hlt hrM hyM hr hy hE
    have he' : e = 0 := by simpa using he
    subst he'
    refine ⟨hlr, hrM, ?_⟩
    simp only [powRun]
    have : kr = E := by simpa using hE
    subst this
    exact hr
  | succ k ih =>
    intro e r y t kr ky he hlr hly hlt hrM hyM hr hy hE
    by_cases hz : e = 0
    · subst hz
      refine ⟨by simpa [powRun] using hlr, by simpa [powRun] using hrM, ?_⟩
      simp only [powRun, if_pos rfl]
      have : kr = E := by simpa using hE
      subst this
      exact hr
    · simp only [powRun, if_neg hz]
      have hlt1 : (tOf r y t n e).length = n * n := by
        unfold tOf; split
        · rw [matC_length]; exact hlt
        · exact hlt
      have hlr1 : (rOf r y t n e).length = n * n := by
        unfold rOf; split
        · rw [matC_length]; exact hlt
        · exact hlr
      have hly1 : (yOf r y t n e).length = n * n := by
        unfold yOf; rw [matC_length]; exact hlt1
      have hrM1 : ∀ x ∈ rOf r y t n e, x < M64 := by
        unfold rOf; split
        · exact matC_lt r y t n hlt
        · exact hrM
      have hyM1 : ∀ x ∈ yOf r y t n e, x < M64 := by
        unfold yOf; exact matC_lt y y (tOf r y t n e) n hlt1
      have hy1 : EqOn n (toF n (yOf r y t n e)) (PW n A (ky + ky)) := by
        unfold yOf
        have h1 := (matC_toF y y (tOf r y t n e) n hlt1).2
        intro i j hi hj
        rw [h1 i j hi hj]
        have h2 := mulF_congr n (toF n y) (PW n A ky) (toF n y) (PW n A ky) hy hy i j hi hj
        rw [h2]
        exact ((PW_add n A ky ky) i j hi hj).symm
      have hr1 : ∃ kr1, EqOn n (toF n (rOf r y t n e)) (PW n A kr1) ∧ kr1 = kr + (if e % 2 = 1 then ky else 0) := by
        by_cases hodd : e % 2 = 1
        · refine ⟨kr + ky, ?_, by simp [hodd]⟩
          unfold rOf
          rw [if_pos hodd]
          have h1 := (matC_toF r y t n hlt).2
          intro i j hi hj
          rw [h1 i j hi hj]
          have h2 := mulF_congr n (toF n r) (PW n A kr) (toF n y) (PW n A ky) hr hy i j hi hj
          rw [h2]
          exact ((PW_add n A kr ky) i j hi hj).symm
        · refine ⟨kr, ?_, by simp [hodd]⟩
          unfold rOf
          rw [if_neg hodd]
          exact hr
      obtain ⟨kr1, hr1, hkr1⟩ := hr1
      apply ih (e / 2) (rOf r y t n e) (yOf r y t n e) (yOf r y t n e) kr1 (ky + ky) (by
          have : e < 2 ^ (k + 1) := he
          rw [Nat.pow_succ] at this
          omega) hlr1 hly1 hly1 hrM1 hyM1 hr1 hy1
      -- kr1 + (ky + ky) * (e / 2) = E
      rw [hkr1, mul_two_aux]
      have hd : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      have hE' : kr + ky * (2 * (e / 2) + e % 2) = E := by rw [← hd]; exact hE
      rw [Nat.mul_add] at hE'
      by_cases hodd : e % 2 = 1
      · rw [if_pos hodd]; rw [hodd] at hE'; omega
      · have h0 : e % 2 = 0 := by omega
        rw [if_neg hodd]; rw [h0] at hE'; omega

theorem init_lt (r0 : List Nat) (n : Nat) (hl : r0.length = n * n) :
    ∀ x ∈ diagL (zeroL r0 (n * n)) n n, x < M64 := by
  intro x hx
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hx
  have hl' : (diagL (zeroL r0 (n * n)) n n).length = n * n := by rw [diagL_len, zeroL_len, hl]
  have hid : idx < n * n := by omega
  have : (diagL (zeroL r0 (n * n)) n n).getD idx 0 = (diagL (zeroL r0 (n * n)) n n)[idx] := by
    simp [List.getD_eq_getElem?_getD, hidx]
  rw [← this, diagL_get, zeroL_len, hl, zeroL_get, hl]
  by_cases h1 : (∃ u, u < n ∧ idx = u * n + u) ∧ idx < n * n
  · rw [if_pos h1]; decide
  · rw [if_neg h1, if_pos ⟨hid, hid⟩]; decide

def CTOT (n : Nat) : Nat := 64 * CBW n (n * n) + 360 * (n * n) + 400

theorem mm_val (mv : MV) (vv : Nat → List Int) (P : List Cell) (n e : Nat) (hnn : n * n < 2147483648) (he : e < M64) :
    vdenM mv vv (penvN mv.nv (gS P [ci n, cu e])) (.binary i32 .mul (.variable i32 (mv.nv + 0)) (.variable i32 (mv.nv + 0))) =
      some ((n * n : Nat) : Int) := by
  have hn32 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  have E : penvN mv.nv (gS P [ci n, cu e]) (mv.nv + 0) i32 = some (n : Int) :=
    envs mv P [ci n, cu e] 0 (ci n) rfl (validN n hn32)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E, Option.bind_some, Option.bind_some]
  have : binaryValue .mul (n : Int) (n : Int) = ((n * n : Nat) : Int) := by
    show (n : Int) * (n : Int) = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ hnn)

set_option maxHeartbeats 128000000 in
/-- The whole body of `mat_pow`. -/
theorem body_pow (mv : MV) (hnv : mv.nv = 4) (hty : ∀ k, mv.ty k = u64) (P : List Cell) (fu : Nat) (a r0 y0 t0 : List Nat)
    (n e : Nat) (hnn : n * n < 2147483647) (he : e < M64) (hla : a.length = n * n) (hlr : r0.length = n * n)
    (hly : y0.length = n * n) (hlt : t0.length = n * n) (haM : ∀ x ∈ a, x < M64)
    (hfu : 64 + (3 * n + 4 + n * n + 2) ≤ fu) :
    ∃ res : PRM, pexecM mv fu (bodyPow mv.nv) (gS P [ci n, cu e]) (VP a r0 y0 t0) = some res ∧ res.ret = none ∧
      res.ps = gS P (CE n 0 (n * n)) ∧
      res.vv = VP a (powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).1 (powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).2.1
        (powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).2.2 ∧
      res.cost ≤ CTOT n ∧ res.need ≤ P.length + 2 * 4 + 200 ∧ res.wk ≤ 64 * (2 * (n * n + n * n)) + 3 * (n * n) := by
  have hm' : n * n < 2147483647 := hnn
  have d := gSM_decl mv P [ci n, cu e] (VP a r0 y0 t0) i32 _ ((n * n : Nat) : Int) ((n * n : Nat) : Int)
    (mm_val mv _ P n e (by omega) he) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have a1 := (pexecM_prim mv fu _ _ _).trans d
  -- y = a
  obtain ⟨⟨cps, cvv, cret, ccost, cneed, cwk⟩, hcr, hcps, hcvv, hcret, hcc, hcnd, hcw⟩ :=
    copy_loop mv hty (VP a r0 y0 t0) 2 0 (by omega) (by omega) (by decide) y0 a (VP_get2 _ _ _ _) (VP_get0 _ _ _ _) haM P
      (CE n e (n * n)) 3 2 (n * n) (by omega) (by simp) (by simp) hm' hly hla fu (by omega)
  simp only at hcps hcvv hcret hcc hcnd hcw
  subst hcps hcvv hcret
  rw [VP_upd2] at hcr
  -- r = 0
  obtain ⟨⟨zps, zvv, zret, zcost, zneed, zwk⟩, hzr, hzps, hzvv, hzret, hzc, hznd, hzw⟩ :=
    zero_loop mv hty (VP a r0 a t0) 1 (by omega) r0 (VP_get1 _ _ _ _) P (CE n e (n * n)) 3 2 (n * n) (by omega) (by simp)
      (by simp) hm' hlr fu (by omega)
  simp only at hzps hzvv hzret hzc hznd hzw
  subst hzps hzvv hzret
  rw [VP_upd1] at hzr
  -- diagonal
  obtain ⟨⟨dps, dvv, dret, dcost, dneed, dwk⟩, hdr, hdps, hdvv, hdret, hdc, hdnd, hdw⟩ :=
    diag_loop mv hty (VP a (zeroL r0 (n * n)) a t0) 1 (by omega) (zeroL r0 (n * n)) (VP_get1 _ _ _ _) P (CE n e (n * n)) 3 0 n
      (by omega) (by simp) (by simp) (by omega) (by rw [zeroL_len]; exact hlr) fu (by omega)
  simp only at hdps hdvv hdret hdc hdnd hdw
  subst hdps hdvv hdret
  rw [VP_upd1] at hdr
  have hlD := (init_identity r0 n hlr).1
  -- the loop
  have hpw : e < 2 ^ 64 := by
    have : (2 : Nat) ^ 64 = M64 := rfl
    omega
  obtain ⟨wres, hwr, hwret, hwps, hwvv, hwc, hwnd, hwwk⟩ :=
    pow_while mv hnv hty P a n (n * n) rfl hnn hla 64 e (diagL (zeroL r0 (n * n)) n n) a t0 fu hpw he hlD hla hlt
      (init_lt r0 n hlr) haM (by omega)
  have b4 := seqM_some hwr hwret (pexecM_skip mv fu _ _)
  have b3 := seqM_some hdr rfl b4
  have b2 := seqM_some hzr rfl b3
  have b1 := seqM_some hcr rfl b2
  have b0 := seqM_some a1 rfl b1
  have hnm := Nat.le_mul_self n
  refine ⟨_, b0, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwps]
  · rw [hwvv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, CTOT] at hcc hzc hdc hwc ⊢
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, gS_mem_len, gS_bs_len] at hcnd hznd hdnd hwnd ⊢
    rw [hwps] at *
    simp [gS_mem_len, gS_bs_len] at *
    omega
  · simp at hcw hzw hdw hwwk ⊢
    omega

/-- The result of `mat_pow`: the `e`-th power of the matrix `a`. -/
theorem pow_final (n e : Nat) (hnn : n * n < 2147483647) (he : e < M64) (a r0 t0 : List Nat) (hla : a.length = n * n)
    (hlr : r0.length = n * n) (hlt : t0.length = n * n) (haM : ∀ x ∈ a, x < M64) :
    (powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).1.length = n * n ∧
    (∀ x ∈ (powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).1, x < M64) ∧
    ∀ i j, i < n → j < n → (powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).1.getD (i * n + j) 0 =
      PW n (toF n a) e i j := by
  have hpw : e < 2 ^ 64 := by
    have : (2 : Nat) ^ 64 = M64 := rfl
    omega
  have hBd : Bd n (toF n a) := by
    intro i j hi hj
    have hij : i * n + j < n * n := Proofs.MatMulExec.idx_lt n i j hi hj
    unfold toF
    have : a.getD (i * n + j) 0 = a[i * n + j]'(by omega) := by simp [List.getD_eq_getElem?_getD, hla, hij]
    rw [this]; exact haM _ (List.getElem_mem _)
  have hr : EqOn n (toF n (diagL (zeroL r0 (n * n)) n n)) (PW n (toF n a) 0) := by
    intro i j hi hj
    exact (init_identity r0 n hlr).2 i j hi hj
  have hy : EqOn n (toF n a) (PW n (toF n a) 1) := by
    intro i j hi hj
    exact ((Proofs.MatPowMath.mulF_one_left n (toF n a) hBd) i j hi hj).symm
  obtain ⟨hl, hM, hE⟩ := powRun_spec n (toF n a) e 64 e (diagL (zeroL r0 (n * n)) n n) a t0 0 1 hpw
    (init_identity r0 n hlr).1 hla hlt (init_lt r0 n hlr) haM hr hy (by omega)
  exact ⟨hl, hM, fun i j hi hj => hE i j hi hj⟩

end Proofs.MatPowExec













