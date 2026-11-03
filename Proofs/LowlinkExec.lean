import Proofs.LowlinkProg
import Proofs.LowlinkLists

namespace Proofs.LowlinkExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getM vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false)
open Proofs.DijkstraScan
open Proofs.DijkstraExec
open Proofs.LowlinkProg Proofs.LowlinkLists

/-- The vectors of `lowlink`: `head`, `target` (read-only), `ord`, `low`, `par`, `sep`, `it`, `stk`. -/
def VX (H T : List Nat) (x : XS) : Nat → List Int := fun k =>
  if k = 0 then H.map (fun a : Nat => (a : Int)) else if k = 1 then T.map (fun a : Nat => (a : Int))
  else if k = 2 then x.Ol else if k = 3 then x.Ll else if k = 4 then x.Pl else if k = 5 then x.Sl
  else if k = 6 then x.Il else if k = 7 then x.Kl else []

theorem VX_0 (H T x) : VX H T x 0 = H.map (fun a : Nat => (a : Int)) := by simp [VX]
theorem VX_1 (H T x) : VX H T x 1 = T.map (fun a : Nat => (a : Int)) := by simp [VX]
theorem VX_2 (H T x) : VX H T x 2 = x.Ol := by simp [VX]
theorem VX_3 (H T x) : VX H T x 3 = x.Ll := by simp [VX]
theorem VX_4 (H T x) : VX H T x 4 = x.Pl := by simp [VX]
theorem VX_5 (H T x) : VX H T x 5 = x.Sl := by simp [VX]
theorem VX_6 (H T x) : VX H T x 6 = x.Il := by simp [VX]
theorem VX_7 (H T x) : VX H T x 7 = x.Kl := by simp [VX]

theorem VX_w2 (H T x L') : upd (VX H T x) 2 L' = VX H T { x with Ol := L' } := by
  funext j; simp only [upd, VX]; split_ifs <;> simp_all
theorem VX_w3 (H T x L') : upd (VX H T x) 3 L' = VX H T { x with Ll := L' } := by
  funext j; simp only [upd, VX]; split_ifs <;> simp_all
theorem VX_w4 (H T x L') : upd (VX H T x) 4 L' = VX H T { x with Pl := L' } := by
  funext j; simp only [upd, VX]; split_ifs <;> simp_all
theorem VX_w5 (H T x L') : upd (VX H T x) 5 L' = VX H T { x with Sl := L' } := by
  funext j; simp only [upd, VX]; split_ifs <;> simp_all
theorem VX_w6 (H T x L') : upd (VX H T x) 6 L' = VX H T { x with Il := L' } := by
  funext j; simp only [upd, VX]; split_ifs <;> simp_all
theorem VX_w7 (H T x L') : upd (VX H T x) 7 L' = VX H T { x with Kl := L' } := by
  funext j; simp only [upd, VX]; split_ifs <;> simp_all


/-! ### Evaluation of the expressions of the program -/

section Eval
variable (mv : MV) (vv : Nat → List Int) (P cl : List Cell)

theorem ev_cell {j x : Nat} (hj : cl[j]? = some (ci x)) (hx : x < M31) :
    penvN mv.nv (gS P cl) (mv.nv + j) i32 = some (x : Int) :=
  envs mv P cl j (ci x) hj (i32v x hx)

theorem d_vr {j x : Nat} (hj : cl[j]? = some (ci x)) (hx : x < M31) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (vr mv.nv j) = some (x : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_variable]
  exact ev_cell mv P cl hj hx

theorem d_ixc {j x : Nat} (hj : cl[j]? = some (ci x)) (hx : x < M31) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (ixc mv.nv j) = some (x : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  exact cidx_den _ (mv.nv + j) x (ev_cell mv P cl hj hx) hx

theorem d_rdv {k j x : Nat} (hk : k < mv.nv) (hty : mv.ty k = i32) (hj : cl[j]? = some (ci x)) (hx : x < M31)
    (y : Int) (hy : (vv k)[x]? = some y) (hv : i32.valid y = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (rdv mv.nv k j) = some y :=
  rdM_val mv vv _ k hk i32 hty.symm (ixc mv.nv j) rfl rfl x (cidx_den _ (mv.nv + j) x (ev_cell mv P cl hj hx) hx) y hy
    (by rw [hty]; exact hv)

theorem den_cast_u64 (env : Nat → Ty → Option Int) (e : NExpr) (x : Nat) (h : e.denote env = some (x : Int))
    (hx : x < M31) : (NExpr.cast u64 e).denote env = some (x : Int) := by
  rw [den_cast, h, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : x < 2147483648 := hx; omega)

theorem add1_den (env : Nat → Ty → Option Int) (k x : Nat) (h : env k i32 = some (x : Int)) (hx : x + 1 < M31) :
    (NExpr.binary i32 .add (.variable i32 k) one).denote env = some ((x + 1 : Nat) : Int) := by
  have o : one.denote env = some 1 := by
    show (NExpr.literal i32 1).denote env = some 1
    rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]
  rw [den_binary, den_variable, h, Option.bind_some, o, Option.bind_some]
  have e : binaryValue .add (x : Int) 1 = ((x + 1 : Nat) : Int) := by
    show (x : Int) + 1 = _; push_cast; rfl
  rw [e]
  exact conv_signed i32 rfl rfl _ (i32v _ hx)

theorem sub1_den (env : Nat → Ty → Option Int) (k x : Nat) (h : env k i32 = some (x : Int)) (hx : x < M31) (h1 : 1 ≤ x) :
    (NExpr.binary i32 .sub (.variable i32 k) one).denote env = some ((x - 1 : Nat) : Int) := by
  have o : one.denote env = some 1 := by
    show (NExpr.literal i32 1).denote env = some 1
    rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]
  rw [den_binary, den_variable, h, Option.bind_some, o, Option.bind_some]
  have e : binaryValue .sub (x : Int) 1 = ((x - 1 : Nat) : Int) := by
    show (x : Int) - 1 = _; omega
  rw [e]
  exact conv_signed i32 rfl rfl _ (i32v _ (by omega))

theorem d_idxTop {x : Nat} (hj : cl[3]? = some (ci x)) (hx : x < M31) (h1 : 1 ≤ x) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (idxTop mv.nv) = some ((x - 1 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  exact den_cast_u64 _ _ _ (sub1_den _ _ x (ev_cell mv P cl hj hx) hx h1) (by omega)

theorem d_idxV1 {x : Nat} (hj : cl[4]? = some (ci x)) (hx : x + 1 < M31) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (idxV1 mv.nv) = some ((x + 1 : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  exact den_cast_u64 _ _ _ (add1_den _ _ x (ev_cell mv P cl hj (by omega)) hx) hx

theorem d_zero : vdenM mv vv (penvN mv.nv (gS P cl)) lit0 = some 0 := by
  rw [vdenM_scalar _ _ _ _ rfl, zero_den]

theorem d_one : vdenM mv vv (penvN mv.nv (gS P cl)) one = some 1 := by
  rw [vdenM_scalar _ _ _ _ rfl]
  show (NExpr.literal i32 1).denote _ = some 1
  rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]

theorem bt_lt (x y : Int) : bT.convert (binaryValue .lt x y) = some (if x < y then 1 else 0) := by
  by_cases h : x < y <;> simp [binaryValue, h, Ty.convert, bT, Ty.valid]
theorem bt_gt (x y : Int) : bT.convert (binaryValue .gt x y) = some (if x > y then 1 else 0) := by
  by_cases h : x > y <;> simp [binaryValue, h, Ty.convert, bT, Ty.valid]
theorem bt_le (x y : Int) : bT.convert (binaryValue .le x y) = some (if x ≤ y then 1 else 0) := by
  by_cases h : x ≤ y <;> simp [binaryValue, h, Ty.convert, bT, Ty.valid]
theorem bt_ne (x y : Int) : bT.convert (binaryValue .ne x y) = some (if x ≠ y then 1 else 0) := by
  by_cases h : x = y
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : (x != y) = true := by simp [h]
    simp [binaryValue, this, h, Ty.convert, bT, Ty.valid]

theorem d_binb {op : Binary} {a b : NExpr} (hs : (NExpr.binary bT op a b).scalarOnly = false) {x y : Int}
    (ha : vdenM mv vv (penvN mv.nv (gS P cl)) a = some x) (hb : vdenM mv vv (penvN mv.nv (gS P cl)) b = some y) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT op a b) = bT.convert (binaryValue op x y) := by
  rw [vdenM_binary _ _ _ _ _ _ _ hs, ha, Option.bind_some, hb, Option.bind_some]

theorem d_add1 {a : NExpr} (hs : (NExpr.binary i32 .add a one).scalarOnly = false) {x : Nat}
    (ha : vdenM mv vv (penvN mv.nv (gS P cl)) a = some (x : Int)) (hx : x + 1 < M31) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary i32 .add a one) = some ((x + 1 : Nat) : Int) := by
  rw [vdenM_binary _ _ _ _ _ _ _ hs, ha, Option.bind_some, d_one, Option.bind_some]
  have e : binaryValue .add (x : Int) 1 = ((x + 1 : Nat) : Int) := by
    show (x : Int) + 1 = _; push_cast; rfl
  rw [e]
  exact conv_signed i32 rfl rfl _ (i32v _ hx)

theorem d_add1I {a : NExpr} (hs : (NExpr.binary i32 .add a one).scalarOnly = false) {x : Int}
    (ha : vdenM mv vv (penvN mv.nv (gS P cl)) a = some x) (hx : i32.valid (x + 1) = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary i32 .add a one) = some (x + 1) := by
  rw [vdenM_binary _ _ _ _ _ _ _ hs, ha, Option.bind_some, d_one, Option.bind_some]
  exact conv_signed i32 rfl rfl _ hx

end Eval


/-! ### `if (c) { vector[k][i] = e; }` -/

theorem cw_true (mv : MV) (fu : Nat) (c iE vE : NExpr) (k : Nat) (hk : k < mv.nv) (hty : mv.ty k = i32) (ps : PS)
    (vv : Nat → List Int) (b : Int) (hc : vdenM mv vv (penvN mv.nv ps) c = some b) (hb : b ≠ 0) (x : Int) (p : Nat)
    (hx : vdenM mv vv (penvN mv.nv ps) vE = some x) (hp : vdenM mv vv (penvN mv.nv ps) iE = some (p : Int))
    (hlt : p < (vv k).length) (hv : i32.valid x = true) :
    ∃ r : PRM, pexecM mv fu (CWb c (.write (.local k) i32 iE vE)) ps vv = some r ∧ r.ret = none ∧ r.ps = ps ∧
      r.vv = upd vv k ((vv k).set p x) ∧
      r.cost = (vwp vE).1 + (vwp iE).1 + 3 + 1 + (vwp c).1 + 1 ∧
      r.need ≤ ps.mem.length + ps.bs.length + (vwp c).2 + iE.nodes + vE.nodes + (vwp vE).2 + (vwp iE).2 + 5 ∧
      r.wk = 1 := by
  have wr := pstmtM_write_ok mv ps vv k hk iE vE x p hx hp hlt (by rw [hty]; exact hv)
  rw [hty] at wr
  have a1 := (pexecM_prim mv fu (.write (.local k) i32 iE vE) ps vv).trans wr
  have a2 := seqM_some a1 rfl (pexecM_skip mv fu ps _)
  have a3 := pexecM_scope mv fu _ ps _ _ a2
  simp only [List.take_length] at a3
  have a4 := seqM_some a3 rfl (pexecM_skip mv fu ps _)
  have a5 := pexecM_branch_true mv fu c _ Sk ps vv b hc hb _ a4
  refine ⟨_, a5, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp
    omega
  · simp

theorem cw_false (mv : MV) (fu : Nat) (c : NExpr) (s : NStmt) (ps : PS) (vv : Nat → List Int)
    (hc : vdenM mv vv (penvN mv.nv ps) c = some 0) :
    ∃ r : PRM, pexecM mv fu (CWb c s) ps vv = some r ∧ r.ret = none ∧ r.ps = ps ∧ r.vv = vv ∧
      r.cost = (vwp c).1 + 1 ∧ r.need ≤ ps.mem.length + ps.bs.length + (vwp c).2 + 2 ∧ r.wk = 0 := by
  have a := pexecM_branch_false mv fu c (.sequence (.scope (.sequence (.primitive s) Sk)) Sk) Sk ps vv hc _ (pexecM_skip mv fu ps vv)
  exact ⟨_, a, rfl, rfl, rfl, by simp, by simp; omega, by simp⟩


/-! ### Common facts -/

theorem i32_valid_iff (v : Int) : i32.valid v = true ↔ -2147483648 ≤ v ∧ v < 2147483648 := by
  show Ty.valid ⟨32, true, false⟩ v = true ↔ _
  simp [Ty.valid]


theorem rd_valid {l : List Int} (hv : ∀ y ∈ l, i32.valid y = true) {i : Nat} (hi : i < l.length) :
    i32.valid (l.getD i 0) = true := by
  apply hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem _

theorem scope_drop (mv : MV) (fu : Nat) (body : Command) (P cs cs' ds : List Cell) (vv : Nat → List Int) (r : PRM)
    (hl : cs.length = cs'.length) (hr : pexecM mv fu body (gS P cs) vv = some r) (hps : r.ps = gS P (cs' ++ ds)) :
    pexecM mv fu (.scope body) (gS P cs) vv = some ⟨gS P cs', r.vv, r.ret, r.cost + 1, r.need, r.wk⟩ := by
  have a := pexecM_scope mv fu body (gS P cs) vv r hr
  have tk := gS_takeC P cs cs' ds hl
  rw [hps, tk] at a
  exact a

theorem den_idxTop (env : Nat → Ty → Option Int) (nv x : Nat) (h : env (nv + 3) i32 = some (x : Int)) (hx : x < M31)
    (h1 : 1 ≤ x) : (idxTop nv).denote env = some ((x - 1 : Nat) : Int) := by
  have o : one.denote env = some 1 := by
    show (NExpr.literal i32 1).denote env = some 1
    rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]
  exact den_cast_u64 _ _ _ (by
    rw [den_binary, den_variable, h, Option.bind_some, o, Option.bind_some]
    have e : binaryValue .sub (x : Int) 1 = ((x - 1 : Nat) : Int) := by
      show (x : Int) - 1 = _; omega
    rw [e]
    exact conv_signed i32 rfl rfl _ (i32v _ (by omega))) (by omega)

/-- `stk[sp - 1]` -/
theorem d_stk {mv : MV} (vv : Nat → List Int) (P cl : List Cell) (hnv : mv.nv = 8) (hty : mv.ty 7 = i32) {sp : Nat}
    (hj : cl[3]? = some (ci sp)) (hsp : sp < M31) (h1 : 1 ≤ sp) (y : Int) (hy : (vv 7)[sp - 1]? = some y)
    (hv : i32.valid y = true) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.read i32 (.local 7) (idxTop mv.nv)) = some y := by
  have hidx : (idxTop mv.nv).denote (penvN mv.nv (gS P cl)) = some ((sp - 1 : Nat) : Int) :=
    den_idxTop _ mv.nv sp (ev_cell mv P cl hj hsp) hsp h1
  exact rdM_val mv vv _ 7 (by omega) i32 hty.symm (idxTop mv.nv) rfl rfl (sp - 1) hidx y hy (by rw [hty]; exact hv)

theorem d_cSp {mv : MV} (vv : Nat → List Int) (P cl : List Cell) {y : Nat} (hj : cl[3]? = some (ci y)) (hy : y < M31) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (cSp mv.nv) = some (if (y : Int) > 0 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  show (NExpr.binary bT .gt (.variable i32 (mv.nv + 3)) lit0).denote _ = _
  rw [den_binary, den_variable, ev_cell mv P cl hj hy, Option.bind_some, zero_den, Option.bind_some, bt_gt]

end Proofs.LowlinkExec
