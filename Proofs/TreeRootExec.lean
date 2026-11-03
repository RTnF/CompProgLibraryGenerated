import Proofs.ForLoopG
import Proofs.TreeRootMath
import Proofs.TopoSortExec
import Proofs.Generated.TreeRoot

namespace Proofs.TreeRootExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB Proofs.ForLoopG
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getM vec_getI vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false
  getD_mem cs s64_valid_of lt_conv)
open Proofs.TopoSortExec (i32v one_den zero_den natList_get sumIdx_den succIdx_den)
open Proofs.TopoSortMath (HeadOK)

/-! ### The program: variable `nv + c` is the scalar cell `c`
0 = root, 1 = n, 2 = sp, 3 = it, 4 = v, 5 = start, 6 = cnt, 7 = d, 8 = w;
vectors 0 = head, 1 = target, 2 = cost (long long), 3 = parent, 4 = depth, 5 = cost_depth (long long), 6 = stk -/

abbrev ix (nv c : Nat) : NExpr := .cast u64 (.variable i32 (nv + c))
abbrev lit1 : NExpr := .literal i32 1
abbrev lit0 : NExpr := .literal i32 0
abbrev sIdx (nv : Nat) : NExpr := .cast u64 (.binary i32 .add (.variable i32 (nv + 5)) (.variable i32 (nv + 7)))
-- inner body
abbrev dW (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 1) (sIdx nv))
abbrev c4 (nv : Nat) : NExpr := .binary bT .lt (.read i32 (.local 3) (ix nv 8)) lit0
abbrev w3 (nv : Nat) : NStmt := .write (.local 3) i32 (ix nv 8) (.variable i32 (nv + 4))
abbrev w4 (nv : Nat) : NStmt :=
  .write (.local 4) i32 (ix nv 8) (.binary i32 .add (.read i32 (.local 4) (ix nv 4)) lit1)
abbrev w5 (nv : Nat) : NStmt :=
  .write (.local 5) s64 (ix nv 8) (.binary s64 .add (.read s64 (.local 5) (ix nv 4)) (.read s64 (.local 2) (sIdx nv)))
abbrev w6 (nv : Nat) : NStmt := .write (.local 6) i32 (ix nv 2) (.variable i32 (nv + 8))
abbrev a2 (nv : Nat) : NStmt := .assign (nv + 2) i32 (.binary i32 .add (.variable i32 (nv + 2)) lit1)
abbrev Yin (nv : Nat) : Command :=
  .sequence (.primitive (w3 nv)) (.sequence (.primitive (w4 nv)) (.sequence (.primitive (w5 nv))
    (.sequence (.primitive (w6 nv)) (.sequence (.primitive (a2 nv)) Sk))))
abbrev Xin (nv : Nat) : Command :=
  .sequence (.primitive (dW nv)) (.sequence (.branch (c4 nv) (.sequence (.scope (Yin nv)) Sk) Sk) Sk)
-- outer body
abbrev dec2 (nv : Nat) : NStmt := .assign (nv + 2) i32 (.binary i32 .sub (.variable i32 (nv + 2)) lit1)
abbrev dV (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 6) (ix nv 2))
abbrev dS (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 0) (ix nv 4))
abbrev dC (nv : Nat) : NStmt :=
  .declare i32 true (.binary i32 .sub (.read i32 (.local 0) (.cast u64 (.binary i32 .add (.variable i32 (nv + 4)) lit1)))
    (.variable i32 (nv + 5)))
abbrev dDV (nv : Nat) : NStmt := .declare s64 true (.read s64 (.local 5) (ix nv 4))
abbrev dFF (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 6) (ix nv 1))
abbrev dMX (nv : Nat) : NStmt := .declare s64 true (.read s64 (.local 5) (ix nv 8))
abbrev cMX (nv : Nat) : NExpr := .binary bT .lt (.variable s64 (nv + 9)) (.variable s64 (nv + 7))
abbrev wFar (nv : Nat) : NStmt := .write (.local 6) i32 (ix nv 1) (.variable i32 (nv + 4))
abbrev Yfar (nv : Nat) : Command := .sequence (.scope (.sequence (.primitive (wFar nv)) Sk)) Sk
abbrev Zfar (nv : Nat) : Command :=
  .sequence (.primitive (dDV nv)) (.sequence (.primitive (dFF nv)) (.sequence (.primitive (dMX nv))
    (.sequence (.branch (cMX nv) (Yfar nv) Sk) Sk)))
abbrev Z3 (nv : Nat) : Command :=
  .sequence (.primitive (dec2 nv)) (.sequence (.primitive (dV nv)) (.sequence (.primitive (dS nv))
    (.sequence (.primitive (dC nv)) (.sequence (forStmtB nv 7 6 (Xin nv)) (Zfar nv)))))
abbrev c3 (nv : Nat) : NExpr := .binary bT .gt (.variable i32 (nv + 2)) lit0
abbrev B3 (nv : Nat) : Command := .sequence (.branch (c3 nv) (.sequence (.scope (Z3 nv)) Sk) Sk) Sk
-- prologue
abbrev pP (nv : Nat) : NStmt := .write (.local 3) i32 (ix nv 0) (.variable i32 nv)
abbrev pD (nv : Nat) : NStmt := .write (.local 4) i32 (ix nv 0) lit0
abbrev pC (nv : Nat) : NStmt := .write (.local 5) s64 (ix nv 0) (.cast s64 lit0)
abbrev pS (nv : Nat) : NStmt := .write (.local 6) i32 (.cast u64 lit0) (.variable i32 nv)
abbrev pF (nv : Nat) : NStmt := .write (.local 6) i32 (ix nv 1) (.variable i32 nv)
abbrev bodyTR (nv : Nat) : Command :=
  .sequence (.primitive (pP nv)) (.sequence (.primitive (pD nv)) (.sequence (.primitive (pC nv))
    (.sequence (.primitive (pS nv)) (.sequence (.primitive (pF nv)) (.sequence (.primitive (.declare i32 true lit1))
      (.sequence (forStmtB nv 3 1 (B3 nv)) Sk))))))

theorem body_eqTR : Proofs.TreeRootInstance.tree_root_std_vector_int.body = bodyTR 7 := rfl

/-- The contents of the seven vectors `head`, `target`, `cost`, `parent`, `depth`, `cost_depth`, `stk`. -/
def VR (H T : List Nat) (Cs Pa De Cd Stk : List Int) : Nat → List Int := fun k =>
  if k = 0 then H.map (fun x : Nat => (x : Int)) else if k = 1 then T.map (fun x : Nat => (x : Int))
  else if k = 2 then Cs else if k = 3 then Pa else if k = 4 then De else if k = 5 then Cd
  else if k = 6 then Stk else []

theorem VR_get0 (H T : List Nat) (Cs Pa De Cd Stk : List Int) : VR H T Cs Pa De Cd Stk 0 = H.map (fun x : Nat => (x : Int)) := by simp [VR]
theorem VR_get1 (H T : List Nat) (Cs Pa De Cd Stk : List Int) : VR H T Cs Pa De Cd Stk 1 = T.map (fun x : Nat => (x : Int)) := by simp [VR]
theorem VR_get2 (H T : List Nat) (Cs Pa De Cd Stk : List Int) : VR H T Cs Pa De Cd Stk 2 = Cs := by simp [VR]
theorem VR_get3 (H T : List Nat) (Cs Pa De Cd Stk : List Int) : VR H T Cs Pa De Cd Stk 3 = Pa := by simp [VR]
theorem VR_get4 (H T : List Nat) (Cs Pa De Cd Stk : List Int) : VR H T Cs Pa De Cd Stk 4 = De := by simp [VR]
theorem VR_get5 (H T : List Nat) (Cs Pa De Cd Stk : List Int) : VR H T Cs Pa De Cd Stk 5 = Cd := by simp [VR]
theorem VR_get6 (H T : List Nat) (Cs Pa De Cd Stk : List Int) : VR H T Cs Pa De Cd Stk 6 = Stk := by simp [VR]

theorem VR_set3 (H T : List Nat) (Cs Pa De Cd Stk x : List Int) : upd (VR H T Cs Pa De Cd Stk) 3 x = VR H T Cs x De Cd Stk := by
  funext k; unfold upd VR; split <;> simp_all
theorem VR_set4 (H T : List Nat) (Cs Pa De Cd Stk x : List Int) : upd (VR H T Cs Pa De Cd Stk) 4 x = VR H T Cs Pa x Cd Stk := by
  funext k; unfold upd VR; split <;> simp_all
theorem VR_set5 (H T : List Nat) (Cs Pa De Cd Stk x : List Int) : upd (VR H T Cs Pa De Cd Stk) 5 x = VR H T Cs Pa De x Stk := by
  funext k; unfold upd VR; split <;> simp_all
theorem VR_set6 (H T : List Nat) (Cs Pa De Cd Stk x : List Int) : upd (VR H T Cs Pa De Cd Stk) 6 x = VR H T Cs Pa De Cd x := by
  funext k; unfold upd VR; split <;> simp_all

open Proofs.TreeRootMath (St relax relax_new relax_of_visited InvB arcs relax_invB)

theorem i32_valid_of (x : Int) (h : -2147483648 ≤ x ∧ x < 2147483648) : i32.valid x = true := by
  show Ty.valid ⟨32, true, false⟩ x = true
  simp [Ty.valid]
  omega

def V32 (l : List Int) : Prop := ∀ x ∈ l, i32.valid x = true
def V64 (l : List Int) : Prop := ∀ x ∈ l, s64.valid x = true

/-- The stack vector holds the abstract stack in its first cells (it has one more cell, for the farthest vertex). -/
def StkOK (n : Nat) (Stk : List Int) (S : List Nat) : Prop :=
  Stk.length = n + 1 ∧ ∀ i, i < S.length → Stk.getD i 0 = ((S.getD i 0 : Nat) : Int)

/-- What the executions need to know about the abstract state and the vector contents. -/
structure Ctx (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int) : Prop where
  B : InvB H T Cs n root Cb st
  stk : StkOK n Stk st.S
  vp : V32 st.par
  vd : V32 st.dep
  vc : V64 st.cd
  vs : V32 Stk

theorem V32_set (l : List Int) (i : Nat) (x : Int) (h : V32 l) (hx : i32.valid x = true) : V32 (l.set i x) := by
  intro y hy
  rcases List.mem_or_eq_of_mem_set hy with h1 | h1
  · exact h y h1
  · rw [h1]; exact hx

theorem V64_set (l : List Int) (i : Nat) (x : Int) (h : V64 l) (hx : s64.valid x = true) : V64 (l.set i x) := by
  intro y hy
  rcases List.mem_or_eq_of_mem_set hy with h1 | h1
  · exact h y h1
  · rw [h1]; exact hx

/-- Looking at an arc to an already discovered vertex changes nothing. -/
theorem relax_ctx_old (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int) (v p : Nat)
    (C : Ctx H T Cs n root Cb st Stk) (h : 0 ≤ st.par.getD (T.getD p 0) 0) :
    Ctx H T Cs n root Cb (relax T Cs v p st) Stk := by
  rw [relax_of_visited T Cs v p st h]; exact C

/-- Looking at an arc to a new vertex discovers it. -/
theorem relax_ctx_new (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int) (v p : Nat)
    (C : Ctx H T Cs n root Cb st Stk) (hn : n < M31) (hv : v ∈ st.L) (hp : p ∈ arcs H v)
    (hT : T.getD p 0 < n) (hC : (Cs.getD p 0).natAbs ≤ Cb) (hCb : n * Cb < 9223372036854775808)
    (h : st.par.getD (T.getD p 0) 0 < 0) :
    Ctx H T Cs n root Cb (relax T Cs v p st) (Stk.set st.S.length (T.getD p 0)) := by
  have I1 := relax_invB H T Cs n root Cb st v p C.B hv hp hT hC
  have hlen := I1.S_len
  rw [relax_new T Cs v p st h] at I1 hlen ⊢
  have hSl : st.S.length + 1 ≤ n := by simpa using hlen
  have hvn : v < n := C.B.Llt v hv
  have hwL : T.getD p 0 ∉ st.L := fun h' => by
    have := (C.B.vis _ hT).mpr h'
    omega
  have hSk : st.S.length < Stk.length := by rw [C.stk.1]; omega
  refine ⟨I1, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [C.stk.1]
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hil : i < st.S.length
    · have hne : i ≠ st.S.length := by omega
      rw [Proofs.TreeRootMath.getD_set_ne Stk st.S.length i _ hne]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hil] at *
      exact C.stk.2 i hil
    · have hieq : i = st.S.length := by omega
      subst hieq
      simp [List.getD_eq_getElem?_getD, hSk]
  · exact V32_set _ _ _ C.vp (i32v v (by omega))
  · refine V32_set _ _ _ C.vd ?_
    obtain ⟨h1, h2⟩ := C.B.dep_range hv
    have hnI : (n : Int) < 2147483648 := by exact_mod_cast hn
    exact i32_valid_of _ (by omega)
  · refine V64_set _ _ _ C.vc (s64_valid_of _ ?_)
    have := C.B.cd_range hv (Cs.getD p 0) hC
    have h2 : (n : Int) * (Cb : Int) < 9223372036854775808 := by exact_mod_cast hCb
    omega
  · exact V32_set _ _ _ C.vs (i32v _ (by omega))

abbrev cells8 (root n sp it v start cnt d : Nat) : List Cell :=
  [ci root, ci n, ci sp, ci it, ci v, ci start, ci cnt, ci d]
abbrev cells9 (root n sp it v start cnt d w : Nat) : List Cell :=
  [ci root, ci n, ci sp, ci it, ci v, ci start, ci cnt, ci d, ci w]

theorem binary_add_val (a b : Int) : binaryValue .add a b = a + b := rfl

set_option maxHeartbeats 4000000 in
/-- The five statements executed when the target has not been discovered yet. -/
theorem yin_exec (mv : MV) (hnv : mv.nv = 7) (ty2 : mv.ty 2 = s64) (ty3 : mv.ty 3 = i32) (ty4 : mv.ty 4 = i32)
    (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = i32)
    (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int) (C : Ctx H T Cs n root Cb st Stk)
    (P : List Cell) (it v start cnt d w : Nat) (hn : n < M31) (hroot : root < n) (hit : it < M31) (hv : v ∈ st.L)
    (hstart : start < M31) (hcnt : cnt < M31) (hd : d < M31) (hp : start + d ∈ arcs H v)
    (hTl : T.length < M31) (hpT : start + d < T.length) (hCl : Cs.length = T.length)
    (hw : T.getD (start + d) 0 = w) (hwn : w < n) (hCb : ∀ q, (Cs.getD q 0).natAbs ≤ Cb)
    (hCbn : n * Cb < 9223372036854775808) (hsp1 : st.S.length + 1 ≤ n) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Yin mv.nv) (gS P (cells9 root n st.S.length it v start cnt d w))
        (VR H T Cs st.par st.dep st.cd Stk) = some r ∧ r.ret = none ∧
      r.ps = gS P (cells9 root n (st.S.length + 1) it v start cnt d w) ∧
      r.vv = VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1))
        (st.cd.set w (st.cd.getD v 0 + Cs.getD (start + d) 0)) (Stk.set st.S.length (w : Int)) ∧
      r.cost ≤ 600 ∧ r.need ≤ P.length + 70 ∧ r.wk ≤ 4 := by
  have hvn : v < n := C.B.Llt v hv
  have hlP := C.B.lenP
  have hlD := C.B.lenD
  have hlC := C.B.lenC
  have hSk := C.stk.1
  have hnI : (n : Int) < 2147483648 := by exact_mod_cast hn
  obtain ⟨hd1, hd2⟩ := C.B.dep_range hv
  have E4 := envs mv P (cells9 root n st.S.length it v start cnt d w) 4 (ci v) rfl (i32v v (by omega))
  have E5 := envs mv P (cells9 root n st.S.length it v start cnt d w) 5 (ci start) rfl (i32v start hstart)
  have E7 := envs mv P (cells9 root n st.S.length it v start cnt d w) 7 (ci d) rfl (i32v d hd)
  have E8 := envs mv P (cells9 root n st.S.length it v start cnt d w) 8 (ci w) rfl (i32v w (by omega))
  have E2 := envs mv P (cells9 root n st.S.length it v start cnt d w) 2 (ci st.S.length) rfl (i32v _ (by omega))
  have hidx8 : vdenM mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w)))
      (ix mv.nv 8) = some (w : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 8) w E8 (by omega)
  -- parent[w] = v
  have hx3 : vdenM mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w)))
      (.variable i32 (mv.nv + 4)) = some (v : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E4
  have w3' := pstmtM_write_ok mv (gS P (cells9 root n st.S.length it v start cnt d w)) (VR H T Cs st.par st.dep st.cd Stk) 3
    (by omega) (ix mv.nv 8) (.variable i32 (mv.nv + 4)) (v : Int) w hx3 hidx8 (by rw [VR_get3]; omega)
    (by rw [ty3]; exact i32v v (by omega))
  rw [ty3, VR_get3, VR_set3] at w3'
  have a1 := (pexecM_prim mv fu (w3 mv.nv) _ _).trans w3'
  -- depth[w] = depth[v] + 1
  have rdv := rdM_val mv (VR H T Cs (st.par.set w (v : Int)) st.dep st.cd Stk)
    (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w))) 4 (by omega) i32 ty4.symm (ix mv.nv 4) rfl rfl v
    (cidx_den _ (mv.nv + 4) v E4 (by omega)) (st.dep.getD v 0) (by rw [VR_get4]; exact vec_getI st.dep v (by omega))
    (by rw [ty4]; exact C.vd _ (getD_mem _ _ (by omega)))
  have hx4 : vdenM mv (VR H T Cs (st.par.set w (v : Int)) st.dep st.cd Stk)
      (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w)))
      (.binary i32 .add (.read i32 (.local 4) (ix mv.nv 4)) lit1) = some (st.dep.getD v 0 + 1) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, rdv, Option.bind_some, vdenM_scalar _ _ _ _ rfl, one_den, Option.bind_some,
      binary_add_val]
    exact conv_signed i32 rfl rfl _ (i32_valid_of _ (by omega))
  have w4' := pstmtM_write_ok mv (gS P (cells9 root n st.S.length it v start cnt d w))
    (VR H T Cs (st.par.set w (v : Int)) st.dep st.cd Stk) 4 (by omega) (ix mv.nv 8)
    (.binary i32 .add (.read i32 (.local 4) (ix mv.nv 4)) lit1) (st.dep.getD v 0 + 1) w hx4 hidx8
    (by rw [VR_get4]; omega) (by rw [ty4]; exact i32_valid_of _ (by omega))
  rw [ty4, VR_get4, VR_set4] at w4'
  have a2' := (pexecM_prim mv fu (w4 mv.nv) _ _).trans w4'
  -- cost_depth[w] = cost_depth[v] + cost[start + d]
  have hsidx : (sIdx mv.nv).denote (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w))) =
      some ((start + d : Nat) : Int) := sumIdx_den _ _ _ start d E5 E7 (by omega)
  have rcd := rdM_val mv (VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1)) st.cd Stk)
    (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w))) 5 (by omega) s64 ty5.symm (ix mv.nv 4) rfl rfl v
    (cidx_den _ (mv.nv + 4) v E4 (by omega)) (st.cd.getD v 0) (by rw [VR_get5]; exact vec_getI st.cd v (by omega))
    (by rw [ty5]; exact C.vc _ (getD_mem _ _ (by omega)))
  have rcs := rdM_val mv (VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1)) st.cd Stk)
    (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w))) 2 (by omega) s64 ty2.symm (sIdx mv.nv) rfl rfl
    (start + d) hsidx (Cs.getD (start + d) 0) (by rw [VR_get2]; exact vec_getI Cs _ (by omega))
    (by rw [ty2]; exact s64_valid_of _ (by
      have := hCb (start + d)
      have h2 : ((Cs.getD (start + d) 0).natAbs : Int) ≤ (Cb : Int) := by exact_mod_cast this
      have hn1 : (1 : Int) ≤ (n : Int) := by omega
      have h3 : (Cb : Int) ≤ (n : Int) * (Cb : Int) := by
        have := Int.mul_le_mul_of_nonneg_right hn1 (Int.natCast_nonneg Cb)
        omega
      have h4 : (n : Int) * (Cb : Int) < 9223372036854775808 := by exact_mod_cast hCbn
      omega))
  have hcdv : s64.valid (st.cd.getD v 0 + Cs.getD (start + d) 0) = true := by
    refine s64_valid_of _ ?_
    have := C.B.cd_range hv (Cs.getD (start + d) 0) (hCb _)
    have h4 : (n : Int) * (Cb : Int) < 9223372036854775808 := by exact_mod_cast hCbn
    omega
  have hx5 : vdenM mv (VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1)) st.cd Stk)
      (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w)))
      (.binary s64 .add (.read s64 (.local 5) (ix mv.nv 4)) (.read s64 (.local 2) (sIdx mv.nv))) =
      some (st.cd.getD v 0 + Cs.getD (start + d) 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, rcd, Option.bind_some, rcs, Option.bind_some, binary_add_val]
    exact conv_signed s64 rfl rfl _ hcdv
  have w5' := pstmtM_write_ok mv (gS P (cells9 root n st.S.length it v start cnt d w))
    (VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1)) st.cd Stk) 5 (by omega) (ix mv.nv 8)
    (.binary s64 .add (.read s64 (.local 5) (ix mv.nv 4)) (.read s64 (.local 2) (sIdx mv.nv)))
    (st.cd.getD v 0 + Cs.getD (start + d) 0) w hx5 hidx8 (by rw [VR_get5]; omega) (by rw [ty5]; exact hcdv)
  rw [ty5, VR_get5, VR_set5] at w5'
  have a3' := (pexecM_prim mv fu (w5 mv.nv) _ _).trans w5'
  -- stk[sp] = w
  have hidx2 : vdenM mv (VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1))
      (st.cd.set w (st.cd.getD v 0 + Cs.getD (start + d) 0)) Stk)
      (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w))) (ix mv.nv 2) = some (st.S.length : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 2) _ E2 (by omega)
  have hx6 : vdenM mv (VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1))
      (st.cd.set w (st.cd.getD v 0 + Cs.getD (start + d) 0)) Stk)
      (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w))) (.variable i32 (mv.nv + 8)) = some (w : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E8
  have w6' := pstmtM_write_ok mv (gS P (cells9 root n st.S.length it v start cnt d w))
    (VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1))
      (st.cd.set w (st.cd.getD v 0 + Cs.getD (start + d) 0)) Stk) 6 (by omega) (ix mv.nv 2)
    (.variable i32 (mv.nv + 8)) (w : Int) st.S.length hx6 hidx2 (by rw [VR_get6]; omega)
    (by rw [ty6]; exact i32v w (by omega))
  rw [ty6, VR_get6, VR_set6] at w6'
  have a4' := (pexecM_prim mv fu (w6 mv.nv) _ _).trans w6'
  -- sp = sp + 1
  have hx7 : vdenM mv (VR H T Cs (st.par.set w (v : Int)) (st.dep.set w (st.dep.getD v 0 + 1))
      (st.cd.set w (st.cd.getD v 0 + Cs.getD (start + d) 0)) (Stk.set st.S.length (w : Int)))
      (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w)))
      (.binary i32 .add (.variable i32 (mv.nv + 2)) lit1) = some ((st.S.length + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E2, Option.bind_some, one_den, Option.bind_some]
    have : binaryValue .add (st.S.length : Int) 1 = ((st.S.length + 1 : Nat) : Int) := by
      rw [binary_add_val]; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ (by omega))
  have as := gSM_assign mv P (cells9 root n st.S.length it v start cnt d w) (VR H T Cs (st.par.set w (v : Int))
    (st.dep.set w (st.dep.getD v 0 + 1)) (st.cd.set w (st.cd.getD v 0 + Cs.getD (start + d) 0))
    (Stk.set st.S.length (w : Int))) 2 (by simp) i32 _ _ _ hx7 (ci st.S.length) rfl rfl (i32v _ (by omega))
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have a5' := (pexecM_prim mv fu (a2 mv.nv) _ _).trans as
  have b1 := seqM_some a5' rfl (pexecM_skip mv fu _ _)
  have b2 := seqM_some a4' rfl b1
  have b3 := seqM_some a3' rfl b2
  have b4 := seqM_some a2' rfl b3
  have b5 := seqM_some a1 rfl b4
  refine ⟨_, b5, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
  · simp

set_option maxHeartbeats 8000000 in
/-- One iteration of the inner loop: `int w = target[start + d]; if (parent[w] < 0) {...}`. -/
theorem xin_body (mv : MV) (hnv : mv.nv = 7) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = s64) (ty3 : mv.ty 3 = i32)
    (ty4 : mv.ty 4 = i32) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = i32)
    (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int) (C : Ctx H T Cs n root Cb st Stk)
    (P : List Cell) (it v start cnt d : Nat) (hn : n < M31) (hroot : root < n) (hit : it < M31) (hv : v ∈ st.L)
    (hstart : start < M31) (hcnt : cnt < M31) (hd : d < M31) (hp : start + d ∈ arcs H v)
    (hTl : T.length < M31) (hpT : start + d < T.length) (hCl : Cs.length = T.length)
    (hTn : ∀ q, T.getD q 0 < n) (hCb : ∀ q, (Cs.getD q 0).natAbs ≤ Cb)
    (hCbn : n * Cb < 9223372036854775808) (fu : Nat) :
    ∃ (r : PRM) (Stk' : List Int), pexecM mv fu (Xin mv.nv) (gS P (cells8 root n st.S.length it v start cnt d))
        (VR H T Cs st.par st.dep st.cd Stk) = some r ∧ r.ret = none ∧
      r.ps = gS P (cells9 root n (relax T Cs v (start + d) st).S.length it v start cnt d (T.getD (start + d) 0)) ∧
      r.vv = VR H T Cs (relax T Cs v (start + d) st).par (relax T Cs v (start + d) st).dep
        (relax T Cs v (start + d) st).cd Stk' ∧
      Ctx H T Cs n root Cb (relax T Cs v (start + d) st) Stk' ∧ Stk'.getD n 0 = Stk.getD n 0 ∧
      r.cost ≤ 800 ∧ r.need ≤ P.length + 70 ∧ r.wk ≤ 4 := by
  have hvn : v < n := C.B.Llt v hv
  have hlP := C.B.lenP
  obtain ⟨w, hw⟩ : ∃ w, T.getD (start + d) 0 = w := ⟨_, rfl⟩
  have hwn : w < n := hw ▸ hTn _
  rw [hw]
  have E5 := envs mv P (cells8 root n st.S.length it v start cnt d) 5 (ci start) rfl (i32v start hstart)
  have E7 := envs mv P (cells8 root n st.S.length it v start cnt d) 7 (ci d) rfl (i32v d hd)
  have hsidx := sumIdx_den _ _ _ start d E5 E7 (by omega)
  have vr := rdM_val mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P (cells8 root n st.S.length it v start cnt d))) 1
    (by omega) i32 ty1.symm (sIdx mv.nv) rfl rfl (start + d) hsidx (w : Int)
    (by rw [VR_get1]; have := vec_getM T (start + d) hpT; rw [hw] at this; exact this) (by rw [ty1]; exact i32v w (by omega))
  have d1 := gSM_decl mv P (cells8 root n st.S.length it v start cnt d) (VR H T Cs st.par st.dep st.cd Stk) i32 _ _ _ vr
    (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
  have q1 := (pexecM_prim mv fu (dW mv.nv) _ _).trans d1
  have E8 := envs mv P (cells9 root n st.S.length it v start cnt d w) 8 (ci w) rfl (i32v w (by omega))
  have vi := rdM_val mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w)))
    3 (by omega) i32 ty3.symm (ix mv.nv 8) rfl rfl w (cidx_den _ (mv.nv + 8) w E8 (by omega)) (st.par.getD w 0)
    (by rw [VR_get3]; exact vec_getI st.par w (by omega)) (by rw [ty3]; exact C.vp _ (getD_mem _ _ (by omega)))
  have vc : vdenM mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P (cells9 root n st.S.length it v start cnt d w)))
      (c4 mv.nv) = some (if st.par.getD w 0 < 0 then 1 else 0) := by
    rw [vdenM_binary _ _ _ _ _ _ _ rfl, vi, Option.bind_some, vdenM_scalar _ _ _ _ rfl, zero_den, Option.bind_some]
    exact lt_conv _ _
  by_cases hneg : st.par.getD w 0 < 0
  · rw [if_pos hneg] at vc
    have hrel : (relax T Cs v (start + d) st).S = st.S ++ [w] := by
      rw [relax_new T Cs v (start + d) st (by rw [hw]; exact hneg), hw]
    have hC' := relax_ctx_new H T Cs n root Cb st Stk v (start + d) C hn hv hp (by rw [hw]; exact hwn) (hCb _) hCbn
      (by rw [hw]; exact hneg)
    rw [hw] at hC'
    have hsp1 : st.S.length + 1 ≤ n := by
      have := hC'.B.S_len
      rw [hrel] at this
      simpa using this
    obtain ⟨ry, hry, hret, hps, hvv, hc, hnd, hwk⟩ := yin_exec mv hnv ty2 ty3 ty4 ty5 ty6 H T Cs n root Cb st Stk C P it v start
      cnt d w hn hroot hit hv hstart hcnt hd hp hTl hpT hCl hw hwn hCb hCbn hsp1 fu
    have s1 := pexecM_scope mv fu _ _ _ ry hry
    have tk := gS_takeC P (cells9 root n st.S.length it v start cnt d w)
      (cells9 root n (st.S.length + 1) it v start cnt d w) [] rfl
    simp only [List.append_nil] at tk
    rw [hps] at s1
    simp only [tk] at s1
    have s2 := seqM_some s1 hret (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu (c4 mv.nv) (.sequence (.scope (Yin mv.nv)) Sk) Sk _ _ 1 vc (by decide) _ s2
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q1 rfl b2
    refine ⟨_, Stk.set st.S.length (w : Int), b3, rfl, ?_, ?_, hC', ?_, ?_, ?_, ?_⟩
    · rw [hrel]; simp
    · rw [hvv, relax_new T Cs v (start + d) st (by rw [hw]; exact hneg), hw]
    · rw [Proofs.TreeRootMath.getD_set_ne Stk st.S.length n _ (by omega)]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hnd ⊢; omega
    · simp at hwk ⊢; omega
  · rw [if_neg hneg] at vc
    have hvis : 0 ≤ st.par.getD (T.getD (start + d) 0) 0 := by rw [hw]; omega
    have hrel := relax_of_visited T Cs v (start + d) st hvis
    have hC' := relax_ctx_old H T Cs n root Cb st Stk v (start + d) C hvis
    have b1 := pexecM_branch_false mv fu (c4 mv.nv) (.sequence (.scope (Yin mv.nv)) Sk) Sk _ _ vc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q1 rfl b2
    refine ⟨_, Stk, b3, rfl, ?_, ?_, hC', rfl, ?_, ?_, ?_⟩
    · rw [hrel]
    · rw [hrel]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp

/-- The state after the first `d` arcs of `v` were looked at. -/
def foldA (T : List Nat) (Cs : List Int) (H : List Nat) (v d : Nat) (st : St) : St :=
  ((arcs H v).take d).foldl (fun s p => Proofs.TreeRootMath.relax T Cs v p s) st

theorem arcs_getElem (H : List Nat) (v d : Nat) (hd : d < (arcs H v).length) : (arcs H v)[d] = H.getD v 0 + d := by
  unfold arcs
  simp [List.getElem_range']

theorem foldA_succ (T : List Nat) (Cs : List Int) (H : List Nat) (v d : Nat) (st : St) (hd : d < (arcs H v).length) :
    foldA T Cs H v (d + 1) st = relax T Cs v (H.getD v 0 + d) (foldA T Cs H v d st) := by
  unfold foldA
  rw [Proofs.TopoSortMath.fold_take_succ (fun s p => relax T Cs v p s) (arcs H v) st d hd, arcs_getElem H v d hd]

theorem arcs_length (H : List Nat) (v : Nat) : (arcs H v).length = H.getD (v + 1) 0 - H.getD v 0 := by
  unfold arcs; simp

theorem foldA_full (T : List Nat) (Cs : List Int) (H : List Nat) (v : Nat) (st : St) :
    foldA T Cs H v (arcs H v).length st = (arcs H v).foldl (fun s p => relax T Cs v p s) st := by
  unfold foldA; rw [List.take_length]

open Proofs.TreeRootMath (relax_ext)

set_option maxHeartbeats 8000000 in
/-- The inner loop `for (int d = 0; d < cnt; d++) {...}`: looking at all arcs of `v`. -/
theorem xin_loop (mv : MV) (hnv : mv.nv = 7) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = s64) (ty3 : mv.ty 3 = i32)
    (ty4 : mv.ty 4 = i32) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = i32)
    (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int) (C : Ctx H T Cs n root Cb st Stk)
    (P : List Cell) (it v start cnt : Nat) (hn : n < M31) (hroot : root < n) (hit : it < M31) (hv : v ∈ st.L)
    (hstart : start = H.getD v 0) (hcnt : cnt = (arcs H v).length) (hcntM : cnt < 2147483647)
    (hTl : T.length < M31) (hend : start + cnt ≤ T.length) (hCl : Cs.length = T.length)
    (hTn : ∀ q, T.getD q 0 < n) (hCb : ∀ q, (Cs.getD q 0).natAbs ≤ Cb)
    (hCbn : n * Cb < 9223372036854775808) (fu : Nat) (hfu : cnt + 1 ≤ fu) :
    ∃ (res : PRM) (Stk' : List Int), pexecM mv fu (forStmtB mv.nv 7 6 (Xin mv.nv))
        (gS P [ci root, ci n, ci st.S.length, ci it, ci v, ci start, ci cnt]) (VR H T Cs st.par st.dep st.cd Stk) = some res ∧
      res.ps = gS P [ci root, ci n, ci (foldA T Cs H v cnt st).S.length, ci it, ci v, ci start, ci cnt] ∧
      res.vv = VR H T Cs (foldA T Cs H v cnt st).par (foldA T Cs H v cnt st).dep (foldA T Cs H v cnt st).cd Stk' ∧
      res.ret = none ∧ Ctx H T Cs n root Cb (foldA T Cs H v cnt st) Stk' ∧ v ∈ (foldA T Cs H v cnt st).L ∧
      Stk'.getD n 0 = Stk.getD n 0 ∧ res.cost ≤ 820 * cnt + 30 ∧ res.need ≤ P.length + 80 ∧ res.wk ≤ 4 * cnt := by
  have hnM : n < 2147483648 := hn
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 7 6 cnt (by omega) hcntM (Xin mv.nv)
    (fun d vv Cc => ∃ Stk', vv = VR H T Cs (foldA T Cs H v d st).par (foldA T Cs H v d st).dep (foldA T Cs H v d st).cd Stk' ∧
      Ctx H T Cs n root Cb (foldA T Cs H v d st) Stk' ∧ v ∈ (foldA T Cs H v d st).L ∧ Stk'.getD n 0 = Stk.getD n 0 ∧
      Cc = [ci root, ci n, ci (foldA T Cs H v d st).S.length, ci it, ci v, ci start, ci cnt])
    800 80 4 0 (by omega)
    (by
      intro d vv Cc fu hd hCl' hC6 ⟨Stk', hvv, hCx, hvL, hFS, hCc⟩ _
      subst hvv; subst hCc
      have hdl : d < (arcs H v).length := by omega
      have hp : H.getD v 0 + d ∈ arcs H v := by rw [← arcs_getElem H v d hdl]; exact List.getElem_mem hdl
      obtain ⟨r, Sk2, hr, hret, hps, hvv, hC', hFn, hc, hnd, hwk⟩ := xin_body mv hnv ty1 ty2 ty3 ty4 ty5 ty6 H T Cs n root Cb
        (foldA T Cs H v d st) Stk' hCx P it v start cnt d hn hroot hit hvL (by omega) (by omega) (by omega)
        (by rw [hstart]; exact hp) hTl (by omega) hCl hTn hCb hCbn fu
      obtain ⟨e1, hL1, _⟩ := relax_ext T Cs v (start + d) (foldA T Cs H v d st)
      refine ⟨r, [ci (T.getD (start + d) 0)], [ci root, ci n, ci (foldA T Cs H v (d + 1) st).S.length, ci it, ci v, ci start, ci cnt],
        hr, hret, ?_, rfl, rfl, ⟨Sk2, ?_, ?_, ?_, by rw [hFn, hFS], rfl⟩, hc, by omega, hwk⟩
      · rw [hps, foldA_succ T Cs H v d st hdl, ← hstart]; try rfl
      · rw [hvv, foldA_succ T Cs H v d st hdl, ← hstart]
      · rw [foldA_succ T Cs H v d st hdl, ← hstart]; exact hC'
      · rw [foldA_succ T Cs H v d st hdl, ← hstart, hL1]; exact List.mem_append.mpr (Or.inl hvL))
    (VR H T Cs st.par st.dep st.cd Stk) [ci root, ci n, ci st.S.length, ci it, ci v, ci start, ci cnt] rfl rfl
    ⟨Stk, by simp [foldA], by simpa [foldA] using C, by simpa [foldA] using hv, rfl, by simp [foldA]⟩ fu (by omega)
  obtain ⟨Stk', hvv, hCx, hvL, hFS, hCc⟩ := hIn
  subst hCc
  exact ⟨res, Stk', hr', hps, hvv, hret, hCx, hvL, hFS, by omega, by omega, by omega⟩

abbrev cellsF (root n sp it v start cnt : Nat) : List Cell :=
  [ci root, ci n, ci sp, ci it, ci v, ci start, ci cnt]

set_option maxHeartbeats 16000000 in
/-- The update of the farthest vertex after the arcs of `v` were looked at. -/
theorem far_exec (mv : MV) (hnv : mv.nv = 7) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = i32)
    (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int) (C : Ctx H T Cs n root Cb st Stk)
    (P : List Cell) (sp it v start cnt F : Nat) (hn : n < M31) (hv : v ∈ st.L) (hF : F < n)
    (hFS : Stk.getD n 0 = (F : Int)) (hsp : sp ≤ n) (fu : Nat) :
    ∃ (r : PRM) (Stk' : List Int), pexecM mv fu (Zfar mv.nv) (gS P (cellsF root n sp it v start cnt))
        (VR H T Cs st.par st.dep st.cd Stk) = some r ∧ r.ret = none ∧
      (∃ cs : List Cell, r.ps = gS P (cellsF root n sp it v start cnt ++ cs)) ∧
      r.vv = VR H T Cs st.par st.dep st.cd Stk' ∧
      Stk' = (if st.cd.getD F 0 < st.cd.getD v 0 then Stk.set n (v : Int) else Stk) ∧
      r.cost ≤ 200 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  have hvn : v < n := C.B.Llt v hv
  have hlC := C.B.lenC
  have hSk : Stk.length = n + 1 := C.stk.1
  have hvM : v < M31 := Nat.lt_trans hvn hn
  have hFM : F < M31 := Nat.lt_trans hF hn
  have hnl : n < Stk.length := by omega
  have memC : ∀ j, j < n → s64.valid (st.cd.getD j 0) = true := by
    intro j hj
    exact C.vc _ (getD_mem _ _ (by omega))
  -- dv = cost_depth[v]
  have E4 := envs mv P (cellsF root n sp it v start cnt) 4 (ci v) rfl (i32v v hvM)
  have r1 := rdM_val mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P (cellsF root n sp it v start cnt))) 5 (by omega) s64
    ty5.symm (ix mv.nv 4) rfl rfl v (cidx_den _ (mv.nv + 4) v E4 hvM) (st.cd.getD v 0)
    (by rw [VR_get5]; exact vec_getI st.cd v (by omega)) (by rw [ty5]; exact memC v hvn)
  have d1 := gSM_decl mv P (cellsF root n sp it v start cnt) (VR H T Cs st.par st.dep st.cd Stk) s64 _ _ _ r1
    (conv_signed s64 rfl rfl _ (memC v hvn))
  have q1 := (pexecM_prim mv fu (dDV mv.nv) _ _).trans d1
  -- f = stk[n]
  have E1 := envs mv P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)]) 1 (ci n) rfl (i32v n hn)
  have r2 := rdM_val mv (VR H T Cs st.par st.dep st.cd Stk)
    (penvN mv.nv (gS P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)]))) 6 (by omega) i32 ty6.symm (ix mv.nv 1) rfl rfl n
    (cidx_den _ (mv.nv + 1) n E1 hn) (F : Int) (by rw [VR_get6, ← hFS]; exact vec_getI Stk n hnl)
    (by rw [ty6]; exact i32v F hFM)
  have d2 := gSM_decl mv P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)]) (VR H T Cs st.par st.dep st.cd Stk) i32 _ _ _ r2
    (conv_signed i32 rfl rfl _ (i32v F hFM))
  have q2 := (pexecM_prim mv fu (dFF mv.nv) _ _).trans d2
  -- mx = cost_depth[f]
  have E8 := envs mv P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F]) 8 (ci F) rfl (i32v F hFM)
  have r3 := rdM_val mv (VR H T Cs st.par st.dep st.cd Stk)
    (penvN mv.nv (gS P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F]))) 5 (by omega) s64 ty5.symm (ix mv.nv 8)
    rfl rfl F (cidx_den _ (mv.nv + 8) F E8 hFM) (st.cd.getD F 0) (by rw [VR_get5]; exact vec_getI st.cd F (by omega))
    (by rw [ty5]; exact memC F hF)
  have d3 := gSM_decl mv P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F]) (VR H T Cs st.par st.dep st.cd Stk)
    s64 _ _ _ r3 (conv_signed s64 rfl rfl _ (memC F hF))
  have q3 := (pexecM_prim mv fu (dMX mv.nv) _ _).trans d3
  -- the comparison
  have e7 := gSM_env mv.nv P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)]) 7
    (cs (st.cd.getD v 0)) rfl (memC v hvn)
  have e9 := gSM_env mv.nv P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)]) 9
    (cs (st.cd.getD F 0)) rfl (memC F hF)
  have hcond : vdenM mv (VR H T Cs st.par st.dep st.cd Stk)
      (penvN mv.nv (gS P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)])))
      (cMX mv.nv) = some (if st.cd.getD F 0 < st.cd.getD v 0 then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e9, Option.bind_some, den_variable, e7, Option.bind_some, lt_conv]
  by_cases hlt : st.cd.getD F 0 < st.cd.getD v 0
  · rw [if_pos hlt] at hcond
    have hidx : vdenM mv (VR H T Cs st.par st.dep st.cd Stk)
        (penvN mv.nv (gS P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)])))
        (ix mv.nv 1) = some (n : Int) := by
      have e1 := gSM_env mv.nv P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)]) 1
        (ci n) rfl (i32v n hn)
      rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 1) n e1 hn
    have hx : vdenM mv (VR H T Cs st.par st.dep st.cd Stk)
        (penvN mv.nv (gS P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)])))
        (.variable i32 (mv.nv + 4)) = some (v : Int) := by
      have e4 := gSM_env mv.nv P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)]) 4
        (ci v) rfl (i32v v hvM)
      rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e4
    have w1 := pstmtM_write_ok mv (gS P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)]))
      (VR H T Cs st.par st.dep st.cd Stk) 6 (by omega) (ix mv.nv 1) (.variable i32 (mv.nv + 4)) (v : Int) n hx hidx
      (by rw [VR_get6]; exact hnl) (by rw [ty6]; exact i32v v hvM)
    rw [ty6, VR_get6, VR_set6] at w1
    have a1 := (pexecM_prim mv fu (wFar mv.nv) _ _).trans w1
    have a2 := seqM_some a1 rfl (pexecM_skip mv fu _ _)
    have a3 := pexecM_scope mv fu _ _ _ _ a2
    have tk := gS_takeC P (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)])
      (cellsF root n sp it v start cnt ++ [cs (st.cd.getD v 0)] ++ [ci F] ++ [cs (st.cd.getD F 0)]) [] rfl
    simp only [List.append_nil] at tk
    simp only [tk] at a3
    have a4 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu (cMX mv.nv) (Yfar mv.nv) Sk _ _ 1 hcond (by decide) _ a4
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q3 rfl b2
    have b4 := seqM_some q2 rfl b3
    have b5 := seqM_some q1 rfl b4
    refine ⟨_, Stk.set n (v : Int), b5, rfl, ⟨[cs (st.cd.getD v 0), ci F, cs (st.cd.getD F 0)], rfl⟩, rfl, by rw [if_pos hlt], ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  · rw [if_neg hlt] at hcond
    have b1 := pexecM_branch_false mv fu (cMX mv.nv) (Yfar mv.nv) Sk _ _ hcond _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q3 rfl b2
    have b4 := seqM_some q2 rfl b3
    have b5 := seqM_some q1 rfl b4
    refine ⟨_, Stk, b5, rfl, ⟨[cs (st.cd.getD v 0), ci F, cs (st.cd.getD F 0)], rfl⟩, rfl, by rw [if_neg hlt], ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp

theorem gt_conv (x y : Int) : bT.convert (binaryValue .gt x y) = some (if x > y then 1 else 0) := by
  by_cases h : x > y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem ctx_pop (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int)
    (C : Ctx H T Cs n root Cb st Stk) : Ctx H T Cs n root Cb { st with S := st.S.dropLast } Stk := by
  refine ⟨C.B.pop, ⟨C.stk.1, ?_⟩, C.vp, C.vd, C.vc, C.vs⟩
  intro i hi
  rcases List.eq_nil_or_concat st.S with h | ⟨S0, b, h0'⟩
  · have : (st.S.dropLast).length = 0 := by rw [h]; rfl
    have : i < 0 := by have h2 : ({ st with S := st.S.dropLast } : St).S.length = (st.S.dropLast).length := rfl
                       omega
    omega
  · have h : st.S = S0 ++ [b] := by rw [h0']; simp
    have hdl : st.S.dropLast = S0 := by rw [h]; simp
    have hi' : i < S0.length := by
      have h2 : ({ st with S := st.S.dropLast } : St).S.length = S0.length := by
        show st.S.dropLast.length = S0.length; rw [hdl]
      omega
    have := C.stk.2 i (by rw [h]; simp; omega)
    show Stk.getD i 0 = ((st.S.dropLast.getD i 0 : Nat) : Int)
    rw [hdl, this, h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi']

/-- The sum of the out-degrees of a list of vertices. -/
def Dsum (H : List Nat) (D : List Nat) : Nat := (D.map (fun x => H.getD (x + 1) 0 - H.getD x 0)).sum

theorem ctx_set_far (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int)
    (C : Ctx H T Cs n root Cb st Stk) (v : Nat) (hv : v < M31) :
    Ctx H T Cs n root Cb st (Stk.set n (v : Int)) := by
  have hSn := C.B.S_len
  refine ⟨C.B, ⟨by simp [C.stk.1], ?_⟩, C.vp, C.vd, C.vc, V32_set _ _ _ C.vs (i32v v hv)⟩
  intro i hi
  have hne : i ≠ n := by omega
  rw [Proofs.TreeRootMath.getD_set_ne Stk n i _ hne]
  exact C.stk.2 i hi

set_option maxHeartbeats 16000000 in
/-- The body of the main loop: `if (sp > 0) { sp--; int v = stk[sp]; ...; for (...) {...} }`. -/
theorem b3_body (mv : MV) (hnv : mv.nv = 7) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = s64)
    (ty3 : mv.ty 3 = i32) (ty4 : mv.ty 4 = i32) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = i32)
    (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st : St) (Stk : List Int) (D : List Nat)
    (C : Ctx H T Cs n root Cb st Stk) (I : Proofs.TreeRootMath.Inv H T Cs n root Cb st) (HK : HeadOK H T n)
    (P : List Cell) (it : Nat) (hn : n < M31) (hroot : root < n) (hit : it < M31)
    (hm2 : T.length < 2147483647) (hCl : Cs.length = T.length)
    (hTn : ∀ q, T.getD q 0 < n) (hCb : ∀ q, (Cs.getD q 0).natAbs ≤ Cb)
    (hCbn : n * Cb < 9223372036854775808) (F : Nat) (G2 : Proofs.TreeRootMath.GInv2 st D F) (hFn : F < n)
    (hFS : Stk.getD n 0 = (F : Int)) (fu : Nat) (hfu : T.length + 2 ≤ fu) :
    ∃ (r : PRM) (Stk' : List Int), pexecM mv fu (B3 mv.nv) (gS P [ci root, ci n, ci st.S.length, ci it])
        (VR H T Cs st.par st.dep st.cd Stk) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci root, ci n, ci (Proofs.TreeRootMath.step H T Cs st).S.length, ci it] ∧
      r.vv = VR H T Cs (Proofs.TreeRootMath.step H T Cs st).par (Proofs.TreeRootMath.step H T Cs st).dep
        (Proofs.TreeRootMath.step H T Cs st).cd Stk' ∧
      Ctx H T Cs n root Cb (Proofs.TreeRootMath.step H T Cs st) Stk' ∧
      Stk'.getD n 0 = ((Proofs.TreeRootMath.stepF st F : Nat) : Int) ∧ Proofs.TreeRootMath.stepF st F < n ∧
      r.cost + 820 * Dsum H D ≤ 700 + 820 * Dsum H (Proofs.TreeRootMath.stepD st D) ∧ r.need ≤ P.length + 100 ∧
      r.wk + 4 * Dsum H D ≤ 4 * Dsum H (Proofs.TreeRootMath.stepD st D) + 1 ∧
      Dsum H D ≤ Dsum H (Proofs.TreeRootMath.stepD st D) := by
  have hnM : n < 2147483648 := hn
  have hSn := C.B.S_len
  have hmM : T.length < M31 := by show T.length < 2147483648; omega
  have E2 := envs mv P [ci root, ci n, ci st.S.length, ci it] 2 (ci st.S.length) rfl (i32v _ (by omega))
  have vc : vdenM mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P [ci root, ci n, ci st.S.length, ci it]))
      (c3 mv.nv) = some (if (st.S.length : Int) > 0 then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E2, Option.bind_some, zero_den, Option.bind_some]
    exact gt_conv _ _
  obtain ⟨hI', h1, h2, h3⟩ := Proofs.TreeRootMath.step_inv H T Cs n root Cb hTn hCb st I
  by_cases hS : st.S = []
  · have hsp0 : st.S.length = 0 := by rw [hS]; rfl
    rw [if_neg (by omega)] at vc
    have hst : Proofs.TreeRootMath.step H T Cs st = st := h1 hS
    have hD : Proofs.TreeRootMath.stepD st D = D := by unfold Proofs.TreeRootMath.stepD; rw [hS]; rfl
    have hFF : Proofs.TreeRootMath.stepF st F = F := by unfold Proofs.TreeRootMath.stepF; rw [hS]; rfl
    have b1 := pexecM_branch_false mv fu (c3 mv.nv) (.sequence (.scope (Z3 mv.nv)) Sk) Sk _ _ vc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, Stk, b2, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hst]
    · rw [hst]
    · rw [hst]; exact C
    · rw [hFF]; exact hFS
    · rw [hFF]; exact hFn
    · rw [hD]; simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    · rw [hD]; simp
    · rw [hD]
  · rw [if_pos (by have : 0 < st.S.length := List.length_pos_iff.mpr hS; omega)] at vc
    obtain ⟨v, S0, ext, hS0, hL, hSx, hst, hcdp⟩ := h3 hS
    have hSlen : st.S.length = S0.length + 1 := by rw [hS0]; simp
    have hvS : v ∈ st.S := by rw [hS0]; simp
    have hvL : v ∈ st.L := I.B.Ssub v hvS
    have hvn : v < n := I.B.Llt v hvL
    have hDS : Proofs.TreeRootMath.stepD st D = D ++ [v] := by
      unfold Proofs.TreeRootMath.stepD; rw [hS0]; simp
    have hHle : ∀ j, j ≤ n → H.getD j 0 ≤ T.length := by
      intro j hj
      have := HeadOK.le H T n HK n (Nat.le_refl _) j hj
      rw [HK.last] at this
      exact this
    have hmono := HK.mono v hvn
    have hcntEq : (Proofs.TreeRootMath.arcs H v).length = H.getD (v + 1) 0 - H.getD v 0 := arcs_length H v
    have hb1 := hHle (v + 1) (by omega)
    have hb0 := hHle v (by omega)
    have hHl : H.length = n + 1 := HK.len
    -- sp = sp - 1
    have hx0 : vdenM mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P [ci root, ci n, ci st.S.length, ci it]))
        (.binary i32 .sub (.variable i32 (mv.nv + 2)) lit1) = some ((st.S.length - 1 : Nat) : Int) := by
      rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E2, Option.bind_some, one_den, Option.bind_some]
      have : binaryValue .sub (st.S.length : Int) 1 = ((st.S.length - 1 : Nat) : Int) := by
        show (st.S.length : Int) - 1 = _; omega
      rw [this]
      exact conv_signed i32 rfl rfl _ (i32v _ (by omega))
    have as := gSM_assign mv P [ci root, ci n, ci st.S.length, ci it] (VR H T Cs st.par st.dep st.cd Stk) 2 (by simp) i32 _ _ _
      hx0 (ci st.S.length) rfl rfl (i32v _ (by omega)) (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
    have q0 := (pexecM_prim mv fu (dec2 mv.nv) _ _).trans as
    -- int v = stk[sp]
    have E2' := envs mv P [ci root, ci n, ci (st.S.length - 1), ci it] 2 (ci (st.S.length - 1)) rfl (i32v _ (by omega))
    have hStkv : Stk.getD (st.S.length - 1) 0 = (v : Int) := by
      have h' := C.stk.2 (st.S.length - 1) (by omega)
      have e : st.S.getD (st.S.length - 1) 0 = v := by
        have hk : st.S.length - 1 = S0.length := by omega
        rw [hk, hS0, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp
      rw [h', e]
    have vv1 := rdM_val mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P [ci root, ci n, ci (st.S.length - 1), ci it]))
      6 (by omega) i32 ty6.symm (ix mv.nv 2) rfl rfl (st.S.length - 1) (cidx_den _ (mv.nv + 2) _ E2' (by omega)) (v : Int)
      (by rw [VR_get6, ← hStkv]; exact vec_getI Stk _ (by rw [C.stk.1]; omega)) (by rw [ty6]; exact i32v v (by omega))
    have d1 := gSM_decl mv P [ci root, ci n, ci (st.S.length - 1), ci it] (VR H T Cs st.par st.dep st.cd Stk) i32 _ _ _ vv1
      (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
    have q1 := (pexecM_prim mv fu (dV mv.nv) _ _).trans d1
    -- int start = head[v]
    have E4 := envs mv P [ci root, ci n, ci (st.S.length - 1), ci it, ci v] 4 (ci v) rfl (i32v _ (by omega))
    have vs := rdM_val mv (VR H T Cs st.par st.dep st.cd Stk) (penvN mv.nv (gS P [ci root, ci n, ci (st.S.length - 1), ci it, ci v]))
      0 (by omega) i32 ty0.symm (ix mv.nv 4) rfl rfl v (cidx_den _ (mv.nv + 4) _ E4 (by omega)) ((H.getD v 0 : Nat) : Int)
      (by rw [VR_get0]; exact vec_getM H v (by omega)) (by rw [ty0]; exact i32v _ (by omega))
    have d2 := gSM_decl mv P [ci root, ci n, ci (st.S.length - 1), ci it, ci v] (VR H T Cs st.par st.dep st.cd Stk) i32 _ _ _ vs
      (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
    have q2 := (pexecM_prim mv fu (dS mv.nv) _ _).trans d2
    -- int cnt = head[v + 1] - start
    have E4' := envs mv P [ci root, ci n, ci (st.S.length - 1), ci it, ci v, ci (H.getD v 0)] 4 (ci v) rfl (i32v _ (by omega))
    have E5 := envs mv P [ci root, ci n, ci (st.S.length - 1), ci it, ci v, ci (H.getD v 0)] 5 (ci (H.getD v 0)) rfl
      (i32v _ (by omega))
    have vh1 := rdM_val mv (VR H T Cs st.par st.dep st.cd Stk)
      (penvN mv.nv (gS P [ci root, ci n, ci (st.S.length - 1), ci it, ci v, ci (H.getD v 0)])) 0 (by omega) i32 ty0.symm
      (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 4)) lit1)) rfl rfl (v + 1)
      (succIdx_den _ (mv.nv + 4) v E4' (by omega)) ((H.getD (v + 1) 0 : Nat) : Int)
      (by rw [VR_get0]; exact vec_getM H _ (by omega)) (by rw [ty0]; exact i32v _ (by omega))
    have vcnt : vdenM mv (VR H T Cs st.par st.dep st.cd Stk)
        (penvN mv.nv (gS P [ci root, ci n, ci (st.S.length - 1), ci it, ci v, ci (H.getD v 0)]))
        (.binary i32 .sub (.read i32 (.local 0) (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 4)) lit1)))
          (.variable i32 (mv.nv + 5))) = some ((H.getD (v + 1) 0 - H.getD v 0 : Nat) : Int) := by
      rw [vdenM_binary _ _ _ _ _ _ _ rfl, vh1, Option.bind_some, vdenM_scalar _ _ _ _ rfl, den_variable, E5, Option.bind_some]
      have : binaryValue .sub ((H.getD (v + 1) 0 : Nat) : Int) ((H.getD v 0 : Nat) : Int) =
          ((H.getD (v + 1) 0 - H.getD v 0 : Nat) : Int) := by
        show _ - _ = _; omega
      rw [this]
      exact conv_signed i32 rfl rfl _ (i32v _ (by omega))
    have d3 := gSM_decl mv P [ci root, ci n, ci (st.S.length - 1), ci it, ci v, ci (H.getD v 0)]
      (VR H T Cs st.par st.dep st.cd Stk) i32 _ _ _ vcnt (conv_signed i32 rfl rfl _ (i32v _ (by omega)))
    have q3 := (pexecM_prim mv fu (dC mv.nv) _ _).trans d3
    rw [← hcntEq] at q3
    -- the inner loop
    have hlen1 : ({ st with S := st.S.dropLast } : St).S.length = st.S.length - 1 := by
      show st.S.dropLast.length = _; simp
    have Cpop := ctx_pop H T Cs n root Cb st Stk C
    have hvL1 : v ∈ ({ st with S := st.S.dropLast } : St).L := hvL
    obtain ⟨rf, Stk', hrf, hrfps, hrfvv, hrfret, hrfC, hrfvL, hrfFS, hrfc, hrfn, hrfw⟩ := xin_loop mv hnv ty1 ty2 ty3 ty4 ty5 ty6 H T Cs n root Cb
      { st with S := st.S.dropLast } Stk Cpop P it v (H.getD v 0) (Proofs.TreeRootMath.arcs H v).length hn hroot hit hvL1 rfl rfl
      (by omega) hmM (by omega) hCl hTn hCb hCbn fu (by omega)
    rw [hlen1] at hrf
    have hfull : foldA T Cs H v (Proofs.TreeRootMath.arcs H v).length { st with S := st.S.dropLast } =
        Proofs.TreeRootMath.step H T Cs st := by
      rw [foldA_full, hst]; rfl
    rw [hfull] at hrfps hrfvv hrfC hrfvL
    have hFL : F ∈ st.L := G2.Fin
    have hFS' : Stk'.getD n 0 = (F : Int) := by
      have : ({ st with S := st.S.dropLast } : St).S.length ≤ n := hrfC.B.S_len.trans (Nat.le_refl _) |> fun h => by
        have := Cpop.B.S_len; exact this
      rw [hrfFS]; exact hFS
    have hspn : (Proofs.TreeRootMath.step H T Cs st).S.length ≤ n := hrfC.B.S_len
    obtain ⟨rg, Stk'', hrg, hretg, ⟨csx, hrgps⟩, hrgvv, hStk'', hcg, hng, hwg⟩ := far_exec mv hnv ty5 ty6 H T Cs n root Cb
      (Proofs.TreeRootMath.step H T Cs st) Stk' hrfC P (Proofs.TreeRootMath.step H T Cs st).S.length it v (H.getD v 0)
      (Proofs.TreeRootMath.arcs H v).length F hn hrfvL hFn hFS' hspn fu
    have hFcd : (Proofs.TreeRootMath.step H T Cs st).cd.getD F 0 = st.cd.getD F 0 := hcdp F hFL
    have hvcd : (Proofs.TreeRootMath.step H T Cs st).cd.getD v 0 = st.cd.getD v 0 := hcdp v hvL
    have hnl : n < Stk'.length := by have := hrfC.stk.1; omega
    have hStkF : Stk''.getD n 0 = ((Proofs.TreeRootMath.stepF st F : Nat) : Int) := by
      have hg : st.S.getLast? = some v := by rw [hS0]; simp
      unfold Proofs.TreeRootMath.stepF
      rw [hg, hStk'', hFcd, hvcd]
      show _ = (((if st.cd.getD F 0 < st.cd.getD v 0 then v else F : Nat)) : Int)
      by_cases hlt : st.cd.getD F 0 < st.cd.getD v 0
      · rw [if_pos hlt, if_pos hlt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; rfl
      · rw [if_neg hlt, if_neg hlt]; exact hFS'
    have hCtx'' : Ctx H T Cs n root Cb (Proofs.TreeRootMath.step H T Cs st) Stk'' := by
      rw [hStk'']
      by_cases hlt : (Proofs.TreeRootMath.step H T Cs st).cd.getD F 0 < (Proofs.TreeRootMath.step H T Cs st).cd.getD v 0
      · rw [if_pos hlt]; exact ctx_set_far H T Cs n root Cb _ Stk' hrfC v (Nat.lt_trans (hrfC.B.Llt v hrfvL) hn)
      · rw [if_neg hlt]; exact hrfC
    have hFlt : Proofs.TreeRootMath.stepF st F < n := by
      have hg : st.S.getLast? = some v := by rw [hS0]; simp
      unfold Proofs.TreeRootMath.stepF
      rw [hg]
      show (if st.cd.getD F 0 < st.cd.getD v 0 then v else F) < n
      by_cases hlt : st.cd.getD F 0 < st.cd.getD v 0
      · rw [if_pos hlt]; exact I.B.Llt v hvL
      · rw [if_neg hlt]; exact hFn
    have f1 := seqM_some hrf hrfret (by rw [hrfps, hrfvv]; exact hrg)
    have f2 := seqM_some q3 rfl f1
    have f3 := seqM_some q2 rfl f2
    have f4 := seqM_some q1 rfl f3
    have f5 := seqM_some q0 rfl f4
    have f6 := pexecM_scope mv fu _ _ _ _ f5
    have tk := gS_takeC P [ci root, ci n, ci st.S.length, ci it]
      [ci root, ci n, ci (Proofs.TreeRootMath.step H T Cs st).S.length, ci it]
      ([ci v, ci (H.getD v 0), ci (Proofs.TreeRootMath.arcs H v).length] ++ csx) (by simp)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at tk
    have hpsg : rg.ps = gS P ([ci root, ci n, ci (Proofs.TreeRootMath.step H T Cs st).S.length, ci it] ++
        ([ci v, ci (H.getD v 0), ci (Proofs.TreeRootMath.arcs H v).length] ++ csx)) := by
      rw [hrgps]; rfl
    rw [hpsg] at f6
    simp only [List.append_assoc, List.cons_append, List.nil_append] at f6
    simp only [tk] at f6
    have f7 := seqM_some f6 (by simp [hretg]) (pexecM_skip mv fu _ _)
    have g1 := pexecM_branch_true mv fu (c3 mv.nv) (.sequence (.scope (Z3 mv.nv)) Sk) Sk _ _ 1 vc (by decide) _ f7
    have g2 := seqM_some g1 (by simp [hretg]) (pexecM_skip mv fu _ _)
    have hDsum : Dsum H (D ++ [v]) = Dsum H D + (Proofs.TreeRootMath.arcs H v).length := by
      unfold Dsum; rw [hcntEq]; simp
    refine ⟨_, Stk'', g2, ?_, rfl, ?_, hCtx'', hStkF, hFlt, ?_, ?_, ?_, ?_⟩
    · simp [hretg]
    · simp [hrgvv]
    · rw [hDS, hDsum]
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrfc hcg ⊢
      omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrfn hng ⊢
      omega
    · rw [hDS, hDsum]
      simp at hrfw hwg ⊢
      omega
    · rw [hDS, hDsum]; omega

theorem dsum_le (H T : List Nat) (n : Nat) (HK : HeadOK H T n) (D : List Nat) (hnd : D.Nodup) (hlt : ∀ x ∈ D, x < n) :
    Dsum H D ≤ T.length := by
  have h1 := Proofs.TreeRootMath.sum_nodup_le (fun x => H.getD (x + 1) 0 - H.getD x 0) n D hnd hlt
  have h2 := Proofs.TreeRootMath.sum_outdeg H n HK.mono
  have h3 := HK.last
  have h4 := HK.zero
  unfold Dsum
  omega

/-- The ghost of the main loop: the abstract state, the stack vector and the popped vertices. -/
structure OG where
  st : St
  Stk : List Int
  D : List Nat
  F : Nat

set_option maxHeartbeats 16000000 in
/-- The main loop `for (int it = 0; it < n; it++) {...}`. -/
theorem l3_loop (mv : MV) (hnv : mv.nv = 7) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = s64)
    (ty3 : mv.ty 3 = i32) (ty4 : mv.ty 4 = i32) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = i32)
    (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (st0 : St) (Stk0 : List Int) (F0 : Nat)
    (C0 : Ctx H T Cs n root Cb st0 Stk0) (I0 : Proofs.TreeRootMath.Inv H T Cs n root Cb st0)
    (G0 : Proofs.TreeRootMath.GInv2 st0 [] F0) (hF0 : Stk0.getD n 0 = (F0 : Int)) (hF0n : F0 < n) (HK : HeadOK H T n)
    (P : List Cell) (hn : n < M31) (hroot : root < n) (hn2 : n < 2147483647) (hm2 : T.length < 2147483647)
    (hCl : Cs.length = T.length) (hTn : ∀ q, T.getD q 0 < n) (hCb : ∀ q, (Cs.getD q 0).natAbs ≤ Cb)
    (hCbn : n * Cb < 9223372036854775808) (fu : Nat) (hfu : T.length + 2 + n + 1 ≤ fu) :
    ∃ (res : PRM) (g2 : OG), pexecM mv fu (forStmtB mv.nv 3 1 (B3 mv.nv)) (gS P [ci root, ci n, ci st0.S.length])
        (VR H T Cs st0.par st0.dep st0.cd Stk0) = some res ∧
      res.ps = gS P [ci root, ci n, ci g2.st.S.length] ∧ g2.st = Proofs.TreeRootMath.runL H T Cs n st0 ∧
      res.vv = VR H T Cs g2.st.par g2.st.dep g2.st.cd g2.Stk ∧ res.ret = none ∧
      Ctx H T Cs n root Cb g2.st g2.Stk ∧ Proofs.TreeRootMath.Inv H T Cs n root Cb g2.st ∧
      Proofs.TreeRootMath.GInv2 g2.st g2.D g2.F ∧ g2.Stk.getD n 0 = (g2.F : Int) ∧ g2.F < n ∧
      res.cost ≤ 720 * n + 30 + 820 * T.length ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ 4 * T.length + n := by
  have hnM : n < 2147483648 := hn
  obtain ⟨res, C2, g2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runG mv P 3 1 n (by omega) hn2 (B3 mv.nv)
    (fun t vv Cc (g : OG) => g.st = Proofs.TreeRootMath.runL H T Cs t st0 ∧
      vv = VR H T Cs g.st.par g.st.dep g.st.cd g.Stk ∧ Cc = [ci root, ci n, ci g.st.S.length] ∧
      Ctx H T Cs n root Cb g.st g.Stk ∧ Proofs.TreeRootMath.Inv H T Cs n root Cb g.st ∧
      Proofs.TreeRootMath.GInv2 g.st g.D g.F ∧ g.Stk.getD n 0 = (g.F : Int) ∧ g.F < n)
    (fun g => 820 * (T.length - Dsum H g.D)) (fun g => 4 * (T.length - Dsum H g.D)) 700 100 1 (T.length + 2) (by omega)
    (by
      intro t vv Cc g fu ht hCl' hC1 ⟨hg, hvv, hCc, hCx, hIv, hGI, hFS, hFn⟩ hfu'
      subst hvv; subst hCc
      obtain ⟨r, Stk', hr, hret, hps, hvv, hC', hSF, hFlt, hcost, hneed, hwk, hmono⟩ := b3_body mv hnv ty0 ty1 ty2 ty3 ty4 ty5 ty6 H T Cs n root Cb
        g.st g.Stk g.D hCx hIv HK P t hn hroot (by omega) hm2 hCl hTn hCb hCbn g.F hGI hFn hFS fu hfu'
      have hG' := Proofs.TreeRootMath.ginv2_step H T Cs n root Cb hTn hCb g.st g.D g.F hIv hGI
      have hI' := (Proofs.TreeRootMath.step_inv H T Cs n root Cb hTn hCb g.st hIv).1
      have hbd := dsum_le H T n HK _ hG'.g.nd (fun x hx => hI'.B.Llt x (hG'.g.inL x hx))
      refine ⟨r, [], [ci root, ci n, ci (Proofs.TreeRootMath.step H T Cs g.st).S.length],
        ⟨Proofs.TreeRootMath.step H T Cs g.st, Stk', Proofs.TreeRootMath.stepD g.st g.D,
          Proofs.TreeRootMath.stepF g.st g.F⟩, hr, hret, hps, rfl, rfl,
        ⟨?_, hvv, rfl, hC', hI', hG', hSF, hFlt⟩, ?_, hneed, ?_⟩
      · show Proofs.TreeRootMath.step H T Cs g.st = Proofs.TreeRootMath.runL H T Cs (t + 1) st0
        rw [Proofs.TreeRootMath.runL_succ, ← hg]
      · show r.cost + 820 * (T.length - Dsum H (Proofs.TreeRootMath.stepD g.st g.D)) ≤ 700 + 820 * (T.length - Dsum H g.D)
        omega
      · show r.wk + 4 * (T.length - Dsum H (Proofs.TreeRootMath.stepD g.st g.D)) ≤ 1 + 4 * (T.length - Dsum H g.D)
        omega)
    (VR H T Cs st0.par st0.dep st0.cd Stk0) [ci root, ci n, ci st0.S.length] ⟨st0, Stk0, [], F0⟩ rfl rfl
    ⟨by simp [Proofs.TreeRootMath.runL], rfl, rfl, C0, I0, G0, hF0, hF0n⟩ fu (by omega)
  obtain ⟨hg, hvv, hCc, hCx, hIv, hGI, hFS, hFn⟩ := hIn
  have hD0 : Dsum H ([] : List Nat) = 0 := rfl
  refine ⟨res, g2, hr', ?_, hg, hvv, hret, hCx, hIv, hGI, hFS, hFn, ?_, ?_, ?_⟩
  · rw [hps, hCc]
  · show res.cost ≤ _
    have : (T.length - Dsum H ([] : List Nat)) = T.length := by rw [hD0]; rfl
    simp only [this] at hc
    omega
  · omega
  · have : (T.length - Dsum H ([] : List Nat)) = T.length := by rw [hD0]; rfl
    simp only [this] at hw
    omega

set_option maxHeartbeats 16000000 in
/-- The whole body of `tree_root`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 7) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = s64)
    (ty3 : mv.ty 3 = i32) (ty4 : mv.ty 4 = i32) (ty5 : mv.ty 5 = s64) (ty6 : mv.ty 6 = i32)
    (H T : List Nat) (Cs par dep cd Stk : List Int) (n root Cb : Nat) (HK : HeadOK H T n)
    (P : List Cell) (hn : n < M31) (hroot : root < n) (hn2 : n < 2147483647) (hm2 : T.length < 2147483647)
    (hCl : Cs.length = T.length) (hTn : ∀ q, T.getD q 0 < n) (hCb : ∀ q, (Cs.getD q 0).natAbs ≤ Cb)
    (hCbn : n * Cb < 9223372036854775808)
    (hP : par.length = n) (hD : dep.length = n) (hCd : cd.length = n) (hS : Stk.length = n + 1)
    (hneg : ∀ v, v < n → par.getD v 0 < 0) (vp : V32 par) (vd : V32 dep) (vc : V64 cd) (vs : V32 Stk)
    (fu : Nat) (hfu : T.length + 2 + n + 1 ≤ fu) :
    ∃ (r : PRM) (g2 : OG), pexecM mv fu (bodyTR mv.nv) (gS P [ci root, ci n]) (VR H T Cs par dep cd Stk) = some r ∧
      r.ret = none ∧ r.ps = gS P [ci root, ci n, ci g2.st.S.length] ∧
      g2.st = Proofs.TreeRootMath.runL H T Cs n (Proofs.TreeRootMath.initSt par dep cd root) ∧
      r.vv = VR H T Cs g2.st.par g2.st.dep g2.st.cd g2.Stk ∧
      Ctx H T Cs n root Cb g2.st g2.Stk ∧ Proofs.TreeRootMath.Inv H T Cs n root Cb g2.st ∧
      Proofs.TreeRootMath.GInv2 g2.st g2.D g2.F ∧ g2.Stk.getD n 0 = (g2.F : Int) ∧ g2.F < n ∧
      r.cost ≤ 720 * n + 820 * T.length + 300 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 * T.length + n + 5 := by
  have hnM : n < 2147483648 := hn
  have E0 := envs mv P [ci root, ci n] 0 (ci root) rfl (i32v root (by omega))
  have hidx0 : vdenM mv (VR H T Cs par dep cd Stk) (penvN mv.nv (gS P [ci root, ci n])) (ix mv.nv 0) = some (root : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 0) root E0 (by omega)
  have hx0 : vdenM mv (VR H T Cs par dep cd Stk) (penvN mv.nv (gS P [ci root, ci n])) (.variable i32 mv.nv) = some (root : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0
  -- parent[root] = root
  have w1 := pstmtM_write_ok mv (gS P [ci root, ci n]) (VR H T Cs par dep cd Stk) 3 (by omega) (ix mv.nv 0)
    (.variable i32 mv.nv) (root : Int) root hx0 hidx0 (by rw [VR_get3]; omega) (by rw [ty3]; exact i32v root (by omega))
  rw [ty3, VR_get3, VR_set3] at w1
  have a1 := (pexecM_prim mv fu (pP mv.nv) _ _).trans w1
  -- depth[root] = 0
  have hidx0' : vdenM mv (VR H T Cs (par.set root (root : Int)) dep cd Stk) (penvN mv.nv (gS P [ci root, ci n])) (ix mv.nv 0) =
      some (root : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 0) root E0 (by omega)
  have w2 := pstmtM_write_ok mv (gS P [ci root, ci n]) (VR H T Cs (par.set root (root : Int)) dep cd Stk) 4 (by omega)
    (ix mv.nv 0) lit0 0 root (zero_lit_val mv _ _) hidx0' (by rw [VR_get4]; omega) (by rw [ty4]; exact i32v 0 (by omega))
  rw [ty4, VR_get4, VR_set4] at w2
  have a2 := (pexecM_prim mv fu (pD mv.nv) _ _).trans w2
  -- cost_depth[root] = 0
  have hidx0'' : vdenM mv (VR H T Cs (par.set root (root : Int)) (dep.set root 0) cd Stk) (penvN mv.nv (gS P [ci root, ci n]))
      (ix mv.nv 0) = some (root : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 0) root E0 (by omega)
  have hz : vdenM mv (VR H T Cs (par.set root (root : Int)) (dep.set root 0) cd Stk) (penvN mv.nv (gS P [ci root, ci n]))
      (.cast s64 lit0) = some 0 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_cast, zero_den, Option.bind_some]
    exact conv_signed s64 rfl rfl 0 (s64_valid_of _ (by decide))
  have w3 := pstmtM_write_ok mv (gS P [ci root, ci n]) (VR H T Cs (par.set root (root : Int)) (dep.set root 0) cd Stk) 5
    (by omega) (ix mv.nv 0) (.cast s64 lit0) 0 root hz hidx0'' (by rw [VR_get5]; omega)
    (by rw [ty5]; exact s64_valid_of _ (by decide))
  rw [ty5, VR_get5, VR_set5] at w3
  have a3 := (pexecM_prim mv fu (pC mv.nv) _ _).trans w3
  -- stk[0] = root
  have hidxS : vdenM mv (VR H T Cs (par.set root (root : Int)) (dep.set root 0) (cd.set root 0) Stk)
      (penvN mv.nv (gS P [ci root, ci n])) (.cast u64 lit0) = some ((0 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_cast, zero_den, Option.bind_some, convert_u64]; rfl
  have hxS : vdenM mv (VR H T Cs (par.set root (root : Int)) (dep.set root 0) (cd.set root 0) Stk)
      (penvN mv.nv (gS P [ci root, ci n])) (.variable i32 mv.nv) = some (root : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0
  have w4 := pstmtM_write_ok mv (gS P [ci root, ci n]) (VR H T Cs (par.set root (root : Int)) (dep.set root 0) (cd.set root 0) Stk)
    6 (by omega) (.cast u64 lit0) (.variable i32 mv.nv) (root : Int) 0 hxS hidxS (by rw [VR_get6]; omega)
    (by rw [ty6]; exact i32v root (by omega))
  rw [ty6, VR_get6, VR_set6] at w4
  have a4 := (pexecM_prim mv fu (pS mv.nv) _ _).trans w4
  -- stk[n] = root
  have E1 := envs mv P [ci root, ci n] 1 (ci n) rfl (i32v n hn)
  have hidxF : vdenM mv (VR H T Cs (par.set root (root : Int)) (dep.set root 0) (cd.set root 0) (Stk.set 0 (root : Int)))
      (penvN mv.nv (gS P [ci root, ci n])) (ix mv.nv 1) = some (n : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 1) n E1 hn
  have hxF : vdenM mv (VR H T Cs (par.set root (root : Int)) (dep.set root 0) (cd.set root 0) (Stk.set 0 (root : Int)))
      (penvN mv.nv (gS P [ci root, ci n])) (.variable i32 mv.nv) = some (root : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E0
  have w5 := pstmtM_write_ok mv (gS P [ci root, ci n])
    (VR H T Cs (par.set root (root : Int)) (dep.set root 0) (cd.set root 0) (Stk.set 0 (root : Int))) 6 (by omega) (ix mv.nv 1)
    (.variable i32 mv.nv) (root : Int) n hxF hidxF (by rw [VR_get6]; simp [hS]) (by rw [ty6]; exact i32v root (by omega))
  rw [ty6, VR_get6, VR_set6] at w5
  have a4b := (pexecM_prim mv fu (pF mv.nv) _ _).trans w5
  -- int sp = 1
  have d5 := gSM_decl mv P [ci root, ci n] (VR H T Cs (par.set root (root : Int)) (dep.set root 0) (cd.set root 0)
    ((Stk.set 0 (root : Int)).set n (root : Int))) i32 lit1 1 1 (by rw [vdenM_scalar _ _ _ _ rfl]; exact one_den _)
    (conv_signed i32 rfl rfl _ (i32v 1 (by omega)))
  have a5 := (pexecM_prim mv fu (.declare i32 true lit1) _ _).trans d5
  -- the main loop
  have hroot0 : 0 < n := by omega
  have I0 := Proofs.TreeRootMath.initInv H T Cs n root Cb par dep cd hroot hP hD hCd hneg
  have C0 : Ctx H T Cs n root Cb (Proofs.TreeRootMath.initSt par dep cd root) ((Stk.set 0 (root : Int)).set n (root : Int)) := by
    refine ⟨I0.B, ⟨by simp [hS], ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by simpa [Proofs.TreeRootMath.initSt] using hi
      subst hi0
      rw [Proofs.TreeRootMath.getD_set_ne _ n 0 _ (by omega)]
      simp [Proofs.TreeRootMath.initSt, List.getD_eq_getElem?_getD, hS, hroot0]
    · exact V32_set _ _ _ vp (i32v root (by omega))
    · exact V32_set _ _ _ vd (i32_valid_of _ (by omega))
    · exact V64_set _ _ _ vc (s64_valid_of _ (by omega))
    · exact V32_set _ _ _ (V32_set _ _ _ vs (i32v root (by omega))) (i32v root (by omega))
  have hF0 : ((Stk.set 0 (root : Int)).set n (root : Int)).getD n 0 = (root : Int) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by simp [hS])]; rfl
  obtain ⟨rl, g2, hrl, hlps, hlst, hlvv, hlret, hlC, hlI, hlG, hlFS, hlFn, hlc, hln, hlw⟩ := l3_loop mv hnv ty0 ty1 ty2 ty3 ty4 ty5 ty6 H T Cs n root Cb
    (Proofs.TreeRootMath.initSt par dep cd root) ((Stk.set 0 (root : Int)).set n (root : Int)) root C0 I0
    (Proofs.TreeRootMath.ginv2_init par dep cd root) hF0 hroot HK P hn hroot hn2 hm2 hCl hTn hCb hCbn fu (by omega)
  have f1 := seqM_some hrl hlret (pexecM_skip mv fu _ _)
  have f2' := seqM_some a5 rfl f1
  have f2 := seqM_some a4b rfl f2'
  have f3 := seqM_some a4 rfl f2
  have f4 := seqM_some a3 rfl f3
  have f5 := seqM_some a2 rfl f4
  have f6 := seqM_some a1 rfl f5
  refine ⟨_, g2, f6, rfl, ?_, hlst, hlvv, hlC, hlI, hlG, hlFS, hlFn, ?_, ?_, ?_⟩
  · exact hlps
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hlc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hlps] at hln ⊢; omega
  · simp at hlw ⊢; omega

end Proofs.TreeRootExec
