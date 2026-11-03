import Proofs.ForLoopB
import Proofs.BellmanFordExec
import Proofs.TopoSortExec
import Proofs.Generated.TreeEdges

namespace Proofs.TreeEdgesExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 pexecM_branch_true pexecM_branch_false
  getD_mem cs s64_valid_of lt_conv ne_conv)
open Proofs.TopoSortExec (i32v)

/-! ### `tree_edges_from_parent` (nv = 3: parent, from, to).  Cells: 0 = n, 1 = m, 2 = i, 3 = p -/

abbrev ixc (nv c : Nat) : NExpr := .cast u64 (.variable i32 (nv + c))
abbrev dP (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 0) (ixc nv 2))
abbrev cNe (nv : Nat) : NExpr := .binary bT .ne (.variable i32 (nv + 3)) (.variable i32 (nv + 2))
abbrev cLe (nv : Nat) : NExpr := .binary bT .le (.literal i32 0) (.variable i32 (nv + 3))
abbrev cLt (nv : Nat) : NExpr := .binary bT .lt (.variable i32 (nv + 3)) (.variable i32 nv)
abbrev wf1 (nv : Nat) : NStmt := .write (.local 1) i32 (ixc nv 1) (.variable i32 (nv + 3))
abbrev wt1 (nv : Nat) : NStmt := .write (.local 2) i32 (ixc nv 1) (.variable i32 (nv + 2))
abbrev incM (nv : Nat) : NStmt := .assign (nv + 1) i32 (.binary i32 .add (.variable i32 (nv + 1)) (.literal i32 1))
abbrev wf2 (nv : Nat) : NStmt := .write (.local 1) i32 (ixc nv 1) (.variable i32 (nv + 2))
abbrev wt2 (nv : Nat) : NStmt := .write (.local 2) i32 (ixc nv 1) (.variable i32 (nv + 3))
abbrev Y3 (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (wf1 nv)) (.sequence (.primitive (wt1 nv)) (.sequence (.primitive (incM nv))
    (.sequence (.primitive (wf2 nv)) (.sequence (.primitive (wt2 nv)) (.sequence (.primitive (incM nv)) Sk))))))) Sk
abbrev Y2 (nv : Nat) : Command := .sequence (.scope (.sequence (.branch (cLt nv) (Y3 nv) Sk) Sk)) Sk
abbrev Y1 (nv : Nat) : Command := .sequence (.scope (.sequence (.branch (cLe nv) (Y2 nv) Sk) Sk)) Sk
abbrev Bi (nv : Nat) : Command := .sequence (.primitive (dP nv)) (.sequence (.branch (cNe nv) (Y1 nv) Sk) Sk)
abbrev bodyTE (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0)))
    (.sequence (forStmtB nv 2 0 (Bi nv)) (.sequence (.primitive (.ret (.variable i32 (nv + 1)))) Sk))

theorem body_eqTE : Proofs.TreeEdgesInstance.tree_edges_from_parent.body = bodyTE 3 := rfl

abbrev cz (x : Int) : Cell := ⟨i32, x⟩

/-- The contents of the vectors `parent`, `from`, `to`. -/
def VE (Pr F T : List Int) : Nat → List Int := fun k => if k = 0 then Pr else if k = 1 then F else if k = 2 then T else []

theorem VE_get0 (Pr F T : List Int) : VE Pr F T 0 = Pr := by simp [VE]
theorem VE_get1 (Pr F T : List Int) : VE Pr F T 1 = F := by simp [VE]
theorem VE_get2 (Pr F T : List Int) : VE Pr F T 2 = T := by simp [VE]
theorem VE_set1 (Pr F T x : List Int) : upd (VE Pr F T) 1 x = VE Pr x T := by
  funext k; unfold upd VE; split <;> simp_all
theorem VE_set2 (Pr F T x : List Int) : upd (VE Pr F T) 2 x = VE Pr F x := by
  funext k; unfold upd VE; split <;> simp_all

/-- The test of the original (`p != i`, `0 <= p`, `p < n`). -/
def Valid (p : Int) (i n : Nat) : Prop := p ≠ (i : Int) ∧ 0 ≤ p ∧ p < (n : Int)

instance (p : Int) (i n : Nat) : Decidable (Valid p i n) := by unfold Valid; infer_instance

/-- The indices below `t` that produce arcs. -/
def vidx (Pr : List Int) (n t : Nat) : List Nat := (List.range t).filter (fun i => decide (Valid (Pr.getD i 0) i n))

/-- The arcs produced by the first `t` indices. -/
def arcP (Pr : List Int) (n t : Nat) : List (Int × Int) :=
  (vidx Pr n t).flatMap (fun i => [(Pr.getD i 0, (i : Int)), ((i : Int), Pr.getD i 0)])

theorem arcP_succ (Pr : List Int) (n t : Nat) :
    arcP Pr n (t + 1) = arcP Pr n t ++ (if Valid (Pr.getD t 0) t n then [(Pr.getD t 0, (t : Int)), ((t : Int), Pr.getD t 0)] else []) := by
  unfold arcP vidx
  rw [List.range_succ, List.filter_append, List.flatMap_append]
  congr 1
  by_cases h : Valid (Pr.getD t 0) t n
  · rw [List.filter_cons_of_pos (by simpa using h), List.filter_nil, if_pos h]
    simp
  · rw [List.filter_cons_of_neg (by simpa using h), List.filter_nil, if_neg h]
    simp

theorem set_pad_int (A O : List Int) (L : Nat) (t : Int) (hA : A.length = L) (hL : L < O.length) :
    (A ++ O.drop L).set L t = (A ++ [t]) ++ O.drop (L + 1) := by
  have hd : O.drop L = O[L] :: O.drop (L + 1) := List.drop_eq_getElem_cons hL
  rw [List.set_append_right _ _ (by omega), hA, Nat.sub_self, hd, List.append_assoc]
  rfl

theorem pair_pad (A O : List Int) (m : Nat) (x y : Int) (hA : A.length = m) (hO : m + 1 < O.length) :
    ((A ++ O.drop m).set m x).set (m + 1) y = (A ++ [x, y]) ++ O.drop (m + 2) := by
  rw [set_pad_int A O m x hA (by omega), set_pad_int (A ++ [x]) O (m + 1) y (by simp [hA]) hO]
  simp [List.append_assoc]

theorem binary_add_val (a b : Int) : binaryValue .add a b = a + b := rfl

set_option maxHeartbeats 8000000 in
/-- The six statements appending the two arcs. -/
theorem y3_exec (mv : MV) (hnv : mv.nv = 3) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (Pr Fc Tc : List Int) (P : List Cell) (n m t : Nat) (p : Int) (hn : n < M31) (ht : t < n) (hFl : m + 1 < Fc.length)
    (hTl : m + 1 < Tc.length) (hm : m + 2 < M31) (hpv : i32.valid p = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Y3 mv.nv) (gS P [ci n, ci m, ci t, cz p]) (VE Pr Fc Tc) = some r ∧ r.ret = none ∧
      r.ps = gS P [ci n, ci (m + 2), ci t, cz p] ∧
      r.vv = VE Pr ((Fc.set m p).set (m + 1) (t : Int)) ((Tc.set m (t : Int)).set (m + 1) p) ∧
      r.cost ≤ 300 ∧ r.need ≤ P.length + 50 ∧ r.wk ≤ 4 := by
  have htM : t < M31 := Nat.lt_trans ht hn
  have hmM : m < M31 := Nat.lt_of_le_of_lt (Nat.le_add_right m 2) hm
  have hm1M : m + 1 < M31 := Nat.lt_of_le_of_lt (Nat.le_add_right (m + 1) 1) hm
  have htv : i32.valid (t : Int) = true := i32v t htM
  -- from[m] = p
  have E1 := envs mv P [ci n, ci m, ci t, cz p] 1 (ci m) rfl (i32v m hmM)
  have E2 := envs mv P [ci n, ci m, ci t, cz p] 2 (ci t) rfl htv
  have E3 := envs mv P [ci n, ci m, ci t, cz p] 3 (cz p) rfl hpv
  have hix : vdenM mv (VE Pr Fc Tc) (penvN mv.nv (gS P [ci n, ci m, ci t, cz p])) (ixc mv.nv 1) = some (m : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 1) m E1 hmM
  have hvp : vdenM mv (VE Pr Fc Tc) (penvN mv.nv (gS P [ci n, ci m, ci t, cz p])) (.variable i32 (mv.nv + 3)) = some p := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
  have hvt : vdenM mv (VE Pr Fc Tc) (penvN mv.nv (gS P [ci n, ci m, ci t, cz p])) (.variable i32 (mv.nv + 2)) = some (t : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2
  have w1 := pstmtM_write_ok mv (gS P [ci n, ci m, ci t, cz p]) (VE Pr Fc Tc) 1 (by omega) (ixc mv.nv 1) (.variable i32 (mv.nv + 3))
    p m hvp hix (by rw [VE_get1]; omega) (by rw [ty1]; exact hpv)
  rw [ty1, VE_get1, VE_set1] at w1
  have a1 := (pexecM_prim mv fu (wf1 mv.nv) _ _).trans w1
  -- to[m] = t
  have hix' : vdenM mv (VE Pr (Fc.set m p) Tc) (penvN mv.nv (gS P [ci n, ci m, ci t, cz p])) (ixc mv.nv 1) = some (m : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 1) m E1 hmM
  have hvt' : vdenM mv (VE Pr (Fc.set m p) Tc) (penvN mv.nv (gS P [ci n, ci m, ci t, cz p])) (.variable i32 (mv.nv + 2)) = some (t : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2
  have w2 := pstmtM_write_ok mv (gS P [ci n, ci m, ci t, cz p]) (VE Pr (Fc.set m p) Tc) 2 (by omega) (ixc mv.nv 1)
    (.variable i32 (mv.nv + 2)) (t : Int) m hvt' hix' (by rw [VE_get2]; omega) (by rw [ty2]; exact htv)
  rw [ty2, VE_get2, VE_set2] at w2
  have a2 := (pexecM_prim mv fu (wt1 mv.nv) _ _).trans w2
  -- m = m + 1
  have hxm : vdenM mv (VE Pr (Fc.set m p) (Tc.set m (t : Int))) (penvN mv.nv (gS P [ci n, ci m, ci t, cz p]))
      (.binary i32 .add (.variable i32 (mv.nv + 1)) (.literal i32 1)) = some ((m + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E1, Option.bind_some, den_literal,
      if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    have : binaryValue .add (m : Int) 1 = ((m + 1 : Nat) : Int) := by
      show (m : Int) + 1 = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ hm1M)
  have as1 := gSM_assign mv P [ci n, ci m, ci t, cz p] (VE Pr (Fc.set m p) (Tc.set m (t : Int))) 1 (by simp) i32 _ _ _ hxm (ci m)
    rfl rfl (i32v m hmM) (conv_signed i32 rfl rfl _ (i32v _ hm1M))
  have a3 := (pexecM_prim mv fu (incM mv.nv) _ _).trans as1
  have hset1 : [ci n, ci m, ci t, cz p].set 1 ⟨i32, ((m + 1 : Nat) : Int)⟩ = [ci n, ci (m + 1), ci t, cz p] := rfl
  rw [hset1] at a3
  -- from[m + 1] = t
  have E1' := envs mv P [ci n, ci (m + 1), ci t, cz p] 1 (ci (m + 1)) rfl (i32v _ hm1M)
  have E2' := envs mv P [ci n, ci (m + 1), ci t, cz p] 2 (ci t) rfl htv
  have E3' := envs mv P [ci n, ci (m + 1), ci t, cz p] 3 (cz p) rfl hpv
  have hix2 : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci n, ci (m + 1), ci t, cz p])) (ixc mv.nv 1) = some ((m + 1 : Nat) : Int) := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ (mv.nv + 1) (m + 1) E1' hm1M
  have hvt2 : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci n, ci (m + 1), ci t, cz p])) (.variable i32 (mv.nv + 2)) = some (t : Int) := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2'
  have hvp2 : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci n, ci (m + 1), ci t, cz p])) (.variable i32 (mv.nv + 3)) = some p := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3'
  have w3 := pstmtM_write_ok mv (gS P [ci n, ci (m + 1), ci t, cz p]) (VE Pr (Fc.set m p) (Tc.set m (t : Int))) 1 (by omega)
    (ixc mv.nv 1) (.variable i32 (mv.nv + 2)) (t : Int) (m + 1) (hvt2 _) (hix2 _)
    (by rw [VE_get1]; simp; omega) (by rw [ty1]; exact htv)
  rw [ty1, VE_get1, VE_set1] at w3
  have a4 := (pexecM_prim mv fu (wf2 mv.nv) _ _).trans w3
  -- to[m + 1] = p
  have w4 := pstmtM_write_ok mv (gS P [ci n, ci (m + 1), ci t, cz p]) (VE Pr ((Fc.set m p).set (m + 1) (t : Int)) (Tc.set m (t : Int))) 2
    (by omega) (ixc mv.nv 1) (.variable i32 (mv.nv + 3)) p (m + 1) (hvp2 _) (hix2 _)
    (by rw [VE_get2]; simp; omega) (by rw [ty2]; exact hpv)
  rw [ty2, VE_get2, VE_set2] at w4
  have a5 := (pexecM_prim mv fu (wt2 mv.nv) _ _).trans w4
  -- m = m + 1 again
  have hxm2 : vdenM mv (VE Pr ((Fc.set m p).set (m + 1) (t : Int)) ((Tc.set m (t : Int)).set (m + 1) p))
      (penvN mv.nv (gS P [ci n, ci (m + 1), ci t, cz p])) (.binary i32 .add (.variable i32 (mv.nv + 1)) (.literal i32 1)) =
      some ((m + 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, E1', Option.bind_some, den_literal,
      if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
    have : binaryValue .add ((m + 1 : Nat) : Int) 1 = ((m + 2 : Nat) : Int) := by
      show ((m + 1 : Nat) : Int) + 1 = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ hm)
  have as2 := gSM_assign mv P [ci n, ci (m + 1), ci t, cz p] (VE Pr ((Fc.set m p).set (m + 1) (t : Int)) ((Tc.set m (t : Int)).set (m + 1) p))
    1 (by simp) i32 _ _ _ hxm2 (ci (m + 1)) rfl rfl (i32v _ hm1M) (conv_signed i32 rfl rfl _ (i32v _ hm))
  have a6 := (pexecM_prim mv fu (incM mv.nv) _ _).trans as2
  have hset2 : [ci n, ci (m + 1), ci t, cz p].set 1 ⟨i32, ((m + 2 : Nat) : Int)⟩ = [ci n, ci (m + 2), ci t, cz p] := rfl
  rw [hset2] at a6
  have b6 := seqM_some a6 rfl (pexecM_skip mv fu _ _)
  have b5 := seqM_some a5 rfl b6
  have b4 := seqM_some a4 rfl b5
  have b3 := seqM_some a3 rfl b4
  have b2 := seqM_some a2 rfl b3
  have b1 := seqM_some a1 rfl b2
  have sc := pexecM_scope mv fu _ _ _ _ b1
  have tk := gS_takeC P [ci n, ci m, ci t, cz p] [ci n, ci (m + 2), ci t, cz p] [] rfl
  simp only [List.append_nil] at tk
  simp only [tk] at sc
  have b7 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, b7, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

/-- `{ if (c) { Y } }` as the converter writes it: a scope around a branch, followed by a skip. -/
abbrev Wr (c : NExpr) (Y : Command) : Command := .sequence (.scope (.sequence (.branch c Y Sk) Sk)) Sk

theorem wrap_true (mv : MV) (fu : Nat) (c : NExpr) (Y : Command) (P cs cs' : List Cell) (vv : Nat → List Int) (r : PRM)
    (hc : vdenM mv vv (penvN mv.nv (gS P cs)) c = some 1) (hY : pexecM mv fu Y (gS P cs) vv = some r)
    (hret : r.ret = none) (hps : r.ps = gS P cs') (hlen : cs.length = cs'.length) :
    ∃ r' : PRM, pexecM mv fu (Wr c Y) (gS P cs) vv = some r' ∧ r'.ret = none ∧ r'.ps = gS P cs' ∧ r'.vv = r.vv ∧
      r'.cost ≤ r.cost + (vwp c).1 + 4 ∧ r'.need ≤ max r.need (P.length + 2 * cs.length + (vwp c).2 + 4) ∧ r'.wk = r.wk := by
  have b1 := pexecM_branch_true mv fu c Y Sk _ _ 1 hc (by decide) r hY
  have b2 := seqM_some b1 hret (pexecM_skip mv fu _ _)
  have sc := pexecM_scope mv fu _ _ _ _ b2
  have tk := gS_takeC P cs cs' [] hlen
  simp only [List.append_nil] at tk
  rw [hps] at sc
  simp only [tk] at sc
  have b3 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, b3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp; try omega
  · simp [gS_mem_len, gS_bs_len]
    try omega
  · simp

theorem wrap_false (mv : MV) (fu : Nat) (c : NExpr) (Y : Command) (P cs : List Cell) (vv : Nat → List Int)
    (hc : vdenM mv vv (penvN mv.nv (gS P cs)) c = some 0) :
    ∃ r' : PRM, pexecM mv fu (Wr c Y) (gS P cs) vv = some r' ∧ r'.ret = none ∧ r'.ps = gS P cs ∧ r'.vv = vv ∧
      r'.cost ≤ (vwp c).1 + 4 ∧ r'.need ≤ P.length + 2 * cs.length + (vwp c).2 + 4 ∧ r'.wk = 0 := by
  have b1 := pexecM_branch_false mv fu c Y Sk _ _ hc _ (pexecM_skip mv fu _ _)
  have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
  have sc := pexecM_scope mv fu _ _ _ _ b2
  have tk := gS_takeC P cs cs [] rfl
  simp only [List.append_nil] at tk
  simp only [tk] at sc
  have b3 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, b3, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp [gS_mem_len, gS_bs_len]
    omega
  · simp

theorem le_conv (x y : Int) : bT.convert (binaryValue .le x y) = some (if x ≤ y then 1 else 0) := by
  by_cases h : x ≤ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem zero_den_lit (env : Nat → Ty → Option Int) : (NExpr.literal i32 0).denote env = some 0 := Proofs.TopoSortExec.zero_den env

abbrev cells4 (n m t : Nat) (p : Int) : List Cell := [ci n, ci m, ci t, cz p]

set_option maxHeartbeats 16000000 in
/-- The body of the loop: read the parent and append the arcs when the parent is a vertex other than `i`. -/
theorem bi_exec (mv : MV) (hnv : mv.nv = 3) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (Pr Fc Tc : List Int) (P : List Cell) (n m t : Nat) (hn : n < M31) (ht : t < n) (hPl : t < Pr.length)
    (hFl : m + 1 < Fc.length) (hTl : m + 1 < Tc.length) (hm : m + 2 < M31) (hPv : i32.valid (Pr.getD t 0) = true) (fu : Nat) :
    ∃ (r : PRM) (m' : Nat) (Fc' Tc' : List Int), pexecM mv fu (Bi mv.nv) (gS P [ci n, ci m, ci t]) (VE Pr Fc Tc) = some r ∧
      r.ret = none ∧ r.ps = gS P (cells4 n m' t (Pr.getD t 0)) ∧ r.vv = VE Pr Fc' Tc' ∧
      (Valid (Pr.getD t 0) t n → m' = m + 2 ∧ Fc' = (Fc.set m (Pr.getD t 0)).set (m + 1) (t : Int) ∧
        Tc' = (Tc.set m (t : Int)).set (m + 1) (Pr.getD t 0)) ∧
      (¬ Valid (Pr.getD t 0) t n → m' = m ∧ Fc' = Fc ∧ Tc' = Tc) ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 4 := by
  have htM : t < M31 := Nat.lt_trans ht hn
  have hmM : m < M31 := Nat.lt_of_le_of_lt (Nat.le_add_right m 2) hm
  generalize hpdef : Pr.getD t 0 = p at hPv ⊢
  -- int p = parent[i]
  have E2 := envs mv P [ci n, ci m, ci t] 2 (ci t) rfl (i32v t htM)
  have rp := rdM_val mv (VE Pr Fc Tc) (penvN mv.nv (gS P [ci n, ci m, ci t])) 0 (by omega) i32 ty0.symm (ixc mv.nv 2) rfl rfl t
    (cidx_den _ (mv.nv + 2) t E2 htM) p (by rw [VE_get0, ← hpdef]; exact vec_getI Pr t hPl) (by rw [ty0]; exact hPv)
  have d1 := gSM_decl mv P [ci n, ci m, ci t] (VE Pr Fc Tc) i32 _ _ _ rp (conv_signed i32 rfl rfl _ hPv)
  have q1 := (pexecM_prim mv fu (dP mv.nv) _ _).trans d1
  -- the conditions
  have e0 : penvN mv.nv (gS P (cells4 n m t p)) mv.nv i32 = some (n : Int) := envs mv P (cells4 n m t p) 0 (ci n) rfl (i32v n hn)
  have e2 := envs mv P (cells4 n m t p) 2 (ci t) rfl (i32v t htM)
  have e3 := envs mv P (cells4 n m t p) 3 (cz p) rfl hPv
  have hcne : vdenM mv (VE Pr Fc Tc) (penvN mv.nv (gS P (cells4 n m t p))) (cNe mv.nv) = some (if p ≠ (t : Int) then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, den_variable, e2, Option.bind_some, ne_conv]
  have hcle : vdenM mv (VE Pr Fc Tc) (penvN mv.nv (gS P (cells4 n m t p))) (cLe mv.nv) = some (if 0 ≤ p then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, zero_den_lit, Option.bind_some, den_variable, e3, Option.bind_some, le_conv]
  have hclt : vdenM mv (VE Pr Fc Tc) (penvN mv.nv (gS P (cells4 n m t p))) (cLt mv.nv) = some (if p < (n : Int) then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, e3, Option.bind_some, den_variable, e0, Option.bind_some, lt_conv]
  -- the common closing: the declaration, then the outer branch, then a skip
  have fin : ∀ (rb : PRM), pexecM mv fu (.branch (cNe mv.nv) (Y1 mv.nv) Sk) (gS P (cells4 n m t p)) (VE Pr Fc Tc) = some rb →
      rb.ret = none → ∃ r : PRM, pexecM mv fu (Bi mv.nv) (gS P [ci n, ci m, ci t]) (VE Pr Fc Tc) = some r ∧ r.ret = none ∧
        r.ps = rb.ps ∧ r.vv = rb.vv ∧ r.cost ≤ rb.cost + 20 ∧
          r.need ≤ max rb.need (max (P.length + 40) (rb.ps.mem.length + rb.ps.bs.length)) ∧ r.wk = rb.wk := by
    intro rb hrb hret
    have s1 := seqM_some hrb hret (pexecM_skip mv fu _ _)
    have s2 := seqM_some q1 rfl s1
    refine ⟨_, s2, by simpa using hret, by simp, by simp, ?_, ?_, by simp⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]; omega
  by_cases h1 : p ≠ (t : Int)
  · rw [if_pos h1] at hcne
    -- the inner wrapper Y1 = Wr cLe Y2
    by_cases h2 : 0 ≤ p
    · rw [if_pos h2] at hcle
      by_cases h3 : p < (n : Int)
      · rw [if_pos h3] at hclt
        have hFp : m + 1 < Fc.length := hFl
        obtain ⟨r3, hr3, hret3, hps3, hvv3, hc3, hn3, hw3⟩ := y3_exec mv hnv ty1 ty2 Pr Fc Tc P n m t p hn ht hFl hTl hm hPv fu
        obtain ⟨r2, hr2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := wrap_true mv fu (cLt mv.nv) (Y3 mv.nv) P (cells4 n m t p)
          [ci n, ci (m + 2), ci t, cz p] (VE Pr Fc Tc) r3 hclt hr3 hret3 hps3 rfl
        obtain ⟨r1, hr1, hret1, hps1, hvv1, hc1, hn1, hw1⟩ := wrap_true mv fu (cLe mv.nv) (Y2 mv.nv) P (cells4 n m t p)
          [ci n, ci (m + 2), ci t, cz p] (VE Pr Fc Tc) r2 hcle hr2 hret2 hps2 rfl
        have b1 := pexecM_branch_true mv fu (cNe mv.nv) (Y1 mv.nv) Sk _ _ 1 hcne (by decide) r1 hr1
        obtain ⟨r, hr, hret, hps, hvv, hc, hn', hw⟩ := fin _ b1 hret1
        refine ⟨r, m + 2, (Fc.set m p).set (m + 1) (t : Int), (Tc.set m (t : Int)).set (m + 1) p, hr, hret, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hps]; exact hps1
        · rw [hvv]; simp [hvv1, hvv2, hvv3]
        · intro _; exact ⟨rfl, rfl, rfl⟩
        · intro hv; exact absurd ⟨h1, h2, h3⟩ hv
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc hc1 hc2 hc3 ⊢; omega
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hps1] at hn' hn1 hn2 hn3 ⊢; omega
        · simp at hw hw1 hw2 hw3 ⊢; omega
      · rw [if_neg h3] at hclt
        obtain ⟨r2, hr2, hret2, hps2, hvv2, hc2, hn2, hw2⟩ := wrap_false mv fu (cLt mv.nv) (Y3 mv.nv) P (cells4 n m t p) (VE Pr Fc Tc) hclt
        obtain ⟨r1, hr1, hret1, hps1, hvv1, hc1, hn1, hw1⟩ := wrap_true mv fu (cLe mv.nv) (Y2 mv.nv) P (cells4 n m t p)
          (cells4 n m t p) (VE Pr Fc Tc) r2 hcle hr2 hret2 hps2 rfl
        have b1 := pexecM_branch_true mv fu (cNe mv.nv) (Y1 mv.nv) Sk _ _ 1 hcne (by decide) r1 hr1
        obtain ⟨r, hr, hret, hps, hvv, hc, hn', hw⟩ := fin _ b1 hret1
        refine ⟨r, m, Fc, Tc, hr, hret, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hps]; exact hps1
        · rw [hvv, hvv1, hvv2]
        · intro hv; exact absurd hv.2.2 h3
        · intro _; exact ⟨rfl, rfl, rfl⟩
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc hc1 hc2 ⊢; omega
        · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hps1] at hn' hn1 hn2 ⊢; omega
        · simp at hw hw1 hw2 ⊢; omega
    · rw [if_neg h2] at hcle
      obtain ⟨r1, hr1, hret1, hps1, hvv1, hc1, hn1, hw1⟩ := wrap_false mv fu (cLe mv.nv) (Y2 mv.nv) P (cells4 n m t p) (VE Pr Fc Tc) hcle
      have b1 := pexecM_branch_true mv fu (cNe mv.nv) (Y1 mv.nv) Sk _ _ 1 hcne (by decide) r1 hr1
      obtain ⟨r, hr, hret, hps, hvv, hc, hn', hw⟩ := fin _ b1 hret1
      refine ⟨r, m, Fc, Tc, hr, hret, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hps]; exact hps1
      · rw [hvv, hvv1]
      · intro hv; exact absurd hv.2.1 h2
      · intro _; exact ⟨rfl, rfl, rfl⟩
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc hc1 ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hps1] at hn' hn1 ⊢; omega
      · simp at hw hw1 ⊢; omega
  · rw [if_neg h1] at hcne
    have b1 := pexecM_branch_false mv fu (cNe mv.nv) (Y1 mv.nv) Sk _ _ hcne _ (pexecM_skip mv fu _ _)
    obtain ⟨r, hr, hret, hps, hvv, hc, hn', hw⟩ := fin _ b1 rfl
    refine ⟨r, m, Fc, Tc, hr, hret, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hps]
    · rw [hvv]
    · intro hv; exact absurd hv.1 h1
    · intro _; exact ⟨rfl, rfl, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hn' ⊢; omega
    · simp at hw ⊢; omega

theorem vidx_len (Pr : List Int) (n t : Nat) : (vidx Pr n t).length ≤ t := by
  unfold vidx
  have := List.length_filter_le (fun i => decide (Valid (Pr.getD i 0) i n)) (List.range t)
  simpa using this

theorem flat2_len {α : Type} (f : Nat → List α) (hf : ∀ i, (f i).length = 2) :
    ∀ l : List Nat, (l.flatMap f).length = 2 * l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.length_append, hf, ih]; simp; omega

theorem arcP_len (Pr : List Int) (n t : Nat) : (arcP Pr n t).length = 2 * (vidx Pr n t).length := by
  unfold arcP
  exact flat2_len _ (fun i => rfl) _

theorem arcP_len_le (Pr : List Int) (n t : Nat) : (arcP Pr n t).length ≤ 2 * t := by
  have := vidx_len Pr n t
  rw [arcP_len]; omega

/-- The vectors `from` and `to` after the first `t` indices were handled. -/
def FFt (Pr : List Int) (n t : Nat) (F0 : List Int) : List Int :=
  (arcP Pr n t).map (fun a => a.1) ++ F0.drop (arcP Pr n t).length
def TTt (Pr : List Int) (n t : Nat) (T0 : List Int) : List Int :=
  (arcP Pr n t).map (fun a => a.2) ++ T0.drop (arcP Pr n t).length

theorem FFt_len (Pr : List Int) (n t : Nat) (F0 : List Int) (h : (arcP Pr n t).length ≤ F0.length) :
    (FFt Pr n t F0).length = F0.length := by
  unfold FFt; simp; omega

theorem TTt_len (Pr : List Int) (n t : Nat) (T0 : List Int) (h : (arcP Pr n t).length ≤ T0.length) :
    (TTt Pr n t T0).length = T0.length := by
  unfold TTt; simp; omega

set_option maxHeartbeats 16000000 in
/-- The whole body of `tree_edges_from_parent`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 3) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32)
    (Pr F0 T0 : List Int) (P : List Cell) (n : Nat) (hn : n < 1073741824) (hPl : n ≤ Pr.length)
    (hF : 2 * n ≤ F0.length) (hT : 2 * n ≤ T0.length) (hPv : ∀ x ∈ Pr, i32.valid x = true) (fu : Nat) (hfu : n + 2 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyTE mv.nv) (gS P [ci n]) (VE Pr F0 T0) = some r ∧
      r.ret = some (((arcP Pr n n).length : Nat) : Int) ∧ r.vv = VE Pr (FFt Pr n n F0) (TTt Pr n n T0) ∧
      (∃ cs : List Cell, r.ps = gS P cs) ∧ r.cost ≤ 420 * n + 60 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 4 * n := by
  have hnM : n < M31 := by show n < 2147483648; omega
  have mem : ∀ j, j < Pr.length → i32.valid (Pr.getD j 0) = true := fun j hj => hPv _ (getD_mem _ _ hj)
  -- int m = 0
  have d0 := gSM_decl mv P [ci n] (VE Pr F0 T0) i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact Proofs.TopoSortExec.zero_den _) (conv_signed i32 rfl rfl _ (i32v 0 (by decide)))
  have q0 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d0
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv (P) 2 0 n (by omega) (by omega) (Bi mv.nv)
    (fun t vv C => vv = VE Pr (FFt Pr n t F0) (TTt Pr n t T0) ∧ C = [ci n, ci (arcP Pr n t).length]) 400 60 4 0 (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hl := arcP_len_le Pr n t
      have hlF : (FFt Pr n t F0).length = F0.length := FFt_len Pr n t F0 (by omega)
      have hlT : (TTt Pr n t T0).length = T0.length := TTt_len Pr n t T0 (by omega)
      obtain ⟨r, m', Fc', Tc', hr, hret, hps, hvv, hval, hnval, hc, hnd, hwk⟩ := bi_exec mv hnv ty0 ty1 ty2 Pr
        (FFt Pr n t F0) (TTt Pr n t T0) P n (arcP Pr n t).length t hnM ht (by omega) (by omega) (by omega)
        (by show (arcP Pr n t).length + 2 < 2147483648; omega) (mem t (by omega)) fu
      refine ⟨r, [cz (Pr.getD t 0)], [ci n, ci m'], hr, hret, hps, rfl, rfl, ⟨?_, ?_⟩, hc, hnd, hwk⟩
      · rw [hvv]
        unfold FFt TTt
        rw [arcP_succ]
        by_cases hv : Valid (Pr.getD t 0) t n
        · obtain ⟨hm', hF', hT'⟩ := hval hv
          rw [if_pos hv]
          unfold FFt at hF'
          unfold TTt at hT'
          rw [hF', hT']
          simp only [List.length_append, List.map_append, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
          rw [pair_pad _ F0 _ _ _ (by simp) (by omega), pair_pad _ T0 _ _ _ (by simp) (by omega)]
        · obtain ⟨hm', hF', hT'⟩ := hnval hv
          rw [if_neg hv]
          unfold FFt at hF'
          unfold TTt at hT'
          rw [hF', hT']
          simp
      · rw [arcP_succ]
        by_cases hv : Valid (Pr.getD t 0) t n
        · obtain ⟨hm', _, _⟩ := hval hv
          rw [if_pos hv, hm']; simp
        · obtain ⟨hm', _, _⟩ := hnval hv
          rw [if_neg hv, hm']; simp)
    (VE Pr (FFt Pr n 0 F0) (TTt Pr n 0 T0)) [ci n, ci (arcP Pr n 0).length] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  have h00 : (arcP Pr n 0).length = 0 := by simp [arcP, vidx]
  have hall : (arcP Pr n n).length ≤ 2 * n := arcP_len_le Pr n n
  have hallM : (arcP Pr n n).length < M31 := by show (arcP Pr n n).length < 2147483648; omega
  have e1 := gSM_env mv.nv P [ci n, ci (arcP Pr n n).length] 1 (ci (arcP Pr n n).length) rfl (i32v _ hallM)
  have rr := pstmtM_ret_ok mv (gS P [ci n, ci (arcP Pr n n).length]) (VE Pr (FFt Pr n n F0) (TTt Pr n n T0))
    (.variable i32 (mv.nv + 1)) (((arcP Pr n n).length : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e1)
  have e4 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have hr0 : pexecM mv fu (forStmtB mv.nv 2 0 (Bi mv.nv)) (gS P ([ci n] ++ [(⟨i32, 0⟩ : Cell)])) (VE Pr F0 T0) = some res := by
    have := hr'
    rw [h00] at this
    exact this
  have c2 := seqM_some hr0 hret (by rw [hps, hvv]; exact e4)
  have c1 := seqM_some q0 rfl c2
  refine ⟨_, c1, rfl, ?_, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · simp [hvv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hps] at hnd ⊢; omega
  · simp at hw ⊢; omega

end Proofs.TreeEdgesExec
