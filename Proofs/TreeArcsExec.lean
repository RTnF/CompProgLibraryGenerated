import Proofs.TreeEdgesExec
import Proofs.Generated.TreeArcs

namespace Proofs.TreeArcsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem)
open Proofs.TopoSortExec (i32v)
open Proofs.TreeEdgesExec (cz pair_pad flat2_len)

/-! ### `tree_arcs_from_list` (nv = 4: from, to, af, at).  Cells: 0 = m, 1 = i, 2 = a, 3 = b -/

abbrev idxE (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 1))
abbrev idx2 (nv : Nat) : NExpr := .cast u64 (.binary i32 .mul (.literal i32 2) (.variable i32 (nv + 1)))
abbrev idx21 (nv : Nat) : NExpr :=
  .cast u64 (.binary i32 .add (.binary i32 .mul (.literal i32 2) (.variable i32 (nv + 1))) (.literal i32 1))
abbrev dA (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 0) (idxE nv))
abbrev dB (nv : Nat) : NStmt := .declare i32 true (.read i32 (.local 1) (idxE nv))
abbrev wA1 (nv : Nat) : NStmt := .write (.local 2) i32 (idx2 nv) (.variable i32 (nv + 2))
abbrev wB1 (nv : Nat) : NStmt := .write (.local 3) i32 (idx2 nv) (.variable i32 (nv + 3))
abbrev wA2 (nv : Nat) : NStmt := .write (.local 2) i32 (idx21 nv) (.variable i32 (nv + 3))
abbrev wB2 (nv : Nat) : NStmt := .write (.local 3) i32 (idx21 nv) (.variable i32 (nv + 2))
abbrev Bar (nv : Nat) : Command :=
  .sequence (.primitive (dA nv)) (.sequence (.primitive (dB nv)) (.sequence (.primitive (wA1 nv)) (.sequence (.primitive (wB1 nv))
    (.sequence (.primitive (wA2 nv)) (.sequence (.primitive (wB2 nv)) Sk)))))
abbrev bodyAR (nv : Nat) : Command := .sequence (forStmtB nv 1 0 (Bar nv)) Sk

theorem body_eqAR : Proofs.TreeArcsInstance.tree_arcs_from_list.body = bodyAR 4 := rfl

theorem idx2_den (env : Nat → Ty → Option Int) (k t : Nat) (h : env k i32 = some (t : Int)) (ht : 2 * t + 1 < M31) :
    (NExpr.cast u64 (.binary i32 .mul (.literal i32 2) (.variable i32 k))).denote env = some ((2 * t : Nat) : Int) := by
  rw [den_cast, den_binary, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, den_variable, h,
    Option.bind_some]
  have e : binaryValue .mul (2 : Int) (t : Int) = ((2 * t : Nat) : Int) := by
    show (2 : Int) * (t : Int) = _; push_cast; rfl
  rw [e, conv_signed i32 rfl rfl _ (i32v _ (by omega)), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : 2 * t + 1 < 2147483648 := ht; omega)

theorem idx21_den (env : Nat → Ty → Option Int) (k t : Nat) (h : env k i32 = some (t : Int)) (ht : 2 * t + 1 < M31) :
    (NExpr.cast u64 (.binary i32 .add (.binary i32 .mul (.literal i32 2) (.variable i32 k)) (.literal i32 1))).denote env =
      some ((2 * t + 1 : Nat) : Int) := by
  rw [den_cast, den_binary, den_binary, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, den_variable, h,
    Option.bind_some]
  have e : binaryValue .mul (2 : Int) (t : Int) = ((2 * t : Nat) : Int) := by
    show (2 : Int) * (t : Int) = _; push_cast; rfl
  rw [e, conv_signed i32 rfl rfl _ (i32v _ (by omega)), Option.bind_some, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have e2 : binaryValue .add ((2 * t : Nat) : Int) 1 = ((2 * t + 1 : Nat) : Int) := by
    show ((2 * t : Nat) : Int) + 1 = _; push_cast; rfl
  rw [e2, conv_signed i32 rfl rfl _ (i32v _ ht), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have : 2 * t + 1 < 2147483648 := ht; omega)

/-- The contents of the vectors `from`, `to`, `af`, `at`. -/
def VA (Fr To AF AT : List Int) : Nat → List Int := fun k =>
  if k = 0 then Fr else if k = 1 then To else if k = 2 then AF else if k = 3 then AT else []

theorem VA_get0 (Fr To AF AT : List Int) : VA Fr To AF AT 0 = Fr := by simp [VA]
theorem VA_get1 (Fr To AF AT : List Int) : VA Fr To AF AT 1 = To := by simp [VA]
theorem VA_get2 (Fr To AF AT : List Int) : VA Fr To AF AT 2 = AF := by simp [VA]
theorem VA_get3 (Fr To AF AT : List Int) : VA Fr To AF AT 3 = AT := by simp [VA]
theorem VA_set2 (Fr To AF AT x : List Int) : upd (VA Fr To AF AT) 2 x = VA Fr To x AT := by
  funext k; unfold upd VA; split <;> simp_all
theorem VA_set3 (Fr To AF AT x : List Int) : upd (VA Fr To AF AT) 3 x = VA Fr To AF x := by
  funext k; unfold upd VA; split <;> simp_all

set_option maxHeartbeats 16000000 in
/-- One iteration of the loop. -/
theorem b_body (mv : MV) (hnv : mv.nv = 4) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32) (ty3 : mv.ty 3 = i32)
    (Fr To AF AT : List Int) (P : List Cell) (m t : Nat) (hm : m < M31) (ht : t < m) (h2 : 2 * t + 1 < M31)
    (hF : t < Fr.length) (hT : t < To.length) (hAF : 2 * t + 1 < AF.length) (hAT : 2 * t + 1 < AT.length)
    (hav : i32.valid (Fr.getD t 0) = true) (hbv : i32.valid (To.getD t 0) = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Bar mv.nv) (gS P [ci m, ci t]) (VA Fr To AF AT) = some r ∧ r.ret = none ∧
      r.ps = gS P ([ci m] ++ [ci t] ++ [cz (Fr.getD t 0), cz (To.getD t 0)]) ∧
      r.vv = VA Fr To ((AF.set (2 * t) (Fr.getD t 0)).set (2 * t + 1) (To.getD t 0))
        ((AT.set (2 * t) (To.getD t 0)).set (2 * t + 1) (Fr.getD t 0)) ∧
      r.cost ≤ 300 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 4 := by
  have htM : t < M31 := Nat.lt_trans ht hm
  generalize hadef : Fr.getD t 0 = a at hav ⊢
  generalize hbdef : To.getD t 0 = b at hbv ⊢
  have E1 := envs mv P [ci m, ci t] 1 (ci t) rfl (i32v t htM)
  have r1 := rdM_val mv (VA Fr To AF AT) (penvN mv.nv (gS P [ci m, ci t])) 0 (by omega) i32 ty0.symm (idxE mv.nv) rfl rfl t
    (cidx_den _ (mv.nv + 1) t E1 htM) a (by rw [VA_get0, ← hadef]; exact vec_getI Fr t hF) (by rw [ty0]; exact hav)
  have d1 := gSM_decl mv P [ci m, ci t] (VA Fr To AF AT) i32 _ _ _ r1 (conv_signed i32 rfl rfl _ hav)
  have q1 := (pexecM_prim mv fu (dA mv.nv) _ _).trans d1
  have E1' := envs mv P [ci m, ci t, cz a] 1 (ci t) rfl (i32v t htM)
  have r2 := rdM_val mv (VA Fr To AF AT) (penvN mv.nv (gS P [ci m, ci t, cz a])) 1 (by omega) i32 ty1.symm (idxE mv.nv) rfl rfl t
    (cidx_den _ (mv.nv + 1) t E1' htM) b (by rw [VA_get1, ← hbdef]; exact vec_getI To t hT) (by rw [ty1]; exact hbv)
  have d2 := gSM_decl mv P [ci m, ci t, cz a] (VA Fr To AF AT) i32 _ _ _ r2 (conv_signed i32 rfl rfl _ hbv)
  have q2 := (pexecM_prim mv fu (dB mv.nv) _ _).trans d2
  -- the four writes
  have E1'' := envs mv P [ci m, ci t, cz a, cz b] 1 (ci t) rfl (i32v t htM)
  have E2 := envs mv P [ci m, ci t, cz a, cz b] 2 (cz a) rfl hav
  have E3 := envs mv P [ci m, ci t, cz a, cz b] 3 (cz b) rfl hbv
  have hi2 : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci m, ci t, cz a, cz b])) (idx2 mv.nv) = some ((2 * t : Nat) : Int) := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl]; exact idx2_den _ (mv.nv + 1) t E1'' h2
  have hi21 : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci m, ci t, cz a, cz b])) (idx21 mv.nv) = some ((2 * t + 1 : Nat) : Int) := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl]; exact idx21_den _ (mv.nv + 1) t E1'' h2
  have hva : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci m, ci t, cz a, cz b])) (.variable i32 (mv.nv + 2)) = some a := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E2
  have hvb : ∀ V, vdenM mv V (penvN mv.nv (gS P [ci m, ci t, cz a, cz b])) (.variable i32 (mv.nv + 3)) = some b := by
    intro V; rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact E3
  have w1 := pstmtM_write_ok mv (gS P [ci m, ci t, cz a, cz b]) (VA Fr To AF AT) 2 (by omega) (idx2 mv.nv) (.variable i32 (mv.nv + 2)) a
    (2 * t) (hva _) (hi2 _) (by rw [VA_get2]; omega) (by rw [ty2]; exact hav)
  rw [ty2, VA_get2, VA_set2] at w1
  have a1 := (pexecM_prim mv fu (wA1 mv.nv) _ _).trans w1
  have w2 := pstmtM_write_ok mv (gS P [ci m, ci t, cz a, cz b]) (VA Fr To (AF.set (2 * t) a) AT) 3 (by omega) (idx2 mv.nv)
    (.variable i32 (mv.nv + 3)) b (2 * t) (hvb _) (hi2 _) (by rw [VA_get3]; omega) (by rw [ty3]; exact hbv)
  rw [ty3, VA_get3, VA_set3] at w2
  have a2 := (pexecM_prim mv fu (wB1 mv.nv) _ _).trans w2
  have w3 := pstmtM_write_ok mv (gS P [ci m, ci t, cz a, cz b]) (VA Fr To (AF.set (2 * t) a) (AT.set (2 * t) b)) 2 (by omega)
    (idx21 mv.nv) (.variable i32 (mv.nv + 3)) b (2 * t + 1) (hvb _) (hi21 _) (by rw [VA_get2]; simp; omega)
    (by rw [ty2]; exact hbv)
  rw [ty2, VA_get2, VA_set2] at w3
  have a3 := (pexecM_prim mv fu (wA2 mv.nv) _ _).trans w3
  have w4 := pstmtM_write_ok mv (gS P [ci m, ci t, cz a, cz b])
    (VA Fr To ((AF.set (2 * t) a).set (2 * t + 1) b) (AT.set (2 * t) b)) 3 (by omega) (idx21 mv.nv)
    (.variable i32 (mv.nv + 2)) a (2 * t + 1) (hva _) (hi21 _) (by rw [VA_get3]; simp; omega) (by rw [ty3]; exact hav)
  rw [ty3, VA_get3, VA_set3] at w4
  have a4 := (pexecM_prim mv fu (wB2 mv.nv) _ _).trans w4
  have b5 := seqM_some a4 rfl (pexecM_skip mv fu _ _)
  have b4 := seqM_some a3 rfl b5
  have b3 := seqM_some a2 rfl b4
  have b2 := seqM_some a1 rfl b3
  have b1 := seqM_some q2 rfl b2
  have b0 := seqM_some q1 rfl b1
  refine ⟨_, b0, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  · simp

/-- The first `t` edges as the list of their arcs, the sources (`ilvF`) and the targets (`ilvT`). -/
def ilvF (Fr To : List Int) (t : Nat) : List Int := (List.range t).flatMap (fun i => [Fr.getD i 0, To.getD i 0])
def ilvT (Fr To : List Int) (t : Nat) : List Int := (List.range t).flatMap (fun i => [To.getD i 0, Fr.getD i 0])

theorem ilvF_succ (Fr To : List Int) (t : Nat) : ilvF Fr To (t + 1) = ilvF Fr To t ++ [Fr.getD t 0, To.getD t 0] := by
  unfold ilvF
  rw [List.range_succ, List.flatMap_append]
  simp

theorem ilvT_succ (Fr To : List Int) (t : Nat) : ilvT Fr To (t + 1) = ilvT Fr To t ++ [To.getD t 0, Fr.getD t 0] := by
  unfold ilvT
  rw [List.range_succ, List.flatMap_append]
  simp

theorem ilvF_len (Fr To : List Int) (t : Nat) : (ilvF Fr To t).length = 2 * t := by
  unfold ilvF
  rw [Proofs.TreeEdgesExec.flat2_len (fun i => [Fr.getD i 0, To.getD i 0]) (fun i => rfl)]
  simp

theorem ilvT_len (Fr To : List Int) (t : Nat) : (ilvT Fr To t).length = 2 * t := by
  unfold ilvT
  rw [Proofs.TreeEdgesExec.flat2_len (fun i => [To.getD i 0, Fr.getD i 0]) (fun i => rfl)]
  simp

def AFt (Fr To AF : List Int) (t : Nat) : List Int := ilvF Fr To t ++ AF.drop (2 * t)
def ATt (Fr To AT : List Int) (t : Nat) : List Int := ilvT Fr To t ++ AT.drop (2 * t)

theorem AFt_len (Fr To AF : List Int) (t : Nat) (h : 2 * t ≤ AF.length) : (AFt Fr To AF t).length = AF.length := by
  unfold AFt; rw [List.length_append, ilvF_len, List.length_drop]; omega

theorem ATt_len (Fr To AT : List Int) (t : Nat) (h : 2 * t ≤ AT.length) : (ATt Fr To AT t).length = AT.length := by
  unfold ATt; rw [List.length_append, ilvT_len, List.length_drop]; omega

theorem AFt_succ (Fr To AF : List Int) (t : Nat) (h : 2 * t + 1 < AF.length) :
    ((AFt Fr To AF t).set (2 * t) (Fr.getD t 0)).set (2 * t + 1) (To.getD t 0) = AFt Fr To AF (t + 1) := by
  unfold AFt
  rw [pair_pad _ AF (2 * t) _ _ (ilvF_len Fr To t) h, ilvF_succ]
  simp [List.append_assoc]
  rfl

theorem ATt_succ (Fr To AT : List Int) (t : Nat) (h : 2 * t + 1 < AT.length) :
    ((ATt Fr To AT t).set (2 * t) (To.getD t 0)).set (2 * t + 1) (Fr.getD t 0) = ATt Fr To AT (t + 1) := by
  unfold ATt
  rw [pair_pad _ AT (2 * t) _ _ (ilvT_len Fr To t) h, ilvT_succ]
  simp [List.append_assoc]
  rfl

set_option maxHeartbeats 16000000 in
/-- The whole body of `tree_arcs_from_list`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 4) (ty0 : mv.ty 0 = i32) (ty1 : mv.ty 1 = i32) (ty2 : mv.ty 2 = i32) (ty3 : mv.ty 3 = i32)
    (Fr To AF AT : List Int) (P : List Cell) (m : Nat) (hm : m < 536870912) (hF : m ≤ Fr.length) (hT : m ≤ To.length)
    (hAF : 2 * m ≤ AF.length) (hAT : 2 * m ≤ AT.length) (hFv : ∀ x ∈ Fr, i32.valid x = true) (hTv : ∀ x ∈ To, i32.valid x = true)
    (fu : Nat) (hfu : m + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyAR mv.nv) (gS P [ci m]) (VA Fr To AF AT) = some r ∧ r.ret = none ∧
      r.vv = VA Fr To (AFt Fr To AF m) (ATt Fr To AT m) ∧ (∃ cs : List Cell, r.ps = gS P cs) ∧
      r.cost ≤ 320 * m + 40 ∧ r.need ≤ P.length + 60 ∧ r.wk ≤ 4 * m := by
  have hmM : m < M31 := by show m < 2147483648; omega
  have memF : ∀ j, j < Fr.length → i32.valid (Fr.getD j 0) = true := fun j hj => hFv _ (getD_mem _ _ hj)
  have memT : ∀ j, j < To.length → i32.valid (To.getD j 0) = true := fun j hj => hTv _ (getD_mem _ _ hj)
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 1 0 m (by omega) (by omega) (Bar mv.nv)
    (fun t vv C => vv = VA Fr To (AFt Fr To AF t) (ATt Fr To AT t) ∧ C = [ci m]) 300 60 4 0 (by omega)
    (by
      intro t vv C fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      have hlF := AFt_len Fr To AF t (by omega)
      have hlT := ATt_len Fr To AT t (by omega)
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := b_body mv hnv ty0 ty1 ty2 ty3 Fr To (AFt Fr To AF t) (ATt Fr To AT t) P m t hmM ht
        (by show 2 * t + 1 < 2147483648; omega) (by omega) (by omega) (by omega) (by omega) (memF t (by omega))
        (memT t (by omega)) fu
      refine ⟨r, [cz (Fr.getD t 0), cz (To.getD t 0)], [ci m], hr, hret, hps, rfl, rfl, ⟨?_, rfl⟩, hc, hnd, hwk⟩
      rw [hvv, AFt_succ Fr To AF t (by omega), ATt_succ Fr To AT t (by omega)])
    (VA Fr To (AFt Fr To AF 0) (ATt Fr To AT 0)) [ci m] rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  have t1 := seqM_some hr' hret (pexecM_skip mv fu _ _)
  refine ⟨_, t1, by simp [hret], ?_, ⟨[ci m], by simp [hps]⟩, ?_, ?_, ?_⟩
  · simp [hvv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, hps] at hnd ⊢; omega
  · simp at hw ⊢; omega

end Proofs.TreeArcsExec
