import Proofs.RollingHashBuild

namespace Proofs.RollingHashExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB Proofs.RollingHashCore Proofs.RollingHashBuild
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (size_val0)
open Proofs.Mod61Body (M61 u64_lt)

theorem mE_val (env : Nat → Ty → Option Int) : mE.denote env = some (M61 : Int) := Proofs.Mod61Body.mE_value env

theorem m31_val (env : Nat → Ty → Option Int) : m31E.denote env = some (2147483647 : Int) := by
  have a : u64.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid 2147483648 = true := by simp [Ty.valid]
  have c : i32.valid 1 = true := by simp [Ty.valid]
  have d : u64.valid 2147483647 = true := by simp [Ty.valid]
  have f : u64.valid (1 * 2147483648) = true := by simpa using b
  have g : u64.valid (2147483648 - 1) = true := by simpa using d
  simp [NExpr.denote, a, b, c, binaryValue, Ty.convert_of_valid _ _ a, Ty.convert_of_valid _ _ b, Ty.convert_of_valid _ _ f,
    Ty.convert_of_valid _ _ g, Ty.convert_of_valid _ _ d]

theorem m30_val (env : Nat → Ty → Option Int) : m30E.denote env = some (1073741823 : Int) := by
  have a : u64.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid 1073741824 = true := by simp [Ty.valid]
  have c : i32.valid 1 = true := by simp [Ty.valid]
  have d : u64.valid 1073741823 = true := by simp [Ty.valid]
  have f : u64.valid (1 * 1073741824) = true := by simpa using b
  have g : u64.valid (1073741824 - 1) = true := by simpa using d
  simp [NExpr.denote, a, b, c, binaryValue, Ty.convert_of_valid _ _ a, Ty.convert_of_valid _ _ b, Ty.convert_of_valid _ _ f,
    Ty.convert_of_valid _ _ g, Ty.convert_of_valid _ _ d]

theorem cast0_val (env : Nat → Ty → Option Int) : (NExpr.cast u64 (.literal i32 0)).denote env = some 0 := by
  have a : i32.valid 0 = true := by simp [Ty.valid]
  have b : u64.valid 0 = true := by simp [Ty.valid]
  simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]

theorem cast1_val (env : Nat → Ty → Option Int) : (NExpr.cast u64 (.literal i32 1)).denote env = some 1 := by
  have a : i32.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid 1 = true := by simp [Ty.valid]
  simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]

theorem size_val3 (mv : MV) (hnv : mv.nv = 3) (hty2 : mv.ty 2 = i32) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (hn : (vv 2).length < 2147483648) :
    vdenM mv vv env (.cast i32 (.size (.integer i32) (.local 2))) = some ((vv 2).length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer i32) (.local 2))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer i32) (.local 2)).scalarOnly = false := rfl
  have hsz : vdenM mv vv env (.size (.integer i32) (.local 2)) = some ((vv 2).length : Int) := by
    rw [vdenM, if_neg (by rw [hr]; decide), if_pos ⟨by omega, hty2.symm⟩]
  rw [vdenM, if_neg (by rw [hr2]; decide), hsz, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (validN _ hn)

set_option maxHeartbeats 8000000 in
/-- The whole body of `rolling_hash_build`. -/
theorem build_exec (mv : MV) (hnv : mv.nv = 3) (hty2 : mv.ty 2 = i32) (hty0 : mv.ty 0 = u64) (hty1 : mv.ty 1 = u64)
    (fu : Nat) (P : List Cell) (S HS0 PW0 : List Nat) (b n : Nat) (hb131 : b = 131) (hn : n < 2147483647)
    (hS : S.length = n) (hSv : ∀ x ∈ S, x < 2147483648) (hH : HS0.length = n + 1) (hW : PW0.length = n + 1)
    (hfu : n + 1 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (progB mv.nv) (gS P []) (VR S HS0 PW0) = some r ∧ r.ret = none ∧
      r.ps = gS P (C5 b n) ∧ r.vv = VR S (Hs b S n ++ HS0.drop (n + 1)) (Ps b n ++ PW0.drop (n + 1)) ∧
      r.cost ≤ 2120 * n + 200 ∧ r.need ≤ P.length + 105 ∧ r.wk ≤ 2 * n + 2 := by
  have hb : b < 2^61 := by rw [hb131]; omega
  have hnM : n < 2147483648 := by omega
  have hM : M61 < 18446744073709551616 := by unfold M61; omega
  cases HS0 with
  | nil => simp at hH
  | cons h0 t0 =>
  cases PW0 with
  | nil => simp at hW
  | cons p0 q0 =>
  have e0 : vdenM mv (VR S (h0 :: t0) (p0 :: q0)) (penvN mv.nv (gS P [])) (.cast u64 (.literal i32 131)) = some (b : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, hb131]
    have a : i32.valid 131 = true := by simp [Ty.valid]
    have c : u64.valid 131 = true := by simp [Ty.valid]
    simp [NExpr.denote, a, Ty.convert_of_valid _ _ c]
  have d0 := gSM_decl mv P [] (VR S (h0 :: t0) (p0 :: q0)) u64 _ _ _ e0 (Ty.convert_of_valid _ _ (u64_lt b (by omega)))
  have q0' := (pexecM_prim mv fu bDecl _ _).trans d0
  have e1 : vdenM mv (VR S (h0 :: t0) (p0 :: q0)) (penvN mv.nv (gS P [cu b])) mE = some (M61 : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact mE_val _
  have d1 := gSM_decl mv P [cu b] (VR S (h0 :: t0) (p0 :: q0)) u64 mE _ _ e1 (Ty.convert_of_valid _ _ (u64_lt M61 hM))
  have q1 := (pexecM_prim mv fu (.declare u64 true mE) _ _).trans d1
  have e2 : vdenM mv (VR S (h0 :: t0) (p0 :: q0)) (penvN mv.nv (gS P [cu b, cu M61])) m31E = some (2147483647 : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact m31_val _
  have d2 := gSM_decl mv P [cu b, cu M61] (VR S (h0 :: t0) (p0 :: q0)) u64 m31E _ _ e2
    (Ty.convert_of_valid _ _ (u64_lt 2147483647 (by omega)))
  have q2 := (pexecM_prim mv fu (.declare u64 true m31E) _ _).trans d2
  have e3 : vdenM mv (VR S (h0 :: t0) (p0 :: q0)) (penvN mv.nv (gS P [cu b, cu M61, cu 2147483647])) m30E = some (1073741823 : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact m30_val _
  have d3 := gSM_decl mv P [cu b, cu M61, cu 2147483647] (VR S (h0 :: t0) (p0 :: q0)) u64 m30E _ _ e3
    (Ty.convert_of_valid _ _ (u64_lt 1073741823 (by omega)))
  have q3 := (pexecM_prim mv fu (.declare u64 true m30E) _ _).trans d3
  have hlen0 : (VR S (h0 :: t0) (p0 :: q0) 2).length = n := by rw [VR_get2]; simp [hS]
  have hsz := size_val3 mv hnv hty2 (VR S (h0 :: t0) (p0 :: q0)) (penvN mv.nv (gS P [cu b, cu M61, cu 2147483647, cu 1073741823]))
    (by rw [hlen0]; exact hnM)
  rw [hlen0] at hsz
  have d4 := gSM_decl mv P [cu b, cu M61, cu 2147483647, cu 1073741823] (VR S (h0 :: t0) (p0 :: q0)) i32 _ _ _ hsz
    (conv_signed i32 rfl rfl _ (validN n hnM))
  have q4 := (pexecM_prim mv fu (.declare i32 true (.cast i32 (.size (.integer i32) (.local 2)))) _ _).trans d4
  -- hs[0] = 0
  have x0 : vdenM mv (VR S (h0 :: t0) (p0 :: q0)) (penvN mv.nv (gS P (C5 b n))) (.cast u64 (.literal i32 0)) = some ((0 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cast0_val _
  have wr1 := pstmtM_write_ok mv (gS P (C5 b n)) (VR S (h0 :: t0) (p0 :: q0)) 0 (by omega) (.cast u64 (.literal i32 0))
    (.cast u64 (.literal i32 0)) ((0 : Nat) : Int) 0 x0 x0 (by rw [VR_get0]; simp) (by rw [hty0]; exact u64_lt 0 (by omega))
  rw [hty0, VR_write0] at wr1
  have w1 := (pexecM_prim mv fu (.write (.local 0) u64 (.cast u64 (.literal i32 0)) (.cast u64 (.literal i32 0))) _ _).trans wr1
  have x1 : vdenM mv (VR S ((h0 :: t0).set 0 0) (p0 :: q0)) (penvN mv.nv (gS P (C5 b n))) (.cast u64 (.literal i32 1)) = some ((1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cast1_val _
  have x0' : vdenM mv (VR S ((h0 :: t0).set 0 0) (p0 :: q0)) (penvN mv.nv (gS P (C5 b n))) (.cast u64 (.literal i32 0)) = some ((0 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact cast0_val _
  have wr2 := pstmtM_write_ok mv (gS P (C5 b n)) (VR S ((h0 :: t0).set 0 0) (p0 :: q0)) 1 (by omega) (.cast u64 (.literal i32 0))
    (.cast u64 (.literal i32 1)) ((1 : Nat) : Int) 0 x1 x0' (by rw [VR_get1]; simp) (by rw [hty1]; exact u64_lt 1 (by omega))
  rw [hty1, VR_write1] at wr2
  have w2 := (pexecM_prim mv fu (.write (.local 1) u64 (.cast u64 (.literal i32 0)) (.cast u64 (.literal i32 1))) _ _).trans wr2
  have hHL : ((h0 :: t0).set 0 0).length = n + 1 := by simp [List.length_set] at hH ⊢; omega
  have hPL : ((p0 :: q0).set 0 1).length = n + 1 := by simp [List.length_set] at hW ⊢; omega
  obtain ⟨rl, hrl, hrlps, hrlvv, hrlret, hrlc, hrln, hrlw⟩ := l_build mv hnv hty2 hty0 hty1 fu P S ((h0 :: t0).set 0 0) ((p0 :: q0).set 0 1) b n hb hn
    hS hSv hHL hPL hfu
  have hstart : VR S (Hs b S 0 ++ ((h0 :: t0).set 0 0).drop 1) (Ps b 0 ++ ((p0 :: q0).set 0 1).drop 1) =
      VR S ((h0 :: t0).set 0 0) ((p0 :: q0).set 0 1) := by simp [Hs, HF, Ps, PF]
  have hrl' := hrl
  rw [hstart] at hrl'
  have hdH : ((h0 :: t0).drop (n + 1)) = [] := List.drop_eq_nil_of_le (by simp at hH ⊢; omega)
  have hdP : ((p0 :: q0).drop (n + 1)) = [] := List.drop_eq_nil_of_le (by simp at hW ⊢; omega)
  have hdH' : (((h0 :: t0).set 0 0).drop (n + 1)) = [] := List.drop_eq_nil_of_le (by rw [hHL])
  have hdP' : (((p0 :: q0).set 0 1).drop (n + 1)) = [] := List.drop_eq_nil_of_le (by rw [hPL])
  have q5 := seqM_some hrl' hrlret (pexecM_skip mv fu rl.ps rl.vv)
  have q6 := seqM_some w2 rfl q5
  have q7 := seqM_some w1 rfl q6
  have q8 := seqM_some q4 rfl q7
  have q9 := seqM_some q3 rfl q8
  have q10 := seqM_some q2 rfl q9
  have q11' := seqM_some q1 rfl q10
  have q11 := seqM_some q0' rfl q11'
  refine ⟨_, q11, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrlps
  · rw [hrlvv, hdH, hdH', hdP, hdP']
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrlc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at hrln ⊢
    have : rl.ps.mem.length + rl.ps.bs.length = P.length + 10 := by rw [hrlps]; simp [gS_size]
    omega
  · simp at hrlw ⊢; omega

end Proofs.RollingHashExec
