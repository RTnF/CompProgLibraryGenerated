import Proofs.RollingHashExec

namespace Proofs.RollingHashGet
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB Proofs.RollingHashCore Proofs.RollingHashBuild Proofs.RollingHashExec
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den envs M31 vdenM_binary vec_getM)
open Proofs.Mod61Body (M61 u64_lt)
open Proofs.Mul61Body (midOf retOf mul_bounds denote_nat_bin add_hf mul_hf sub_hf)

/-! ### `rolling_hash_get` (nv = 2): cells 0 = l, 1 = r, 2 = m, 3 = m31, 4 = m30, 5 = a, 6 = b, then the multiplication
(7 .. 14), 15 = x, 16 = xu, 17 = xd, 18 = res -/

abbrev ixL (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 0))
abbrev ixR (nv : Nat) : NExpr := .cast u64 (.variable i32 (nv + 1))
abbrev ixD (nv : Nat) : NExpr := .cast u64 (.binary i32 .sub (.variable i32 (nv + 1)) (.variable i32 (nv + 0)))
abbrev aG (nv : Nat) : NStmt := .declare u64 true (.read u64 (.local 0) (ixL nv))
abbrev bG (nv : Nat) : NStmt := .declare u64 true (.read u64 (.local 1) (ixD nv))
abbrev xE (nv : Nat) : NExpr :=
  .binary u64 .sub (.binary u64 .add (.read u64 (.local 0) (ixR nv)) (.binary u64 .mul (.cast u64 (.literal i32 4)) (vu nv 2)))
    (vu nv 14)
abbrev xG (nv : Nat) : NStmt := .declare u64 true (xE nv)
abbrev progG (nv : Nat) : Command :=
  .sequence (.primitive (.declare u64 true mE)) (.sequence (.primitive (.declare u64 true m31E))
  (.sequence (.primitive (.declare u64 true m30E)) (.sequence (.primitive (aG nv)) (.sequence (.primitive (bG nv))
  (coreCmd nv 5 6 3 4 7 (.sequence (.primitive (xG nv)) (tailCmd nv 15 2 16
    (.sequence (.primitive (.ret (vu nv 18))) Sk))))))))

theorem body_eqG : Proofs.RollingHashInstance.RollingHash_int_hash_2.body = progG 2 := rfl

/-- The contents of the vectors `hs`, `pw`. -/
def VG (HS PW : List Nat) : Nat → List Int := fun k =>
  if k = 0 then HS.map (fun x : Nat => (x : Int)) else if k = 1 then PW.map (fun x : Nat => (x : Int)) else []

theorem VG_get0 (HS PW : List Nat) : VG HS PW 0 = HS.map (fun x : Nat => (x : Int)) := by simp [VG]
theorem VG_get1 (HS PW : List Nat) : VG HS PW 1 = PW.map (fun x : Nat => (x : Int)) := by simp [VG]

theorem getD_lt (S : List Nat) (j : Nat) (h : j < S.length) (hS : ∀ x ∈ S, x < 2^61) : S.getD j 0 < 2^61 := by
  have : S.getD j 0 = S[j] := by simp [List.getD_eq_getElem?_getD, h]
  rw [this]; exact hS _ (List.getElem_mem _)

theorem sub_den (env : Nat → Ty → Option Int) (k1 k0 r l : Nat) (h1 : env k1 i32 = some (r : Int)) (h0 : env k0 i32 = some (l : Int))
    (hl : l ≤ r) (hr : r < 2147483648) :
    (NExpr.cast u64 (.binary i32 .sub (.variable i32 k1) (.variable i32 k0))).denote env = some ((r - l : Nat) : Int) := by
  rw [den_cast, den_binary, den_variable, h1, Option.bind_some, den_variable, h0, Option.bind_some]
  have e : binaryValue .sub (r : Int) (l : Int) = ((r - l : Nat) : Int) := by
    show (r : Int) - l = _; omega
  rw [e, conv_signed i32 rfl rfl _ (validN _ (by omega)), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)

theorem four_value (env : Nat → Ty → Option Int) : (NExpr.cast u64 (.literal i32 4)).denote env = some 4 := by
  have a : i32.valid 4 = true := by simp [Ty.valid]
  have b : u64.valid 4 = true := by simp [Ty.valid]
  simp [NExpr.denote, a, Ty.convert_of_valid _ _ b]

theorem x_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (h rv : Nat) (hh : h < 2^61)
    (hrv : rv ≤ 9223372030412324861)
    (hrd : vdenM mv vv env (.read u64 (.local 0) (ixR mv.nv)) = some (h : Int))
    (E2 : env (mv.nv + 2) u64 = some (M61 : Int)) (E14 : env (mv.nv + 14) u64 = some (rv : Int)) :
    vdenM mv vv env (xE mv.nv) = some ((h + 4 * M61 - rv : Nat) : Int) := by
  have hM : M61 = 2^61 - 1 := rfl
  have mulpart : (NExpr.binary u64 .mul (.cast u64 (.literal i32 4)) (vu mv.nv 2)).denote env = some ((4 * M61 : Nat) : Int) :=
    denote_nat_bin env .mul (fun a b => a * b) mul_hf _ _ 4 M61 (four_value env) (by rw [show vu mv.nv 2 = NExpr.variable u64 (mv.nv + 2) from rfl, den_variable]; exact E2)
      (by omega)
  have hs1 : (NExpr.binary u64 .add (.read u64 (.local 0) (ixR mv.nv))
      (.binary u64 .mul (.cast u64 (.literal i32 4)) (vu mv.nv 2))).scalarOnly = false := by
    simp [NExpr.scalarOnly]
  rw [vdenM_binary _ _ _ _ _ _ _ (by simp [NExpr.scalarOnly]), vdenM_binary _ _ _ _ _ _ _ (by simp [NExpr.scalarOnly]), hrd,
    Option.bind_some, vdenM_scalar _ _ _ _ (by simp [NExpr.scalarOnly]), mulpart, Option.bind_some]
  have e1 : binaryValue .add (h : Int) ((4 * M61 : Nat) : Int) = ((h + 4 * M61 : Nat) : Int) := by
    show _ + _ = _; push_cast; rfl
  rw [e1, Ty.convert_of_valid _ _ (u64_lt _ (by omega)), Option.bind_some,
    vdenM_scalar _ _ _ _ (by simp [NExpr.scalarOnly]), show vu mv.nv 14 = NExpr.variable u64 (mv.nv + 14) from rfl, den_variable, E14,
    Option.bind_some]
  have e2 : binaryValue .sub ((h + 4 * M61 : Nat) : Int) (rv : Int) = ((h + 4 * M61 - rv : Nat) : Int) := by
    show _ - _ = _; omega
  rw [e2]
  exact Ty.convert_of_valid _ _ (u64_lt _ (by omega))


set_option maxHeartbeats 8000000 in
/-- The whole body of `rolling_hash_get`. -/
theorem get_exec (mv : MV) (hnv : mv.nv = 2) (hty0 : mv.ty 0 = u64) (hty1 : mv.ty 1 = u64) (fu : Nat) (P : List Cell)
    (HS PW : List Nat) (l r : Nat) (hl : l ≤ r) (hr : r < HS.length) (hlr : r - l < PW.length) (hr31 : r < 2147483648)
    (hHS : ∀ x ∈ HS, x < 2^61) (hPW : ∀ x ∈ PW, x < 2^61) :
    ∃ rr : PRM, pexecM mv fu (progG mv.nv) (gS P [ci l, ci r]) (VG HS PW) = some rr ∧
      rr.ret = some ((((HS.getD r 0) + 4 * M61 - retOf (HS.getD l 0) (PW.getD (r - l) 0)) % M61 : Nat) : Int) ∧
      (∃ L, rr.ps = gS P ([ci l, ci r] ++ L)) ∧ rr.vv = VG HS PW ∧ rr.cost ≤ 1000 ∧ rr.need ≤ P.length + 105 ∧ rr.wk = 0 := by
  have hM : M61 < 18446744073709551616 := by unfold M61; omega
  have hlM : l < 2147483648 := by omega
  have hlH : l < HS.length := by omega
  obtain ⟨a, ha⟩ : ∃ a, a = HS.getD l 0 := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb, bb = PW.getD (r - l) 0 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = HS.getD r 0 := ⟨_, rfl⟩
  have haL : a < 2^61 := by rw [ha]; exact getD_lt HS l hlH hHS
  have hbL : bb < 2^61 := by rw [hbb]; exact getD_lt PW _ hlr hPW
  have hhL : h < 2^61 := by rw [hh]; exact getD_lt HS r hr hHS
  have hrd0 : (VG HS PW 0)[l]? = some (a : Int) := by rw [VG_get0, vec_getM HS l hlH, ← ha]
  have hrd1 : (VG HS PW 1)[r - l]? = some (bb : Int) := by rw [VG_get1, vec_getM PW _ hlr, ← hbb]
  have hrdr : (VG HS PW 0)[r]? = some (h : Int) := by rw [VG_get0, vec_getM HS r hr, ← hh]
  -- m, m31, m30
  have e1 : vdenM mv (VG HS PW) (penvN mv.nv (gS P [ci l, ci r])) mE = some (M61 : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact mE_val _
  have d1 := gSM_decl mv P [ci l, ci r] (VG HS PW) u64 mE _ _ e1 (Ty.convert_of_valid _ _ (u64_lt M61 hM))
  have q1 := (pexecM_prim mv fu (.declare u64 true mE) _ _).trans d1
  have e2 : vdenM mv (VG HS PW) (penvN mv.nv (gS P [ci l, ci r, cu M61])) m31E = some (2147483647 : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact m31_val _
  have d2 := gSM_decl mv P [ci l, ci r, cu M61] (VG HS PW) u64 m31E _ _ e2 (Ty.convert_of_valid _ _ (u64_lt 2147483647 (by omega)))
  have q2 := (pexecM_prim mv fu (.declare u64 true m31E) _ _).trans d2
  have e3 : vdenM mv (VG HS PW) (penvN mv.nv (gS P [ci l, ci r, cu M61, cu 2147483647])) m30E = some (1073741823 : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]; exact m30_val _
  have d3 := gSM_decl mv P [ci l, ci r, cu M61, cu 2147483647] (VG HS PW) u64 m30E _ _ e3
    (Ty.convert_of_valid _ _ (u64_lt 1073741823 (by omega)))
  have q3 := (pexecM_prim mv fu (.declare u64 true m30E) _ _).trans d3
  -- a = hs[l]
  have E0 := envs mv P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823] 0 (ci l) rfl (validN l hlM)
  have E1 := envs mv P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823] 1 (ci r) rfl (validN r hr31)
  have va := rdM_val mv (VG HS PW) (penvN mv.nv (gS P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823])) 0 (by omega) u64 hty0.symm
    (ixL mv.nv) rfl rfl l (cidx_den _ (mv.nv + 0) l E0 (by exact hlM)) (a : Int) hrd0 (by rw [hty0]; exact u64_lt a (by omega))
  have d4 := gSM_decl mv P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823] (VG HS PW) u64 _ _ _ va
    (Ty.convert_of_valid _ _ (u64_lt a (by omega)))
  have q4 := (pexecM_prim mv fu (aG mv.nv) _ _).trans d4
  -- b = pw[r - l]
  have E0' := envs mv P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a] 0 (ci l) rfl (validN l hlM)
  have E1' := envs mv P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a] 1 (ci r) rfl (validN r hr31)
  have vb := rdM_val mv (VG HS PW) (penvN mv.nv (gS P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a])) 1 (by omega) u64
    hty1.symm (ixD mv.nv) rfl rfl (r - l) (sub_den _ (mv.nv + 1) (mv.nv + 0) r l E1' E0' hl hr31) (bb : Int) hrd1
    (by rw [hty1]; exact u64_lt bb (by omega))
  have d5 := gSM_decl mv P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a] (VG HS PW) u64 _ _ _ vb
    (Ty.convert_of_valid _ _ (u64_lt bb (by omega)))
  have q5 := (pexecM_prim mv fu (bG mv.nv) _ _).trans d5
  -- the product, x and the reduction
  obtain ⟨xv, hxv⟩ : ∃ xv, xv = h + 4 * M61 - retOf a bb := ⟨_, rfl⟩
  have hret := retOf_small a bb haL hbL
  have hxlt : xv < 18446744073709551616 := by rw [hxv]; unfold M61; omega
  have L7 : ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] : List Cell).length = 7 := rfl
  have hL' : ∀ t : Nat, ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb)[7 + t]? = (mulCells a bb)[t]? := by
    intro t; exact get_new _ _ t
  have E2c := env_at mv P ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb) 2 M61 rfl hM
  have E14c := env_at mv P ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb) 14 (retOf a bb)
    (by have := hL' 7; simpa [mulCells] using this) (by have := (mul_bounds a bb haL hbL).2.2.2.2.2.2.2; omega)
  have hrdx : vdenM mv (VG HS PW) (penvN mv.nv (gS P ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb)))
      (.read u64 (.local 0) (ixR mv.nv)) = some (h : Int) := by
    have E1x := envs mv P ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb) 1 (ci r) rfl (validN r hr31)
    exact rdM_val mv (VG HS PW) _ 0 (by omega) u64 hty0.symm (ixR mv.nv) rfl rfl r (cidx_den _ (mv.nv + 1) r E1x (by exact hr31)) (h : Int)
      hrdr (by rw [hty0]; exact u64_lt h (by omega))
  have vx := x_val mv (VG HS PW) _ h (retOf a bb) hhL hret hrdx E2c E14c
  rw [← hxv] at vx
  have dx := gSM_decl mv P ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb) (VG HS PW) u64 _ _ _ vx
    (Ty.convert_of_valid _ _ (u64_lt xv hxlt))
  have qx := (pexecM_prim mv fu (xG mv.nv) _ _).trans dx
  -- ret
  have hretv : vdenM mv (VG HS PW) (penvN mv.nv (gS P ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb ++ [cu xv] ++
      [cu (xv / 2^61), cu (xv % 2^61), cu (xv % M61)]))) (vu mv.nv 18) = some ((xv % M61 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, show vu mv.nv 18 = NExpr.variable u64 (mv.nv + 18) from rfl, den_variable]
    exact env_at mv P _ 18 (xv % M61) (by
      have : 18 = ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb ++ [cu xv]).length + 2 := by
        simp [mulCells]
      rw [this]; exact at_new _ _ 2 _ rfl) (by have := Nat.mod_lt xv (show 0 < M61 by unfold M61; omega); omega)
  have rt := pstmtM_ret_ok mv _ (VG HS PW) _ _ hretv
  have rk := seqM_ret (b := Sk) ((pexecM_prim mv fu (.ret (vu mv.nv 18)) _ _).trans rt) rfl
  have hL16 : ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb ++ [cu xv] : List Cell).length = 16 := by
    simp [mulCells]
  have hLx : ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb ++ [cu xv] : List Cell)[15]? = some (cu xv) := by
    have : 15 = ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb).length + 0 := by simp [mulCells]
    rw [this]; exact at_new ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb) [cu xv] 0 (cu xv) rfl
  have hLm : ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb ++ [cu xv] : List Cell)[2]? = some (cu M61) := by
    simp [mulCells]
  have tc := tail_core mv trivial fu P ([ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb ++ [cu xv])
    (VG HS PW) 15 2 xv hxlt hLx hLm (.sequence (.primitive (.ret (vu mv.nv 18))) Sk) _ rk
  obtain ⟨rt', hrt, hrtret, hrtps, hrtvv, hrtc, hrtn, hrtw⟩ := tc
  rw [hL16] at hrt
  have hx2 := seqM_some qx rfl hrt
  have mc := mul_core mv fu P [ci l, ci r, cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] (VG HS PW) 5 6 3 4 a bb haL hbL rfl rfl rfl rfl
    (.sequence (.primitive (xG mv.nv)) (tailCmd mv.nv 15 2 16 (.sequence (.primitive (.ret (vu mv.nv 18))) Sk))) _ hx2
  obtain ⟨rm, hrm, hrmret, hrmps, hrmvv, hrmc, hrmn, hrmw⟩ := mc
  rw [L7] at hrm
  have fin := seqM_some q1 rfl (seqM_some q2 rfl (seqM_some q3 rfl (seqM_some q4 rfl (seqM_some q5 rfl hrm))))
  rw [← hh, ← ha, ← hbb, ← hxv]
  refine ⟨_, fin, hrmret.trans hrtret, ⟨[cu M61, cu 2147483647, cu 1073741823, cu a, cu bb] ++ mulCells a bb ++ [cu xv] ++
    [cu (xv / 2^61), cu (xv % 2^61), cu (xv % M61)], by rw [hrmps, hrtps]; simp⟩, hrmvv.trans hrtvv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hrmc hrtc ⊢
    omega
  · simp only [gS_size] at hrmn hrtn
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, mulCells] at hrmn hrtn ⊢
    omega
  · simp at hrmw hrtw ⊢
    omega

end Proofs.RollingHashGet
