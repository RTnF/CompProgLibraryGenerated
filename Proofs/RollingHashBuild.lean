import Proofs.RollingHashCore
import Proofs.BellmanFordExec
import Proofs.Generated.RollingHash

namespace Proofs.RollingHashBuild
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB Proofs.RollingHashCore
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)

/-! ### `rolling_hash_build` (nv = 3): cells 0 = b, 1 = m, 2 = m31, 3 = m30, 4 = n, 5 = i, then the block locals
(6 = a, 7 = au, ..., 14 = mulv, 15 = x, 16 = xu, 17 = xd, 18 = res) -/

abbrev ixc (nv c : Nat) : NExpr := .cast u64 (.variable i32 (nv + c))
abbrev mE : NExpr := .binary u64 .sub (.binary u64 .mul (.literal u64 1) (.literal u64 2305843009213693952)) (.cast u64 (.literal i32 1))
abbrev m31E : NExpr := .binary u64 .sub (.binary u64 .mul (.literal u64 1) (.literal u64 2147483648)) (.cast u64 (.literal i32 1))
abbrev m30E : NExpr := .binary u64 .sub (.binary u64 .mul (.literal u64 1) (.literal u64 1073741824)) (.cast u64 (.literal i32 1))
-- block 1: hs
abbrev aS1 (nv : Nat) : NStmt := .declare u64 true (.read u64 (.local 0) (ixc nv 5))
abbrev xS1 (nv : Nat) : NStmt :=
  .declare u64 true (.binary u64 .add (vu nv 14) (.cast u64 (.read i32 (.local 2) (ixc nv 5))))
abbrev wS1 (nv : Nat) : NStmt :=
  .write (.local 0) u64 (.cast u64 (.binary i32 .add (.variable i32 (nv + 5)) (.literal i32 1))) (vu nv 18)
abbrev blk1 (nv : Nat) : Command :=
  .sequence (.primitive (aS1 nv)) (coreCmd nv 6 0 2 3 7 (.sequence (.primitive (xS1 nv))
    (tailCmd nv 15 1 16 (.sequence (.primitive (wS1 nv)) Sk))))
-- block 2: pw
abbrev aS2 (nv : Nat) : NStmt := .declare u64 true (.read u64 (.local 1) (ixc nv 5))
abbrev xS2 (nv : Nat) : NStmt := .declare u64 true (vu nv 14)
abbrev wS2 (nv : Nat) : NStmt :=
  .write (.local 1) u64 (.cast u64 (.binary i32 .add (.variable i32 (nv + 5)) (.literal i32 1))) (vu nv 18)
abbrev blk2 (nv : Nat) : Command :=
  .sequence (.primitive (aS2 nv)) (coreCmd nv 6 0 2 3 7 (.sequence (.primitive (xS2 nv))
    (tailCmd nv 15 1 16 (.sequence (.primitive (wS2 nv)) Sk))))
abbrev bodyB (nv : Nat) : Command := .sequence (.scope (blk1 nv)) (.sequence (.scope (blk2 nv)) Sk)
abbrev bDecl : NStmt := .declare u64 true (.cast u64 (.literal i32 131))
abbrev progB (nv : Nat) : Command :=
  .sequence (.primitive bDecl) (.sequence (.primitive (.declare u64 true mE)) (.sequence (.primitive (.declare u64 true m31E))
  (.sequence (.primitive (.declare u64 true m30E))
  (.sequence (.primitive (.declare i32 true (.cast i32 (.size (.integer i32) (.local 2)))))
  (.sequence (.primitive (.write (.local 0) u64 (.cast u64 (.literal i32 0)) (.cast u64 (.literal i32 0))))
  (.sequence (.primitive (.write (.local 1) u64 (.cast u64 (.literal i32 0)) (.cast u64 (.literal i32 1))))
  (.sequence (forStmtB nv 5 4 (bodyB nv)) Sk)))))))

theorem body_eqRB : Proofs.RollingHashInstance.RollingHash_int_new0.body = progB 3 := rfl


open Proofs.BellmanFordExec (rdM_val cidx_den envs M31 i32_valid_nat vdenM_binary)
open Proofs.Mod61Body (M61 u64_lt res_final)
open Proofs.Mul61Body (midOf retOf mul_bounds)

/-- The contents of the three vectors `s` (`int`), `hs`, `pw` (`unsigned long long`). -/
def VR (S HS PW : List Nat) : Nat → List Int := fun k =>
  if k = 0 then HS.map (fun x : Nat => (x : Int)) else if k = 1 then PW.map (fun x : Nat => (x : Int))
  else if k = 2 then S.map (fun x : Nat => (x : Int)) else []

theorem VR_get2 (S HS PW) : VR S HS PW 2 = S.map (fun x : Nat => (x : Int)) := by simp [VR]
theorem VR_get0 (S HS PW) : VR S HS PW 0 = HS.map (fun x : Nat => (x : Int)) := by simp [VR]
theorem VR_get1 (S HS PW) : VR S HS PW 1 = PW.map (fun x : Nat => (x : Int)) := by simp [VR]

theorem VR_write0 (S HS PW : List Nat) (p x : Nat) :
    upd (VR S HS PW) 0 ((VR S HS PW 0).set p (x : Int)) = VR S (HS.set p x) PW := by
  funext k
  unfold upd VR
  by_cases h1 : k = 0
  · subst h1; simp [List.map_set]
  · simp [h1]

theorem VR_write1 (S HS PW : List Nat) (p x : Nat) :
    upd (VR S HS PW) 1 ((VR S HS PW 1).set p (x : Int)) = VR S HS (PW.set p x) := by
  funext k
  unfold upd VR
  by_cases h2 : k = 1
  · subst h2; simp [List.map_set]
  · simp [h2]

theorem natGet (l : List Nat) (j : Nat) (h : j < l.length) :
    (l.map (fun x : Nat => (x : Int)))[j]? = some ((l.getD j 0 : Nat) : Int) := by
  simp [List.getElem?_map, h, List.getD_eq_getElem?_getD]


abbrev aSk (nv kv : Nat) : NStmt := .declare u64 true (.read u64 (.local kv) (ixc nv 5))
abbrev wSk (nv kv : Nat) : NStmt :=
  .write (.local kv) u64 (.cast u64 (.binary i32 .add (.variable i32 (nv + 5)) (.literal i32 1))) (vu nv 18)
abbrev blkCmd (nv kv : Nat) (xS : NStmt) : Command :=
  .sequence (.primitive (aSk nv kv)) (coreCmd nv 6 0 2 3 7 (.sequence (.primitive xS)
    (tailCmd nv 15 1 16 (.sequence (.primitive (wSk nv kv)) Sk))))

theorem blk1_eq (nv : Nat) : blk1 nv = blkCmd nv 0 (xS1 nv) := rfl
theorem blk2_eq (nv : Nat) : blk2 nv = blkCmd nv 1 (xS2 nv) := rfl

theorem succ_den (env : Nat → Ty → Option Int) (k x : Nat) (h : env k i32 = some (x : Int)) (hx : x + 1 < 2147483648) :
    (NExpr.cast u64 (.binary i32 .add (.variable i32 k) (.literal i32 1))).denote env = some ((x + 1 : Nat) : Int) := by
  have one : (NExpr.literal i32 1).denote env = some 1 := by
    rw [den_literal, if_pos (show i32.valid 1 = true from rfl)]
  rw [den_cast, den_binary, den_variable, h, Option.bind_some, one, Option.bind_some]
  have e : binaryValue .add (x : Int) 1 = ((x + 1 : Nat) : Int) := by
    show (x : Int) + 1 = _; push_cast; rfl
  rw [e, conv_signed i32 rfl rfl _ (validN _ hx), Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)

set_option maxHeartbeats 8000000 in
/-- One block: `a = v[i]; ...; v[i + 1] = (mul61(a, b) + add) mod m` (the `x` statement is a parameter). -/
theorem blk_exec (mv : MV) (hnv : mv.nv = 3) (kv : Nat) (hkv : kv < 3) (htyk : mv.ty kv = u64) (fu : Nat)
    (P C : List Cell) (vv : Nat → List Int) (xS : NStmt) (b i a xv : Nat)
    (hC : C.length = 6) (hb : b < 2^61) (ha : a < 2^61) (hi : i < 2147483647) (hxv : xv < 18446744073709551616)
    (h0 : C[0]? = some (cu b)) (h1 : C[1]? = some (cu M61)) (h2 : C[2]? = some (cu 2147483647))
    (h3 : C[3]? = some (cu 1073741823)) (h5 : C[5]? = some (ci i))
    (hread : (vv kv)[i]? = some (a : Int)) (hlt : i + 1 < (vv kv).length)
    (hx : ∃ rx : PRM, pexecM mv fu (.primitive xS) (gS P (C ++ [cu a] ++ mulCells a b)) vv = some rx ∧
      rx.ret = none ∧ rx.ps = gS P (C ++ [cu a] ++ mulCells a b ++ [cu xv]) ∧ rx.vv = vv ∧ rx.cost ≤ 100 ∧
      rx.need ≤ P.length + 70 ∧ rx.wk = 0) :
    ∃ r : PRM, pexecM mv fu (blkCmd mv.nv kv xS) (gS P C) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C ++ [cu a, cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30),
        cu (midOf a b % 2^30), cu (retOf a b), cu xv, cu (xv / 2^61), cu (xv % 2^61), cu (xv % M61)]) ∧
      r.vv = upd vv kv ((vv kv).set (i + 1) ((xv % M61 : Nat) : Int)) ∧
      r.cost ≤ 1000 ∧ r.need ≤ P.length + 102 ∧ r.wk ≤ 1 := by
  have hnM : i < 2147483648 := by omega
  have a64 : a < 18446744073709551616 := by omega
  have b64 : b < 18446744073709551616 := by omega
  have hC0 : 0 < C.length := by omega
  have hCa : ∀ k, k < 6 → ∀ e : List Cell, (C ++ e)[k]? = C[k]? := fun k hk e => by
    rw [List.getElem?_append_left (by omega)]
  -- declaration of a
  have E5 := envs mv P C 5 (ci i) h5 (validN i hnM)
  have va := rdM_val mv vv (penvN mv.nv (gS P C)) kv (by omega) u64 htyk.symm (ixc mv.nv 5) rfl rfl i
    (cidx_den _ (mv.nv + 5) i E5 (by omega)) (a : Int) hread (by rw [htyk]; exact u64_lt a a64)
  have d0 := gSM_decl mv P C vv u64 _ _ _ va (Ty.convert_of_valid u64 _ (u64_lt a a64))
  have qa := (pexecM_prim mv fu (aSk mv.nv kv) _ _).trans d0
  -- the multiplication core
  have hL1len : (C ++ [cu a]).length = 7 := by simp [hC]
  have hLa : (C ++ [cu a])[6]? = some (cu a) := by
    rw [List.getElem?_append_right (by omega)]; simp [hC]
  have hLb : (C ++ [cu a])[0]? = some (cu b) := by rw [hCa 0 (by omega) _]; exact h0
  have hL31 : (C ++ [cu a])[2]? = some (cu 2147483647) := by rw [hCa 2 (by omega) _]; exact h2
  have hL30 : (C ++ [cu a])[3]? = some (cu 1073741823) := by rw [hCa 3 (by omega) _]; exact h3
  -- the final write at the end of the block
  have hmod : xv % M61 < 18446744073709551616 := by unfold M61; omega
  have hE : C ++ [cu a] ++ mulCells a b ++ [cu xv] ++ [cu (xv / 2^61), cu (xv % 2^61), cu (xv % M61)] =
      C ++ [cu a, cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b), cu (midOf a b / 2^30),
        cu (midOf a b % 2^30), cu (retOf a b), cu xv, cu (xv / 2^61), cu (xv % 2^61), cu (xv % M61)] := by
    simp [mulCells]
  have E5' := envs mv P (C ++ [cu a, cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b),
    cu (midOf a b / 2^30), cu (midOf a b % 2^30), cu (retOf a b), cu xv, cu (xv / 2^61), cu (xv % 2^61), cu (xv % M61)]) 5 (ci i)
    (by rw [hCa 5 (by omega) _]; exact h5) (validN i hnM)
  have hp : vdenM mv vv (penvN mv.nv (gS P (C ++ [cu a, cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31),
      cu (midOf a b), cu (midOf a b / 2^30), cu (midOf a b % 2^30), cu (retOf a b), cu xv, cu (xv / 2^61), cu (xv % 2^61),
      cu (xv % M61)]))) (.cast u64 (.binary i32 .add (.variable i32 (mv.nv + 5)) (.literal i32 1))) = some ((i + 1 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact succ_den _ (mv.nv + 5) i E5' (by omega)
  have hres := env_at mv P (C ++ [cu a, cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31), cu (midOf a b),
    cu (midOf a b / 2^30), cu (midOf a b % 2^30), cu (retOf a b), cu xv, cu (xv / 2^61), cu (xv % 2^61), cu (xv % M61)]) 18 (xv % M61)
    (by have : 18 = C.length + 12 := by omega
        rw [this]; exact at_new C _ 12 _ rfl) hmod
  have hxe : vdenM mv vv (penvN mv.nv (gS P (C ++ [cu a, cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31),
      cu (midOf a b), cu (midOf a b / 2^30), cu (midOf a b % 2^30), cu (retOf a b), cu xv, cu (xv / 2^61), cu (xv % 2^61),
      cu (xv % M61)]))) (vu mv.nv 18) = some ((xv % M61 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, show vu mv.nv 18 = NExpr.variable u64 (mv.nv + 18) from rfl, den_variable]
    exact hres
  have wr := pstmtM_write_ok mv (gS P (C ++ [cu a, cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31),
      cu (midOf a b), cu (midOf a b / 2^30), cu (midOf a b % 2^30), cu (retOf a b), cu xv, cu (xv / 2^61), cu (xv % 2^61),
      cu (xv % M61)])) vv kv (by omega) _ _ ((xv % M61 : Nat) : Int) (i + 1) hxe hp (by omega) (by rw [htyk]; exact u64_lt _ hmod)
  rw [htyk] at wr
  have w1 := (pexecM_prim mv fu (wSk mv.nv kv) _ _).trans wr
  have w2 := seqM_some w1 rfl (pexecM_skip mv fu _ _)
  rw [← hE] at w2
  -- the reduction
  have hL10 : C ++ [cu a] ++ mulCells a b ++ [cu xv] = C ++ [cu a, cu (a / 2^31), cu (a % 2^31), cu (b / 2^31), cu (b % 2^31),
      cu (midOf a b), cu (midOf a b / 2^30), cu (midOf a b % 2^30), cu (retOf a b), cu xv] := by simp [mulCells]
  have hlen16 : (C ++ [cu a] ++ mulCells a b ++ [cu xv]).length = 16 := by simp [hC, mulCells]
  have hx15 : (C ++ [cu a] ++ mulCells a b ++ [cu xv])[15]? = some (cu xv) := by
    rw [hL10]
    have : 15 = C.length + 9 := by omega
    rw [this]; exact at_new C _ 9 _ rfl
  have hm1 : (C ++ [cu a] ++ mulCells a b ++ [cu xv])[1]? = some (cu M61) := by
    rw [hL10, hCa 1 (by omega) _]; exact h1
  have tc := tail_core mv trivial fu P (C ++ [cu a] ++ mulCells a b ++ [cu xv]) vv 15 1 xv hxv hx15 hm1
    (.sequence (.primitive (wSk mv.nv kv)) Sk) _ w2
  obtain ⟨rt, hrt, hrtret, hrtps, hrtvv, hrtc, hrtn, hrtw⟩ := tc
  rw [hlen16] at hrt
  obtain ⟨rx, hrx, hrxret, hrxps, hrxvv, hrxc, hrxn, hrxw⟩ := hx
  have hx2 := seqM_some hrx hrxret (by rw [hrxps, hrxvv]; exact hrt)
  have mc := mul_core mv fu P (C ++ [cu a]) vv 6 0 2 3 a b ha hb hLa hLb hL31 hL30
    (.sequence (.primitive xS) (tailCmd mv.nv 15 1 16 (.sequence (.primitive (wSk mv.nv kv)) Sk))) _ hx2
  obtain ⟨rm, hrm, hrmret, hrmps, hrmvv, hrmc, hrmn, hrmw⟩ := mc
  rw [hL1len] at hrm
  have fin := seqM_some qa rfl hrm
  refine ⟨_, fin, hrmret.trans hrtret, hrmps.trans (hrtps.trans (congrArg (gS P) hE)), hrmvv.trans hrtvv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hrmc hrtc hrtn ⊢
    omega
  · simp only [gS_size] at hrmn hrtn
    simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, hC, mulCells] at hrmn hrtn ⊢
    omega
  · simp at hrmw hrtw ⊢
    omega


theorem castRead_val (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (idx : NExpr) (s : Nat)
    (hs : idx.scalarOnly = true) (hrd : vdenM mv vv env (.read i32 (.local 2) idx) = some (s : Int)) (hlt : s < 18446744073709551616) :
    vdenM mv vv env (.cast u64 (.read i32 (.local 2) idx)) = some (s : Int) := by
  have hr2 : (NExpr.cast u64 (.read i32 (.local 2) idx)).scalarOnly = false := by
    simp [NExpr.scalarOnly, hs]
  rw [vdenM, if_neg (by rw [hr2]; decide), hrd, Option.bind_some, convert_u64]
  congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)

/-- `x = mulv + (unsigned long long)s[i]` -/
theorem x1_exec (mv : MV) (hnv : mv.nv = 3) (hty2 : mv.ty 2 = i32) (fu : Nat) (P C : List Cell) (vv : Nat → List Int)
    (a b i s0 : Nat) (hC : C.length = 6) (ha : a < 2^61) (hb : b < 2^61) (h5 : C[5]? = some (ci i)) (hi : i < 2147483648)
    (hrd : (vv 2)[i]? = some (s0 : Int)) (hs0 : s0 < 2147483648) :
    ∃ rx : PRM, pexecM mv fu (.primitive (xS1 mv.nv)) (gS P (C ++ [cu a] ++ mulCells a b)) vv = some rx ∧
      rx.ret = none ∧ rx.ps = gS P (C ++ [cu a] ++ mulCells a b ++ [cu (retOf a b + s0)]) ∧ rx.vv = vv ∧ rx.cost ≤ 100 ∧
      rx.need ≤ P.length + 70 ∧ rx.wk = 0 := by
  obtain ⟨bd1, bd2, bd3, bd4, bd5, bd6, bd7, bd8⟩ := mul_bounds a b ha hb
  have hsum : retOf a b + s0 < 18446744073709551616 := by
    have h63 := retOf_small a b ha hb
    omega
  have hcell : ∀ e : List Cell, (C ++ e)[5]? = some (ci i) := fun e => by
    rw [List.getElem?_append_left (by omega)]; exact h5
  have E5 := envs mv P (C ++ [cu a] ++ mulCells a b) 5 (ci i) (by
    rw [List.append_assoc]; exact hcell _) (validN i hi)
  have E14 : penvN mv.nv (gS P (C ++ [cu a] ++ mulCells a b)) (mv.nv + 14) u64 = some ((retOf a b : Nat) : Int) :=
    env_at mv P (C ++ [cu a] ++ mulCells a b) 14 (retOf a b) (by
      have : 14 = C.length + 8 := by omega
      rw [this, List.append_assoc]; exact at_new C _ 8 _ rfl) (by omega)
  have rd := rdM_val mv vv (penvN mv.nv (gS P (C ++ [cu a] ++ mulCells a b))) 2 (by omega) i32 hty2.symm (ixc mv.nv 5) rfl rfl i
    (cidx_den _ (mv.nv + 5) i E5 (by omega)) (s0 : Int) hrd (by rw [hty2]; exact validN s0 hs0)
  have cr := castRead_val mv vv (penvN mv.nv (gS P (C ++ [cu a] ++ mulCells a b))) (ixc mv.nv 5) s0 rfl rd (by omega)
  have vx : vdenM mv vv (penvN mv.nv (gS P (C ++ [cu a] ++ mulCells a b)))
      (.binary u64 .add (vu mv.nv 14) (.cast u64 (.read i32 (.local 2) (ixc mv.nv 5)))) = some ((retOf a b + s0 : Nat) : Int) := by
    rw [vdenM_binary _ _ _ _ _ _ _ (by simp [NExpr.scalarOnly]), vdenM_scalar _ _ _ _ rfl, show vu mv.nv 14 = NExpr.variable u64 (mv.nv + 14) from rfl,
      den_variable, E14, Option.bind_some, cr, Option.bind_some]
    have : binaryValue .add ((retOf a b : Nat) : Int) (s0 : Int) = ((retOf a b + s0 : Nat) : Int) := by
      show _ + _ = _; push_cast; rfl
    rw [this]
    exact Ty.convert_of_valid _ _ (u64_lt _ hsum)
  have d := gSM_decl mv P (C ++ [cu a] ++ mulCells a b) vv u64 _ _ _ vx (Ty.convert_of_valid _ _ (u64_lt _ hsum))
  have q := (pexecM_prim mv fu (xS1 mv.nv) _ _).trans d
  refine ⟨_, q, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, hC, mulCells]


/-- `x = mulv` -/
theorem x2_exec (mv : MV) (hnv : mv.nv = 3) (fu : Nat) (P C : List Cell) (vv : Nat → List Int)
    (a b : Nat) (hC : C.length = 6) (ha : a < 2^61) (hb : b < 2^61) :
    ∃ rx : PRM, pexecM mv fu (.primitive (xS2 mv.nv)) (gS P (C ++ [cu a] ++ mulCells a b)) vv = some rx ∧
      rx.ret = none ∧ rx.ps = gS P (C ++ [cu a] ++ mulCells a b ++ [cu (retOf a b)]) ∧ rx.vv = vv ∧ rx.cost ≤ 100 ∧
      rx.need ≤ P.length + 70 ∧ rx.wk = 0 := by
  have h63 := retOf_small a b ha hb
  have E14 : penvN mv.nv (gS P (C ++ [cu a] ++ mulCells a b)) (mv.nv + 14) u64 = some ((retOf a b : Nat) : Int) :=
    env_at mv P (C ++ [cu a] ++ mulCells a b) 14 (retOf a b) (by
      have : 14 = C.length + 8 := by omega
      rw [this, List.append_assoc]; exact at_new C _ 8 _ rfl) (by omega)
  have d := decl_u64 mv fu P (C ++ [cu a] ++ mulCells a b) vv (vu mv.nv 14) (retOf a b) rfl
    (by rw [show vu mv.nv 14 = NExpr.variable u64 (mv.nv + 14) from rfl, den_variable]; exact E14) (by omega)
  refine ⟨_, d, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, hC, mulCells]


/-- The hash recurrence `H(t + 1) = (H t * b + s[t]) mod (2^61 - 1)`. -/
def HF (b : Nat) (S : List Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => (retOf (HF b S t) b + S.getD t 0) % M61

/-- The power recurrence `P(t + 1) = P t * b mod (2^61 - 1)`. -/
def PF (b : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => (retOf (PF b t) b) % M61

theorem HF_lt (b : Nat) (S : List Nat) (t : Nat) : HF b S t < 2^61 := by
  cases t with
  | zero => simp [HF]
  | succ t =>
    show (retOf (HF b S t) b + S.getD t 0) % M61 < 2^61
    have h1 := Nat.mod_lt (retOf (HF b S t) b + S.getD t 0) (show 0 < M61 by unfold M61; omega)
    have h2 : M61 < 2^61 := by unfold M61; omega
    omega

theorem PF_lt (b : Nat) (t : Nat) : PF b t < 2^61 := by
  cases t with
  | zero => simp [PF]
  | succ t =>
    show (retOf (PF b t) b) % M61 < 2^61
    have h1 := Nat.mod_lt (retOf (PF b t) b) (show 0 < M61 by unfold M61; omega)
    have h2 : M61 < 2^61 := by unfold M61; omega
    omega

def Hs (b : Nat) (S : List Nat) (t : Nat) : List Nat := (List.range (t + 1)).map (HF b S)
def Ps (b : Nat) (t : Nat) : List Nat := (List.range (t + 1)).map (PF b)

theorem Hs_len (b : Nat) (S : List Nat) (t : Nat) : (Hs b S t).length = t + 1 := by simp [Hs]
theorem Ps_len (b : Nat) (t : Nat) : (Ps b t).length = t + 1 := by simp [Ps]
theorem Hs_succ (b : Nat) (S : List Nat) (t : Nat) : Hs b S (t + 1) = Hs b S t ++ [HF b S (t + 1)] := by
  unfold Hs; rw [List.range_succ, List.map_append]; rfl
theorem Ps_succ (b : Nat) (t : Nat) : Ps b (t + 1) = Ps b t ++ [PF b (t + 1)] := by
  unfold Ps; rw [List.range_succ, List.map_append]; rfl
theorem Hs_get (b : Nat) (S : List Nat) (t : Nat) : (Hs b S t).getD t 0 = HF b S t := by
  simp [Hs, List.getD_eq_getElem?_getD]
theorem Ps_get (b : Nat) (t : Nat) : (Ps b t).getD t 0 = PF b t := by
  simp [Ps, List.getD_eq_getElem?_getD]

theorem set_pad (A O : List Nat) (L t : Nat) (hA : A.length = L) (hL : L < O.length) :
    (A ++ O.drop L).set L t = (A ++ [t]) ++ O.drop (L + 1) := by
  have hd : O.drop L = O[L] :: O.drop (L + 1) := List.drop_eq_getElem_cons hL
  rw [List.set_append_right _ _ (by omega), hA, Nat.sub_self, hd, List.append_assoc]
  rfl


open Proofs.ForLoopC (gS_takeC)

theorem getD_app_left (A B : List Nat) (j : Nat) (h : j < A.length) : (A ++ B).getD j 0 = A.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

abbrev C5 (b n : Nat) : List Cell := [cu b, cu M61, cu 2147483647, cu 1073741823, ci n]

set_option maxHeartbeats 8000000 in
/-- One iteration of the loop: both blocks. -/
theorem body_iter (mv : MV) (hnv : mv.nv = 3) (hty2 : mv.ty 2 = i32) (hty0 : mv.ty 0 = u64) (hty1 : mv.ty 1 = u64)
    (fu : Nat) (P : List Cell) (S HS0 PW0 : List Nat) (b n t : Nat) (hb : b < 2^61) (hn : n < 2147483647) (ht : t < n)
    (hS : S.length = n) (hSv : ∀ x ∈ S, x < 2147483648) (hH : HS0.length = n + 1) (hW : PW0.length = n + 1) :
    ∃ r : PRM, pexecM mv fu (bodyB mv.nv) (gS P (C5 b n ++ [ci t]))
        (VR S (Hs b S t ++ HS0.drop (t + 1)) (Ps b t ++ PW0.drop (t + 1))) = some r ∧ r.ret = none ∧
      r.ps = gS P (C5 b n ++ [ci t]) ∧
      r.vv = VR S (Hs b S (t + 1) ++ HS0.drop (t + 2)) (Ps b (t + 1) ++ PW0.drop (t + 2)) ∧
      r.cost ≤ 2100 ∧ r.need ≤ P.length + 102 ∧ r.wk ≤ 2 := by
  have hnM : n < 2147483648 := by omega
  have hC6 : (C5 b n ++ [ci t]).length = 6 := by simp
  have hSt : S.getD t 0 < 2147483648 := by
    have : S.getD t 0 = S[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, hS, ht]
    rw [this]; exact hSv _ (List.getElem_mem _)
  have hHL : (Hs b S t ++ HS0.drop (t + 1)).length = n + 1 := by simp [Hs_len, List.length_drop]; omega
  have hPL : (Ps b t ++ PW0.drop (t + 1)).length = n + 1 := by simp [Ps_len, List.length_drop]; omega
  have hHF := HF_lt b S t
  have hPF := PF_lt b t
  have hread1 : ((VR S (Hs b S t ++ HS0.drop (t + 1)) (Ps b t ++ PW0.drop (t + 1))) 0)[t]? = some ((HF b S t : Nat) : Int) := by
    rw [VR_get0]
    have h := natGet (Hs b S t ++ HS0.drop (t + 1)) t (by rw [List.length_append, Hs_len]; omega)
    rw [h, getD_app_left _ _ _ (by rw [Hs_len]; omega), Hs_get]
  have hread0 : ((VR S (Hs b S t ++ HS0.drop (t + 1)) (Ps b t ++ PW0.drop (t + 1))) 2)[t]? = some ((S.getD t 0 : Nat) : Int) := by
    rw [VR_get2]; exact natGet S t (by omega)
  -- block 1: hs
  have hx1 := x1_exec mv hnv hty2 fu P (C5 b n ++ [ci t]) (VR S (Hs b S t ++ HS0.drop (t + 1)) (Ps b t ++ PW0.drop (t + 1)))
    (HF b S t) b t (S.getD t 0) hC6 hHF hb (by simp) (by omega) hread0 hSt
  have bl1 := blk_exec mv hnv 0 (by omega) (by rw [hty0]) fu P (C5 b n ++ [ci t])
    (VR S (Hs b S t ++ HS0.drop (t + 1)) (Ps b t ++ PW0.drop (t + 1))) (xS1 mv.nv) b t (HF b S t)
    (retOf (HF b S t) b + S.getD t 0) hC6 hb hHF (by omega) (by have := retOf_small (HF b S t) b hHF hb; omega)
    (by simp) (by simp) (by simp) (by simp) (by simp) hread1
    (by rw [VR_get0, List.length_map]; omega) hx1
  obtain ⟨r1, hr1, hr1ret, hr1ps, hr1vv, hr1c, hr1n, hr1w⟩ := bl1
  -- pop block 1
  have sc1 := pexecM_scope mv fu (blkCmd mv.nv 0 (xS1 mv.nv)) (gS P (C5 b n ++ [ci t]))
    (VR S (Hs b S t ++ HS0.drop (t + 1)) (Ps b t ++ PW0.drop (t + 1))) r1 hr1
  have tk1 := gS_takeC P (C5 b n ++ [ci t]) (C5 b n ++ [ci t]) [cu (HF b S t), cu (HF b S t / 2^31), cu (HF b S t % 2^31),
    cu (b / 2^31), cu (b % 2^31), cu (midOf (HF b S t) b), cu (midOf (HF b S t) b / 2^30), cu (midOf (HF b S t) b % 2^30),
    cu (retOf (HF b S t) b), cu (retOf (HF b S t) b + S.getD t 0), cu ((retOf (HF b S t) b + S.getD t 0) / 2^61),
    cu ((retOf (HF b S t) b + S.getD t 0) % 2^61), cu ((retOf (HF b S t) b + S.getD t 0) % M61)] rfl
  have hHF1 : HF b S (t + 1) = (retOf (HF b S t) b + S.getD t 0) % M61 := rfl
  have hHS1 : (Hs b S t ++ HS0.drop (t + 1)).set (t + 1) (HF b S (t + 1)) = Hs b S (t + 1) ++ HS0.drop (t + 2) := by
    rw [set_pad _ _ _ _ (by rw [Hs_len]) (by omega), Hs_succ]
  have hvv1 : r1.vv = VR S (Hs b S (t + 1) ++ HS0.drop (t + 2)) (Ps b t ++ PW0.drop (t + 1)) := by
    rw [hr1vv, ← hHF1, VR_write0, hHS1]
  rw [hr1ps] at sc1
  simp only [tk1] at sc1
  -- block 2: pw
  have hread2 : ((VR S (Hs b S (t + 1) ++ HS0.drop (t + 2)) (Ps b t ++ PW0.drop (t + 1))) 1)[t]? =
      some ((PF b t : Nat) : Int) := by
    rw [VR_get1]
    have h := natGet (Ps b t ++ PW0.drop (t + 1)) t (by rw [List.length_append, Ps_len]; omega)
    rw [h, getD_app_left _ _ _ (by rw [Ps_len]; omega), Ps_get]
  have hx2 := x2_exec mv hnv fu P (C5 b n ++ [ci t]) (VR S (Hs b S (t + 1) ++ HS0.drop (t + 2)) (Ps b t ++ PW0.drop (t + 1)))
    (PF b t) b hC6 hPF hb
  have bl2 := blk_exec mv hnv 1 (by omega) (by rw [hty1]) fu P (C5 b n ++ [ci t])
    (VR S (Hs b S (t + 1) ++ HS0.drop (t + 2)) (Ps b t ++ PW0.drop (t + 1))) (xS2 mv.nv) b t (PF b t) (retOf (PF b t) b) hC6 hb hPF
    (by omega) (by have := retOf_small (PF b t) b hPF hb; omega) (by simp) (by simp) (by simp) (by simp) (by simp) hread2
    (by rw [VR_get1, List.length_map]; omega) hx2
  obtain ⟨r2, hr2, hr2ret, hr2ps, hr2vv, hr2c, hr2n, hr2w⟩ := bl2
  have sc2 := pexecM_scope mv fu (blkCmd mv.nv 1 (xS2 mv.nv)) (gS P (C5 b n ++ [ci t]))
    (VR S (Hs b S (t + 1) ++ HS0.drop (t + 2)) (Ps b t ++ PW0.drop (t + 1))) r2 hr2
  have tk2 := gS_takeC P (C5 b n ++ [ci t]) (C5 b n ++ [ci t]) [cu (PF b t), cu (PF b t / 2^31), cu (PF b t % 2^31),
    cu (b / 2^31), cu (b % 2^31), cu (midOf (PF b t) b), cu (midOf (PF b t) b / 2^30), cu (midOf (PF b t) b % 2^30),
    cu (retOf (PF b t) b), cu (retOf (PF b t) b), cu (retOf (PF b t) b / 2^61),
    cu (retOf (PF b t) b % 2^61), cu (retOf (PF b t) b % M61)] rfl
  have hPF1 : PF b (t + 1) = (retOf (PF b t) b) % M61 := rfl
  have hPS1 : (Ps b t ++ PW0.drop (t + 1)).set (t + 1) (PF b (t + 1)) = Ps b (t + 1) ++ PW0.drop (t + 2) := by
    rw [set_pad _ _ _ _ (by rw [Ps_len]) (by omega), Ps_succ]
  have hvv2 : r2.vv = VR S (Hs b S (t + 1) ++ HS0.drop (t + 2)) (Ps b (t + 1) ++ PW0.drop (t + 2)) := by
    rw [hr2vv, ← hPF1, VR_write1, hPS1]
  rw [hr2ps] at sc2
  simp only [tk2] at sc2
  have z1 := seqM_some sc2 hr2ret (pexecM_skip mv fu _ _)
  have z2 := seqM_some sc1 hr1ret (by rw [hvv1]; exact z1)
  obtain ⟨rr, hrr, hret, hps, hvv, hcost, hneed, hwk⟩ : ∃ rr : PRM, pexecM mv fu (bodyB mv.nv) (gS P (C5 b n ++ [ci t]))
      (VR S (Hs b S t ++ HS0.drop (t + 1)) (Ps b t ++ PW0.drop (t + 1))) = some rr ∧ rr.ret = none ∧
      rr.ps = gS P (C5 b n ++ [ci t]) ∧ rr.vv = VR S (Hs b S (t + 1) ++ HS0.drop (t + 2)) (Ps b (t + 1) ++ PW0.drop (t + 2)) ∧
      rr.cost ≤ 2100 ∧ rr.need ≤ P.length + 102 ∧ rr.wk ≤ 2 := by
    refine ⟨_, z2, rfl, rfl, hvv2, ?_, ?_, ?_⟩
    · simp; omega
    · simp [gS_size] at hr1n hr2n ⊢
      omega
    · simp; omega
  exact ⟨rr, hrr, hret, hps, hvv, hcost, hneed, hwk⟩


set_option maxHeartbeats 8000000 in
/-- The loop `for (int i = 0; i < n; i++) {...}`. -/
theorem l_build (mv : MV) (hnv : mv.nv = 3) (hty2 : mv.ty 2 = i32) (hty0 : mv.ty 0 = u64) (hty1 : mv.ty 1 = u64)
    (fu : Nat) (P : List Cell) (S HS0 PW0 : List Nat) (b n : Nat) (hb : b < 2^61) (hn : n < 2147483647)
    (hS : S.length = n) (hSv : ∀ x ∈ S, x < 2147483648) (hH : HS0.length = n + 1) (hW : PW0.length = n + 1)
    (hfu : n + 1 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (forStmtB mv.nv 5 4 (bodyB mv.nv)) (gS P (C5 b n))
      (VR S (Hs b S 0 ++ HS0.drop 1) (Ps b 0 ++ PW0.drop 1)) = some res ∧ res.ps = gS P (C5 b n) ∧
      res.vv = VR S (Hs b S n ++ HS0.drop (n + 1)) (Ps b n ++ PW0.drop (n + 1)) ∧ res.ret = none ∧
      res.cost ≤ 2120 * n + 30 ∧ res.need ≤ P.length + 102 ∧ res.wk ≤ 2 * n := by
  obtain ⟨res, C2, hr', hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 5 4 n (by omega) hn (bodyB mv.nv)
    (fun t vv Cl => vv = VR S (Hs b S t ++ HS0.drop (t + 1)) (Ps b t ++ PW0.drop (t + 1)) ∧ Cl = C5 b n)
    2100 102 2 0 (by omega)
    (by
      intro t vv Cl fu ht hCl' hC0 ⟨hvv, hC⟩ _
      subst hvv; subst hC
      obtain ⟨r, hr, hret, hps, hvv, hc, hnd, hwk⟩ := body_iter mv hnv hty2 hty0 hty1 fu P S HS0 PW0 b n t hb hn ht hS hSv hH hW
      exact ⟨r, [], C5 b n, hr, hret, hps, rfl, rfl, ⟨hvv, rfl⟩, hc, hnd, hwk⟩)
    (VR S (Hs b S 0 ++ HS0.drop 1) (Ps b 0 ++ PW0.drop 1)) (C5 b n) rfl rfl ⟨rfl, rfl⟩ fu (by omega)
  obtain ⟨hvv, hC⟩ := hIn
  subst hC
  refine ⟨res, hr', hps, hvv, hret, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

end Proofs.RollingHashBuild
