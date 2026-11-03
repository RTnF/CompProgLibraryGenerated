import Proofs.IsPrimeBody
import Proofs.BellmanFordExec

namespace Proofs.IsPrimeExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.BellmanFordExec (envs pexecM_branch_true pexecM_branch_false lt_conv ne_conv)
open Proofs.IsPrimeBody

abbrev M64 : Nat := 18446744073709551616
abbrev cu (x : Nat) : Cell := ⟨u64, (x : Int)⟩

theorem u64v (x : Nat) (h : x < M64) : u64.valid (x : Int) = true := by
  have h' : x < 18446744073709551616 := h
  rw [valid_u64]; exact decide_eq_true ⟨by omega, by omega⟩

theorem var_den (mv : MV) (P cl : List Cell) (c x : Nat) (hc : cl[c]? = some (cu x)) (hx : x < M64) :
    (vU mv.nv c).denote (penvN mv.nv (gS P cl)) = some (x : Int) := by
  show (NExpr.variable u64 (mv.nv + c)).denote _ = _
  rw [den_variable]
  exact envs mv P cl c (cu x) hc (u64v x hx)

theorem add_den (env : Nat → Ty → Option Int) (e1 e2 : NExpr) (x y : Nat) (h1 : e1.denote env = some (x : Int))
    (h2 : e2.denote env = some (y : Int)) :
    (NExpr.binary u64 .add e1 e2).denote env = some (((x + y) % M64 : Nat) : Int) := by
  rw [den_binary, h1, Option.bind_some, h2, Option.bind_some, convert_u64]
  congr 1

theorem sub_den (env : Nat → Ty → Option Int) (e1 e2 : NExpr) (x y : Nat) (h1 : e1.denote env = some (x : Int))
    (h2 : e2.denote env = some (y : Int)) (hxy : y ≤ x) (hx : x < M64) :
    (NExpr.binary u64 .sub e1 e2).denote env = some ((x - y : Nat) : Int) := by
  rw [den_binary, h1, Option.bind_some, h2, Option.bind_some, convert_u64]
  congr 1
  have : x < 18446744073709551616 := hx
  show ((x : Int) - (y : Int)) % 18446744073709551616 = _
  omega

theorem ge_den (env : Nat → Ty → Option Int) (e1 e2 : NExpr) (x y : Nat) (h1 : e1.denote env = some (x : Int))
    (h2 : e2.denote env = some (y : Int)) :
    (NExpr.binary bT .ge e1 e2).denote env = some (if y ≤ x then 1 else 0) := by
  rw [den_binary, h1, Option.bind_some, h2, Option.bind_some]
  by_cases h : y ≤ x
  · have : (y : Int) ≤ (x : Int) := by omega
    simp [binaryValue, Ty.convert, bT, Ty.valid, h, this]
  · have : ¬ ((y : Int) ≤ (x : Int)) := by omega
    simp [binaryValue, Ty.convert, bT, Ty.valid, h, this]

theorem addm_eq (u v m : Nat) (hu : u < m) (hv : v < m) (hm : m < M64) :
    (if m - v ≤ u then u - (m - v) else (u + v) % M64) = (u + v) % m := by
  by_cases h : m - v ≤ u
  · rw [if_pos h]
    have h1 : m ≤ u + v := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg h, Nat.mod_eq_of_lt (show u + v < M64 by omega), Nat.mod_eq_of_lt (show u + v < m by omega)]

theorem scope_same (P cl1 cl2 : List Cell) (h : cl1.length = cl2.length) :
    (⟨(gS P cl2).mem.take (gS P cl1).mem.length, (gS P cl2).bs.take (gS P cl1).bs.length⟩ : PS) = gS P cl2 := by
  simpa using gS_takeC P cl1 cl2 [] h

/-- `t = u + v; if (u >= m - v) t = u - (m - v);` followed by `K`; the new cell is `it`. -/
abbrev addStmts (nv it iu iv im : Nat) (K : Command) : Command :=
  .sequence (.primitive (.declare u64 true (.binary u64 .add (vU nv iu) (vU nv iv))))
    (.sequence (.branch (.binary bT .ge (vU nv iu) (.binary u64 .sub (vU nv im) (vU nv iv)))
      (.sequence (.scope (.sequence (.primitive (.assign (nv + it) u64
        (.binary u64 .sub (vU nv iu) (.binary u64 .sub (vU nv im) (vU nv iv))))) Sk)) Sk) Sk) K)

set_option maxHeartbeats 16000000 in
theorem addblk_exec (mv : MV) (P cl : List Cell) (iu iv im it u v m : Nat) (hu : cl[iu]? = some (cu u))
    (hv : cl[iv]? = some (cu v)) (hm : cl[im]? = some (cu m)) (hl : cl.length = it) (hum : u < m) (hvm : v < m)
    (hm64 : m < M64) (vv : Nat → List Int) (fu : Nat) (K : Command) (rK : PRM)
    (hK : pexecM mv fu K (gS P (cl ++ [cu ((u + v) % m)])) vv = some rK) :
    ∃ r : PRM, pexecM mv fu (addStmts mv.nv it iu iv im K) (gS P cl) vv = some r ∧ r.ret = rK.ret ∧ r.ps = rK.ps ∧
      r.vv = rK.vv ∧ r.cost ≤ rK.cost + 80 ∧ r.need ≤ max rK.need (P.length + 2 * cl.length + 60) ∧ r.wk = rK.wk := by
  have hu64 : u < M64 := by omega
  have hv64 : v < M64 := by omega
  have hiu : iu < cl.length := (List.getElem?_eq_some_iff.mp hu).1
  have hiv : iv < cl.length := (List.getElem?_eq_some_iff.mp hv).1
  have him : im < cl.length := (List.getElem?_eq_some_iff.mp hm).1
  have hsum : (u + v) % M64 < M64 := Nat.mod_lt _ (by decide)
  have e0 : (NExpr.binary u64 .add (vU mv.nv iu) (vU mv.nv iv)).denote (penvN mv.nv (gS P cl)) =
      some (((u + v) % M64 : Nat) : Int) :=
    add_den _ _ _ u v (var_den mv P cl iu u hu hu64) (var_den mv P cl iv v hv hv64)
  have e0' : vdenM mv vv (penvN mv.nv (gS P cl)) (.binary u64 .add (vU mv.nv iu) (vU mv.nv iv)) =
      some (((u + v) % M64 : Nat) : Int) := by
    rw [vdenM_scalar mv vv _ _ rfl]; exact e0
  have d := gSM_decl mv P cl vv u64 (.binary u64 .add (vU mv.nv iu) (vU mv.nv iv)) (((u + v) % M64 : Nat) : Int)
    (((u + v) % M64 : Nat) : Int) e0' (Ty.convert_of_valid _ _ (u64v _ hsum))
  have a1 := (pexecM_prim mv fu _ _ _).trans d
  -- the condition, evaluated on `cl ++ [t]`
  have hu' : (cl ++ [cu ((u + v) % M64)])[iu]? = some (cu u) := by rw [List.getElem?_append_left hiu]; exact hu
  have hv' : (cl ++ [cu ((u + v) % M64)])[iv]? = some (cu v) := by rw [List.getElem?_append_left hiv]; exact hv
  have hm' : (cl ++ [cu ((u + v) % M64)])[im]? = some (cu m) := by rw [List.getElem?_append_left him]; exact hm
  have hsub : (NExpr.binary u64 .sub (vU mv.nv im) (vU mv.nv iv)).denote (penvN mv.nv (gS P (cl ++ [cu ((u + v) % M64)]))) =
      some ((m - v : Nat) : Int) :=
    sub_den _ _ _ m v (var_den mv P _ im m hm' hm64) (var_den mv P _ iv v hv' hv64) (by omega) hm64
  have hc : vdenM mv vv (penvN mv.nv (gS P (cl ++ [cu ((u + v) % M64)])))
      (.binary bT .ge (vU mv.nv iu) (.binary u64 .sub (vU mv.nv im) (vU mv.nv iv))) = some (if m - v ≤ u then 1 else 0) := by
    rw [vdenM_scalar _ _ _ _ rfl]
    exact ge_den _ _ _ u (m - v) (var_den mv P _ iu u hu' hu64) hsub
  have hcl1 : (cl ++ [cu ((u + v) % M64)]).length = it + 1 := by simp [hl]
  obtain ⟨rB, hB, retB, psB, vvB, cB, nB, wB⟩ : ∃ rB : PRM, pexecM mv fu (.branch (.binary bT .ge (vU mv.nv iu) (.binary u64 .sub (vU mv.nv im) (vU mv.nv iv)))
        (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + it) u64
          (.binary u64 .sub (vU mv.nv iu) (.binary u64 .sub (vU mv.nv im) (vU mv.nv iv))))) Sk)) Sk) Sk)
      (gS P (cl ++ [cu ((u + v) % M64)])) vv = some rB ∧ rB.ret = none ∧ rB.ps = gS P (cl ++ [cu ((u + v) % m)]) ∧
      rB.vv = vv ∧ rB.cost ≤ 70 ∧ rB.need ≤ P.length + 2 * cl.length + 60 ∧ rB.wk = 0 := by
    by_cases hge : m - v ≤ u
    · rw [if_pos hge] at hc
      have hsub2 : (NExpr.binary u64 .sub (vU mv.nv iu) (.binary u64 .sub (vU mv.nv im) (vU mv.nv iv))).denote
          (penvN mv.nv (gS P (cl ++ [cu ((u + v) % M64)]))) = some ((u - (m - v) : Nat) : Int) :=
        sub_den _ _ _ u (m - v) (var_den mv P _ iu u hu' hu64) hsub hge hu64
      have hsub3 : vdenM mv vv (penvN mv.nv (gS P (cl ++ [cu ((u + v) % M64)])))
          (.binary u64 .sub (vU mv.nv iu) (.binary u64 .sub (vU mv.nv im) (vU mv.nv iv))) = some ((u - (m - v) : Nat) : Int) := by
        rw [vdenM_scalar mv vv _ _ rfl]; exact hsub2
      have hs := gSM_assign mv P (cl ++ [cu ((u + v) % M64)]) vv it (by simp [hl]) u64 _ ((u - (m - v) : Nat) : Int)
        ((u - (m - v) : Nat) : Int) hsub3 (cu ((u + v) % M64))
        (by rw [List.getElem?_append_right (by omega)]; simp [hl]) rfl (u64v _ hsum)
        (Ty.convert_of_valid _ _ (u64v _ (by omega)))
      have ha := (pexecM_prim mv fu _ _ _).trans hs
      have hb := seqM_some ha rfl (pexecM_skip mv fu _ _)
      have hsc := pexecM_scope mv fu _ _ _ _ hb
      have hset : (cl ++ [cu ((u + v) % M64)]).set it ⟨u64, ((u - (m - v) : Nat) : Int)⟩ = cl ++ [cu ((u + v) % m)] := by
        rw [List.set_append_right _ _ (by omega)]
        simp [hl]
        have := addm_eq u v m hum hvm hm64
        rw [if_pos hge] at this
        exact_mod_cast this
      rw [hset] at hsc
      have hb2 := seqM_some hsc (by simp) (pexecM_skip mv fu _ _)
      have hbr := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ hb2
      refine ⟨_, hbr, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · simp only [scope_same P (cl ++ [cu ((u + v) % M64)]) (cl ++ [cu ((u + v) % m)]) (by simp)]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hl]; omega
      · simp
    · rw [if_neg hge] at hc
      have hbr := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + it) u64
          (.binary u64 .sub (vU mv.nv iu) (.binary u64 .sub (vU mv.nv im) (vU mv.nv iv))))) Sk)) Sk) Sk _ _ hc _
        (pexecM_skip mv fu _ _)
      have hm2 : (u + v) % M64 = (u + v) % m := by
        have := addm_eq u v m hum hvm hm64
        rw [if_neg hge] at this
        exact this
      refine ⟨_, hbr, rfl, ?_, rfl, ?_, ?_, ?_⟩
      · show gS P (cl ++ [cu ((u + v) % M64)]) = _
        rw [hm2]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hl]; omega
      · simp
  have hK' : pexecM mv fu K rB.ps rB.vv = some rK := by rw [psB, vvB]; exact hK
  have s1 := seqM_some hB retB hK'
  have s0 := seqM_some a1 rfl s1
  refine ⟨_, s0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cB ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, hl] at nB ⊢; omega
  · simp [wB]

theorem tU_den (env : Nat → Ty → Option Int) : tU.denote env = some 2 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, convert_u64]
  rfl

theorem zU_den (env : Nat → Ty → Option Int) : zU.denote env = some 0 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some, convert_u64]
  rfl

theorem oU_den (env : Nat → Ty → Option Int) : oU.denote env = some 1 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some, convert_u64]
  rfl

theorem odd_cell (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (c y : Nat) (hc : cl[c]? = some (cu y)) (hy : y < M64) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (oddE mv.nv c) = some (if y % 2 = 1 then 1 else 0) := by
  have hr : checkedDivRem u64 true (y : Int) 2 = some ((y % 2 : Nat) : Int) := Proofs.PowModStep.rem_value y 2 (by omega) hy
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_divrem, var_den mv P cl c y hc hy, Option.bind_some, tU_den,
    Option.bind_some, hr, Option.bind_some, oU_den, Option.bind_some]
  by_cases h : y % 2 = 1
  · simp [binaryValue, Ty.convert, bT, Ty.valid, h]
  · have : ((y % 2 : Nat) : Int) ≠ 1 := by omega
    simp [binaryValue, Ty.convert, bT, Ty.valid, h, this]
    omega

theorem ne_zero_cell (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (c y : Nat) (hc : cl[c]? = some (cu y)) (hy : y < M64) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.binary bT .ne (vU mv.nv c) zU) = some (if y ≠ 0 then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, var_den mv P cl c y hc hy, Option.bind_some, zU_den, Option.bind_some]
  by_cases h : y = 0
  · subst h; simp [binaryValue, Ty.convert, bT, Ty.valid]
  · have : (y : Int) ≠ 0 := by omega
    simp [binaryValue, Ty.convert, bT, Ty.valid, h, this]

theorem half_cell (mv : MV) (vv : Nat → List Int) (P cl : List Cell) (c y : Nat) (hc : cl[c]? = some (cu y)) (hy : y < M64) :
    vdenM mv vv (penvN mv.nv (gS P cl)) (.divrem u64 false (vU mv.nv c) tU) = some ((y / 2 : Nat) : Int) := by
  have hd : checkedDivRem u64 false (y : Int) 2 = some ((y / 2 : Nat) : Int) := div_value y 2 (by omega) hy
  rw [vdenM_scalar _ _ _ _ rfl, den_divrem, var_den mv P cl c y hc hy, Option.bind_some, tU_den, Option.bind_some, hd]

theorem cells_set (C0 L : List Cell) (b i : Nat) (y : Cell) (hC : C0.length = b) :
    (C0 ++ L).set (b + i) y = C0 ++ L.set i y := by
  rw [List.set_append_right _ _ (by omega)]
  simp [hC]

theorem copy_exec (mv : MV) (P cl : List Cell) (tgt src vo vn : Nat) (hs : cl[src]? = some (cu vn))
    (ht : cl[tgt]? = some (cu vo)) (hvn : vn < M64) (hvo : vo < M64) (vv : Nat → List Int) (fu : Nat) (K : Command) (rK : PRM)
    (hK : pexecM mv fu K (gS P (cl.set tgt (cu vn))) vv = some rK) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (.assign (mv.nv + tgt) u64 (vU mv.nv src))) K) (gS P cl) vv = some r ∧
      r.ret = rK.ret ∧ r.ps = rK.ps ∧ r.vv = rK.vv ∧ r.cost ≤ rK.cost + 20 ∧
      r.need ≤ max rK.need (P.length + 2 * cl.length + 20) ∧ r.wk = rK.wk := by
  have htl : tgt < cl.length := (List.getElem?_eq_some_iff.mp ht).1
  have hv : vdenM mv vv (penvN mv.nv (gS P cl)) (vU mv.nv src) = some (vn : Int) := by
    rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P cl src vn hs hvn
  have s := gSM_assign mv P cl vv tgt htl u64 _ (vn : Int) (vn : Int) hv (cu vo) ht rfl (u64v _ hvo)
    (Ty.convert_of_valid _ _ (u64v _ hvn))
  have a1 := (pexecM_prim mv fu _ _ _).trans s
  have hK' : pexecM mv fu K ((⟨gS P (cl.set tgt ⟨u64, (vn : Int)⟩), vv, none, (vwp (vU mv.nv src)).1 + 1,
      P.length + 2 * cl.length + (vwp (vU mv.nv src)).2 + 2, 0⟩ : PRM).ps)
      ((⟨gS P (cl.set tgt ⟨u64, (vn : Int)⟩), vv, none, (vwp (vU mv.nv src)).1 + 1,
      P.length + 2 * cl.length + (vwp (vU mv.nv src)).2 + 2, 0⟩ : PRM).vv) = some rK := hK
  have s1 := seqM_some a1 rfl hK'
  refine ⟨_, s1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  · simp

theorem halve_exec (mv : MV) (P cl : List Cell) (c y : Nat) (hc : cl[c]? = some (cu y)) (hy : y < M64)
    (vv : Nat → List Int) (fu : Nat) (K : Command) (rK : PRM)
    (hK : pexecM mv fu K (gS P (cl.set c (cu (y / 2)))) vv = some rK) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (halfS mv.nv c)) K) (gS P cl) vv = some r ∧
      r.ret = rK.ret ∧ r.ps = rK.ps ∧ r.vv = rK.vv ∧ r.cost ≤ rK.cost + 20 ∧
      r.need ≤ max rK.need (P.length + 2 * cl.length + 20) ∧ r.wk = rK.wk := by
  have htl : c < cl.length := (List.getElem?_eq_some_iff.mp hc).1
  have hv := half_cell mv vv P cl c y hc hy
  have hq : y / 2 < M64 := by omega
  have s := gSM_assign mv P cl vv c htl u64 _ ((y / 2 : Nat) : Int) ((y / 2 : Nat) : Int) hv (cu y) hc rfl (u64v _ hy)
    (Ty.convert_of_valid _ _ (u64v _ hq))
  have a1 := (pexecM_prim mv fu _ _ _).trans s
  have hK' : pexecM mv fu K ((⟨gS P (cl.set c ⟨u64, ((y / 2 : Nat) : Int)⟩), vv, none, (vwp (.divrem u64 false (vU mv.nv c) tU)).1 + 1,
      P.length + 2 * cl.length + (vwp (.divrem u64 false (vU mv.nv c) tU)).2 + 2, 0⟩ : PRM).ps)
      ((⟨gS P (cl.set c ⟨u64, ((y / 2 : Nat) : Int)⟩), vv, none, (vwp (.divrem u64 false (vU mv.nv c) tU)).1 + 1,
      P.length + 2 * cl.length + (vwp (.divrem u64 false (vU mv.nv c) tU)).2 + 2, 0⟩ : PRM).vv) = some rK := hK
  have s1 := seqM_some a1 rfl hK'
  refine ⟨_, s1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  · simp

/-! ### The multiplication loop -/

/-- The cells of the multiplication block: the parameters, `r`, `x`, `y`, after `C0`. -/
abbrev CLm (C0 : List Cell) (a bb m r x y : Nat) : List Cell := C0 ++ [cu a, cu bb, cu m, cu r, cu x, cu y]

theorem cellq (C0 L : List Cell) (b i : Nat) (hC : C0.length = b) : (C0 ++ L)[b + i]? = L[i]? := by
  subst hC
  rw [List.getElem?_append_right (by omega)]
  simp

abbrev mulK1 (nv b : Nat) : Command := .sequence (.primitive (.assign (nv + (b + 3)) u64 (vU nv (b + 6)))) Sk
abbrev mulK2 (nv b : Nat) : Command :=
  .sequence (.primitive (.assign (nv + (b + 4)) u64 (vU nv (b + 6)))) (.sequence (.primitive (halfS nv (b + 5))) Sk)

set_option maxHeartbeats 16000000 in
/-- `r = (r + x) % m` (the odd branch). -/
theorem mul_first (mv : MV) (P C0 : List Cell) (b a bb m r x y : Nat) (hC : C0.length = b) (hr : r < m) (hx : x < m)
    (hm : m < M64) (vv : Nat → List Int) (fu : Nat) :
    ∃ res : PRM, pexecM mv fu (addStmts mv.nv (b + 6) (b + 3) (b + 4) (b + 2) (mulK1 mv.nv b)) (gS P (CLm C0 a bb m r x y)) vv =
      some res ∧ res.ret = none ∧ res.ps = gS P (CLm C0 a bb m ((r + x) % m) x y ++ [cu ((r + x) % m)]) ∧ res.vv = vv ∧
      res.cost ≤ 120 ∧ res.need ≤ P.length + 2 * b + 100 ∧ res.wk = 0 := by
  have hm64 : m < M64 := hm
  have hlen : (CLm C0 a bb m r x y).length = b + 6 := by simp [hC]
  have hu := cellq C0 [cu a, cu bb, cu m, cu r, cu x, cu y] b 3 hC
  have hv := cellq C0 [cu a, cu bb, cu m, cu r, cu x, cu y] b 4 hC
  have hmm := cellq C0 [cu a, cu bb, cu m, cu r, cu x, cu y] b 2 hC
  have hmod : (r + x) % m < M64 := by have := Nat.mod_lt (r + x) (show 0 < m by omega); omega
  have hc6 : (CLm C0 a bb m r x y ++ [cu ((r + x) % m)])[b + 6]? = some (cu ((r + x) % m)) := by
    rw [List.getElem?_append_right (by simp [hC])]; simp [hC]
  have hc3 : (CLm C0 a bb m r x y ++ [cu ((r + x) % m)])[b + 3]? = some (cu r) := by
    rw [List.getElem?_append_left (by simp [hC])]; simpa using hu
  have hset : (CLm C0 a bb m r x y ++ [cu ((r + x) % m)]).set (b + 3) (cu ((r + x) % m)) =
      CLm C0 a bb m ((r + x) % m) x y ++ [cu ((r + x) % m)] := by
    rw [List.set_append_left _ _ (by simp [hC]), cells_set C0 _ b 3 _ hC]
    simp
  have hK := copy_exec mv P (CLm C0 a bb m r x y ++ [cu ((r + x) % m)]) (b + 3) (b + 6) r ((r + x) % m) hc6 hc3 hmod
    (by omega) vv fu Sk ⟨gS P (CLm C0 a bb m ((r + x) % m) x y ++ [cu ((r + x) % m)]), vv, none, 0,
      (gS P (CLm C0 a bb m ((r + x) % m) x y ++ [cu ((r + x) % m)])).mem.length +
        (gS P (CLm C0 a bb m ((r + x) % m) x y ++ [cu ((r + x) % m)])).bs.length, 0⟩
    (by rw [hset]; exact pexecM_skip mv fu _ _)
  obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := hK
  obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := addblk_exec mv P (CLm C0 a bb m r x y) (b + 3) (b + 4) (b + 2) (b + 6) r x m
    hu hv hmm hlen hr hx hm64 vv fu _ r1 h1
  refine ⟨r2, h2, by rw [ret2, ret1], by rw [ps2, ps1], by rw [vv2, vv1], ?_, ?_, ?_⟩
  · have : r2.cost ≤ r1.cost + 80 := c2
    simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c1; omega
  · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at n1 n2 ⊢; omega
  · rw [w2, w1]

set_option maxHeartbeats 16000000 in
/-- `x = (x + x) % m; y = y / 2` (the part every iteration executes). -/
theorem mul_second (mv : MV) (P C0 : List Cell) (b a bb m r x y : Nat) (hC : C0.length = b) (hx : x < m)
    (hm : m < M64) (hy : y < M64) (vv : Nat → List Int) (fu : Nat) :
    ∃ res : PRM, pexecM mv fu (addStmts mv.nv (b + 6) (b + 4) (b + 4) (b + 2) (mulK2 mv.nv b)) (gS P (CLm C0 a bb m r x y)) vv =
      some res ∧ res.ret = none ∧ res.ps = gS P (CLm C0 a bb m r ((x + x) % m) (y / 2) ++ [cu ((x + x) % m)]) ∧ res.vv = vv ∧
      res.cost ≤ 160 ∧ res.need ≤ P.length + 2 * b + 100 ∧ res.wk = 0 := by
  have hlen : (CLm C0 a bb m r x y).length = b + 6 := by simp [hC]
  have hv := cellq C0 [cu a, cu bb, cu m, cu r, cu x, cu y] b 4 hC
  have hmm := cellq C0 [cu a, cu bb, cu m, cu r, cu x, cu y] b 2 hC
  have hmod : (x + x) % m < M64 := by have := Nat.mod_lt (x + x) (show 0 < m by omega); omega
  have hc6 : (CLm C0 a bb m r x y ++ [cu ((x + x) % m)])[b + 6]? = some (cu ((x + x) % m)) := by
    rw [List.getElem?_append_right (by simp [hC])]; simp [hC]
  have hc4 : (CLm C0 a bb m r x y ++ [cu ((x + x) % m)])[b + 4]? = some (cu x) := by
    rw [List.getElem?_append_left (by simp [hC])]; simpa using hv
  have hc5 : (CLm C0 a bb m r ((x + x) % m) y ++ [cu ((x + x) % m)])[b + 5]? = some (cu y) := by
    rw [List.getElem?_append_left (by simp [hC])]; simpa using cellq C0 [cu a, cu bb, cu m, cu r, cu ((x + x) % m), cu y] b 5 hC
  have hset4 : (CLm C0 a bb m r x y ++ [cu ((x + x) % m)]).set (b + 4) (cu ((x + x) % m)) =
      CLm C0 a bb m r ((x + x) % m) y ++ [cu ((x + x) % m)] := by
    rw [List.set_append_left _ _ (by simp [hC]), cells_set C0 _ b 4 _ hC]
    simp
  have hset5 : (CLm C0 a bb m r ((x + x) % m) y ++ [cu ((x + x) % m)]).set (b + 5) (cu (y / 2)) =
      CLm C0 a bb m r ((x + x) % m) (y / 2) ++ [cu ((x + x) % m)] := by
    rw [List.set_append_left _ _ (by simp [hC]), cells_set C0 _ b 5 _ hC]
    simp
  obtain ⟨rH, hH, retH, psH, vvH, cH, nH, wH⟩ := halve_exec mv P (CLm C0 a bb m r ((x + x) % m) y ++ [cu ((x + x) % m)]) (b + 5) y
    hc5 hy vv fu Sk ⟨gS P (CLm C0 a bb m r ((x + x) % m) (y / 2) ++ [cu ((x + x) % m)]), vv, none, 0,
      (gS P (CLm C0 a bb m r ((x + x) % m) (y / 2) ++ [cu ((x + x) % m)])).mem.length +
        (gS P (CLm C0 a bb m r ((x + x) % m) (y / 2) ++ [cu ((x + x) % m)])).bs.length, 0⟩
    (by rw [hset5]; exact pexecM_skip mv fu _ _)
  obtain ⟨rC, hC', retC, psC, vvC, cC, nC, wC⟩ := copy_exec mv P (CLm C0 a bb m r x y ++ [cu ((x + x) % m)]) (b + 4) (b + 6) x
    ((x + x) % m) hc6 hc4 hmod (by omega) vv fu _ rH (by rw [hset4]; exact hH)
  obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := addblk_exec mv P (CLm C0 a bb m r x y) (b + 4) (b + 4) (b + 2) (b + 6) x x m
    hv hv hmm hlen hx hx hm vv fu _ rC hC'
  refine ⟨r2, h2, by rw [ret2, retC, retH], ?_, by rw [vv2, vvC, vvH], ?_, ?_, ?_⟩
  · rw [ps2, psC, psH]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cC cH ⊢; omega
  · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at nC nH n2 ⊢; omega
  · rw [w2, wC, wH]

set_option maxHeartbeats 16000000 in
/-- One iteration of the multiplication loop. -/
theorem mul_iter (mv : MV) (P C0 : List Cell) (b a bb m r x y : Nat) (hC : C0.length = b) (hr : r < m) (hx : x < m)
    (hm : m < M64) (hy : y < M64) (vv : Nat → List Int) (fu : Nat) :
    ∃ res : PRM, pexecM mv fu (mulLoop mv.nv b) (gS P (CLm C0 a bb m r x y)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (CLm C0 a bb m (if y % 2 = 1 then (r + x) % m else r) ((x + x) % m) (y / 2)) ∧ res.vv = vv ∧
      res.cost ≤ 400 ∧ res.need ≤ P.length + 2 * b + 150 ∧ res.wk = 0 := by
  have hlen : (CLm C0 a bb m r x y).length = b + 6 := by simp [hC]
  have hy5 := cellq C0 [cu a, cu bb, cu m, cu r, cu x, cu y] b 5 hC
  have hc := odd_cell mv vv P (CLm C0 a bb m r x y) (b + 5) y (by simpa using hy5) hy
  have hmod : (r + x) % m < M64 := by have := Nat.mod_lt (r + x) (show 0 < m by omega); omega
  have hmodr : (if y % 2 = 1 then (r + x) % m else r) < m := by
    split
    · exact Nat.mod_lt _ (by omega)
    · exact hr
  have tk1 : (⟨(gS P (CLm C0 a bb m ((r + x) % m) x y ++ [cu ((r + x) % m)])).mem.take (gS P (CLm C0 a bb m r x y)).mem.length,
      (gS P (CLm C0 a bb m ((r + x) % m) x y ++ [cu ((r + x) % m)])).bs.take (gS P (CLm C0 a bb m r x y)).bs.length⟩ : PS) =
      gS P (CLm C0 a bb m ((r + x) % m) x y) :=
    gS_takeC P (CLm C0 a bb m r x y) (CLm C0 a bb m ((r + x) % m) x y) [cu ((r + x) % m)] (by simp)
  -- the state after the first part, for both cases
  obtain ⟨rr, r', hs1, ret1, ps1, vv1, cst1, nd1, wk1, hR1⟩ : ∃ rr : PRM, ∃ r' : Nat,
      pexecM mv fu (.branch (oddE mv.nv (b + 5)) (.sequence (.scope (addStmts mv.nv (b + 6) (b + 3) (b + 4) (b + 2) (mulK1 mv.nv b))) Sk) Sk)
        (gS P (CLm C0 a bb m r x y)) vv = some rr ∧ rr.ret = none ∧ rr.ps = gS P (CLm C0 a bb m r' x y) ∧ rr.vv = vv ∧
        rr.cost ≤ 200 ∧ rr.need ≤ P.length + 2 * b + 120 ∧ rr.wk = 0 ∧ r' = (if y % 2 = 1 then (r + x) % m else r) := by
    by_cases hodd : y % 2 = 1
    · rw [if_pos hodd] at hc
      obtain ⟨rf, hf, retf, psf, vvf, cf, nf, wf⟩ := mul_first mv P C0 b a bb m r x y hC hr hx hm vv fu
      have t1 := pexecM_scope mv fu _ _ _ _ hf
      rw [psf] at t1
      simp only [tk1] at t1
      have t2 := seqM_some t1 (by simp [retf]) (pexecM_skip mv fu _ _)
      have t3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ t2
      refine ⟨_, (r + x) % m, t3, ?_, ?_, ?_, ?_, ?_, ?_, by simp [hodd]⟩
      · rfl
      · rfl
      · exact vvf
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cf ⊢; omega
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at nf ⊢; omega
      · simp [wf]
    · rw [if_neg hodd] at hc
      have t3 := pexecM_branch_false mv fu _ (.sequence (.scope (addStmts mv.nv (b + 6) (b + 3) (b + 4) (b + 2) (mulK1 mv.nv b))) Sk) Sk
        _ _ hc _ (pexecM_skip mv fu _ _)
      refine ⟨_, r, t3, ?_, ?_, ?_, ?_, ?_, ?_, by simp [hodd]⟩
      · rfl
      · rfl
      · rfl
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly]; omega
      · rfl
  have hr1 : r' < m := by rw [hR1]; exact hmodr
  obtain ⟨rf2, hf2, retf2, psf2, vvf2, cf2, nf2, wf2⟩ := mul_second mv P C0 b a bb m r' x y hC hx hm hy vv fu
  have tk2 : (⟨(gS P (CLm C0 a bb m r' ((x + x) % m) (y / 2) ++ [cu ((x + x) % m)])).mem.take
      (gS P (CLm C0 a bb m r x y)).mem.length,
      (gS P (CLm C0 a bb m r' ((x + x) % m) (y / 2) ++ [cu ((x + x) % m)])).bs.take (gS P (CLm C0 a bb m r x y)).bs.length⟩ : PS) =
      gS P (CLm C0 a bb m r' ((x + x) % m) (y / 2)) :=
    gS_takeC P (CLm C0 a bb m r x y) (CLm C0 a bb m r' ((x + x) % m) (y / 2)) [cu ((x + x) % m)] (by simp)
  have hf2' : pexecM mv fu (addStmts mv.nv (b + 6) (b + 4) (b + 4) (b + 2) (mulK2 mv.nv b)) rr.ps rr.vv = some rf2 := by
    rw [ps1, vv1]; exact hf2
  have s1 := seqM_some hs1 ret1 hf2'
  have s2 := pexecM_scope mv fu _ _ _ _ s1
  simp only [psf2] at s2
  simp only [tk2] at s2
  have s3 := seqM_some s2 (by simp [retf2]) (pexecM_skip mv fu _ _)
  refine ⟨_, s3, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR1]
  · rw [vvf2]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cst1 cf2 ⊢; omega
  · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at nd1 nf2 ⊢; omega
  · simp [wk1, wf2]

/-- The state of the multiplication loop after `k` iterations. -/
def mstep (m : Nat) (s : Nat × Nat × Nat) : Nat × Nat × Nat :=
  ((if s.2.2 % 2 = 1 then (s.1 + s.2.1) % m else s.1), (s.2.1 + s.2.1) % m, s.2.2 / 2)

def mrun (m : Nat) : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, s => s
  | k + 1, s => if s.2.2 = 0 then s else mrun m k (mstep m s)

theorem step_mod (m r x y : Nat) :
    ((if y % 2 = 1 then (r + x) % m else r) + ((x + x) % m) * (y / 2)) % m = (r + x * y) % m := by
  have hyy : y = 2 * (y / 2) + y % 2 := (Nat.div_add_mod y 2).symm
  have hmul : x * (2 * (y / 2)) = x * (y / 2) + x * (y / 2) := by rw [Nat.two_mul, Nat.mul_add]
  have hadd : (x + x) * (y / 2) = x * (y / 2) + x * (y / 2) := Nat.add_mul _ _ _
  by_cases hodd : y % 2 = 1
  · rw [if_pos hodd]
    have hid : r + x + (x + x) * (y / 2) = r + x * y := by
      have : x * y = x * (2 * (y / 2) + y % 2) := by rw [← hyy]
      rw [this, Nat.mul_add, hmul, hodd, hadd]; omega
    rw [Nat.add_mod ((r + x) % m), Nat.mod_mod, Nat.mod_mul_mod, ← Nat.add_mod, hid]
  · rw [if_neg hodd]
    have h0 : y % 2 = 0 := by omega
    have hid : r + (x + x) * (y / 2) = r + x * y := by
      have : x * y = x * (2 * (y / 2) + y % 2) := by rw [← hyy]
      rw [this, Nat.mul_add, hmul, h0, hadd]; omega
    rw [Nat.add_mod r, Nat.mod_mul_mod, ← Nat.add_mod, hid]

theorem mrun_spec (m : Nat) (hm : 0 < m) : ∀ (k : Nat) (r x y : Nat), r < m → x < m → y < 2 ^ k →
    (mrun m k (r, x, y)).1 < m ∧ (mrun m k (r, x, y)).1 = (r + x * y) % m ∧ (mrun m k (r, x, y)).2.1 < m ∧
      (mrun m k (r, x, y)).2.2 = 0 := by
  intro k
  induction k with
  | zero =>
    intro r x y hr hx hy
    have : y = 0 := by simpa using hy
    subst this
    simp [mrun]
    exact ⟨hr, (Nat.mod_eq_of_lt hr).symm, hx⟩
  | succ k ih =>
    intro r x y hr hx hy
    by_cases h0 : y = 0
    · subst h0
      simp [mrun]
      exact ⟨hr, (Nat.mod_eq_of_lt hr).symm, hx⟩
    · simp only [mrun, if_neg h0]
      have hy' : y / 2 < 2 ^ k := by rw [Nat.pow_succ] at hy; omega
      have hr' : (if y % 2 = 1 then (r + x) % m else r) < m := by
        split
        · exact Nat.mod_lt _ hm
        · exact hr
      obtain ⟨h1, h2, h3, h4⟩ := ih (if y % 2 = 1 then (r + x) % m else r) ((x + x) % m) (y / 2) hr' (Nat.mod_lt _ hm) hy'
      have e : mstep m (r, x, y) = ((if y % 2 = 1 then (r + x) % m else r), (x + x) % m, y / 2) := rfl
      rw [e]
      exact ⟨h1, by rw [h2]; exact step_mod m r x y, h3, h4⟩

set_option maxHeartbeats 64000000 in
/-- The loop `while (y != 0)` of the multiplication. -/
theorem mul_while (mv : MV) (P C0 : List Cell) (b a bb m : Nat) (hC : C0.length = b) (hm : m < M64) (vv : Nat → List Int) :
    ∀ (k r x y fu : Nat), y < 2 ^ k → r < m → x < m → y < M64 → k + 1 ≤ fu →
      ∃ res : PRM, pexecM mv fu (.whileLoop (.binary bT .ne (vU mv.nv (b + 5)) zU) (mulLoop mv.nv b))
        (gS P (CLm C0 a bb m r x y)) vv = some res ∧ res.ret = none ∧
        res.ps = gS P (CLm C0 a bb m (mrun m k (r, x, y)).1 (mrun m k (r, x, y)).2.1 (mrun m k (r, x, y)).2.2) ∧ res.vv = vv ∧
        res.cost ≤ k * 420 + 30 ∧ res.need ≤ P.length + 2 * b + 150 ∧ res.wk = 0 := by
  intro k
  induction k with
  | zero =>
    intro r x y fu hy0 hr hx hy hfu
    have hy' : y = 0 := by simpa using hy0
    subst hy'
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hy5 := cellq C0 [cu a, cu bb, cu m, cu r, cu x, cu 0] b 5 hC
    have hc := ne_zero_cell mv vv P (CLm C0 a bb m r x 0) (b + 5) 0 (by simpa using hy5) hy
    rw [if_neg (by simp)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  | succ k ih =>
    intro r x y fu hyk hr hx hy hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hy5 := cellq C0 [cu a, cu bb, cu m, cu r, cu x, cu y] b 5 hC
    have hc := ne_zero_cell mv vv P (CLm C0 a bb m r x y) (b + 5) y (by simpa using hy5) hy
    by_cases hz : y = 0
    · subst hz
      rw [if_neg (by simp)] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
      · simp [mrun]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly]; omega
    · rw [if_pos hz] at hc
      obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := mul_iter mv P C0 b a bb m r x y hC hr hx hm hy vv (fu' + 1)
      have hr' : (if y % 2 = 1 then (r + x) % m else r) < m := by
        split
        · exact Nat.mod_lt _ (by omega)
        · exact hr
      have hy2 : y / 2 < 2 ^ k := by rw [Nat.pow_succ] at hyk; omega
      obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih (if y % 2 = 1 then (r + x) % m else r) ((x + x) % m) (y / 2) fu' hy2
        hr' (Nat.mod_lt _ (by omega)) (by omega) (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
      rw [h1]
      simp only [ret1, ps1, vv1]
      rw [h2]
      simp only
      refine ⟨_, rfl, ret2, ?_, vv2, ?_, ?_, ?_⟩
      · rw [ps2]
        have e : mrun m (k + 1) (r, x, y) = mrun m k (mstep m (r, x, y)) := by simp [mrun, hz]
        rw [e]; rfl
      · rw [Nat.succ_mul]
        simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c1 c2 ⊢; omega
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at n1 n2 ⊢; omega
      · simp [w1, w2]

theorem pow64 : (2 : Nat) ^ 64 = M64 := rfl

set_option maxHeartbeats 64000000 in
/-- The whole multiplication block `mul_mod_u64(a, b, m)` (the parameters are in the cells `b, b + 1, b + 2`). -/
theorem mul_block (mv : MV) (P C0 : List Cell) (b a bb m : Nat) (hC : C0.length = b) (ha : a < m) (hb : bb < m)
    (hm : m < M64) (vv : Nat → List Int) (fu : Nat) (hfu : 65 ≤ fu) (rest : Command) (rR : PRM)
    (hrest : pexecM mv fu rest (gS P (CLm C0 a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0)) vv = some rR) :
    ∃ res : PRM, pexecM mv fu (mulBody mv.nv b rest) (gS P (C0 ++ [cu a, cu bb, cu m])) vv = some res ∧
      res.ret = rR.ret ∧ res.ps = rR.ps ∧ res.vv = rR.vv ∧ res.cost ≤ rR.cost + 64 * 420 + 200 ∧
      res.need ≤ max rR.need (P.length + 2 * b + 150) ∧ res.wk = rR.wk := by
  have hm0 : 0 < m := by omega
  have ha64 : a < M64 := by omega
  have hb64 : bb < M64 := by omega
  have hl3 : (C0 ++ [cu a, cu bb, cu m]).length = b + 3 := by simp [hC]
  -- r = 0
  have d1 := gSM_decl mv P (C0 ++ [cu a, cu bb, cu m]) vv u64 zU 0 0 (by rw [vdenM_scalar mv vv _ _ rfl]; exact zU_den _)
    (Ty.convert_of_valid _ _ (u64v 0 (by decide)))
  have a1 := (pexecM_prim mv fu _ _ _).trans d1
  have e1 : C0 ++ [cu a, cu bb, cu m] ++ [(⟨u64, 0⟩ : Cell)] = C0 ++ [cu a, cu bb, cu m, cu 0] := by simp [cu]
  rw [e1] at a1
  -- x = a
  have hxa : (vU mv.nv b).denote (penvN mv.nv (gS P (C0 ++ [cu a, cu bb, cu m, cu 0]))) = some (a : Int) :=
    var_den mv P _ b a (by have := cellq C0 [cu a, cu bb, cu m, cu 0] b 0 hC; simpa using this) ha64
  have d2 := gSM_decl mv P (C0 ++ [cu a, cu bb, cu m, cu 0]) vv u64 (vU mv.nv b) (a : Int) (a : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact hxa) (Ty.convert_of_valid _ _ (u64v a ha64))
  have a2 := (pexecM_prim mv fu _ _ _).trans d2
  have e2 : C0 ++ [cu a, cu bb, cu m, cu 0] ++ [(⟨u64, (a : Int)⟩ : Cell)] = C0 ++ [cu a, cu bb, cu m, cu 0, cu a] := by simp [cu]
  rw [e2] at a2
  -- y = b
  have hyb : (vU mv.nv (b + 1)).denote (penvN mv.nv (gS P (C0 ++ [cu a, cu bb, cu m, cu 0, cu a]))) = some (bb : Int) :=
    var_den mv P _ (b + 1) bb (by have := cellq C0 [cu a, cu bb, cu m, cu 0, cu a] b 1 hC; simpa using this) hb64
  have d3 := gSM_decl mv P (C0 ++ [cu a, cu bb, cu m, cu 0, cu a]) vv u64 (vU mv.nv (b + 1)) (bb : Int) (bb : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact hyb) (Ty.convert_of_valid _ _ (u64v bb hb64))
  have a3 := (pexecM_prim mv fu _ _ _).trans d3
  have e3 : C0 ++ [cu a, cu bb, cu m, cu 0, cu a] ++ [(⟨u64, (bb : Int)⟩ : Cell)] = CLm C0 a bb m 0 a bb := by simp [cu]
  rw [e3] at a3
  -- the loop
  obtain ⟨rw_, hw, retw, psw, vvw, cw, nw, ww⟩ := mul_while mv P C0 b a bb m hC hm vv 64 0 a bb fu (by rw [pow64]; exact hb64) hm0 ha hb64
    (by omega)
  have hspec := mrun_spec m hm0 64 0 a bb hm0 ha (by rw [pow64]; exact hb64)
  have hps : rw_.ps = gS P (CLm C0 a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0) := by
    rw [psw, hspec.2.2.2, hspec.2.1]; simp
  have hrest' : pexecM mv fu rest rw_.ps rw_.vv = some rR := by rw [hps, vvw]; exact hrest
  have b3 := seqM_some hw retw hrest'
  have b2 := seqM_some a3 rfl b3
  have b1 := seqM_some a2 rfl b2
  have b0 := seqM_some a1 rfl b1
  refine ⟨_, b0, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cw ⊢; omega
  · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at nw ⊢; omega
  · simp [ww]

/-- The cells after the call, before the scope that contains it is left. -/
abbrev callCells (Cp : List Cell) (tgt a bb m r xf : Nat) : List Cell :=
  Cp.set tgt (cu r) ++ [cu a, cu bb, cu m, cu r, cu xf, cu 0, cu r, cu r]

set_option maxHeartbeats 64000000 in
theorem mulcall_exec (mv : MV) (P Cp : List Cell) (ia ib im tgt a bb m t0 : Nat) (hia : Cp[ia]? = some (cu a))
    (hib : Cp[ib]? = some (cu bb)) (him : Cp[im]? = some (cu m)) (ht : Cp[tgt]? = some (cu t0)) (hab : a < m) (hbb : bb < m)
    (hm : m < M64) (ht0 : t0 < M64) (vv : Nat → List Int) (fu : Nat) (hfu : 65 ≤ fu) (K : Command) (rK : PRM)
    (hK : pexecM mv fu K (gS P (callCells Cp tgt a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1)) vv = some rK) :
    ∃ res : PRM, pexecM mv fu (callMul mv.nv Cp.length ia ib im tgt K) (gS P Cp) vv = some res ∧ res.ret = rK.ret ∧
      res.ps = rK.ps ∧ res.vv = rK.vv ∧ res.cost ≤ rK.cost + 64 * 420 + 300 ∧
      res.need ≤ max rK.need (P.length + 2 * Cp.length + 150) ∧ res.wk = rK.wk := by
  have ha64 : a < M64 := by omega
  have hb64 : bb < M64 := by omega
  have hm0 : 0 < m := by omega
  have hr : (a * bb) % m < M64 := by have := Nat.mod_lt (a * bb) hm0; omega
  have hxf : (mrun m 64 (0, a, bb)).2.1 < M64 := by
    have := (mrun_spec m hm0 64 0 a bb hm0 hab (by rw [pow64]; exact hb64)).2.2.1; omega
  have hitl := (List.getElem?_eq_some_iff.mp ht).1
  -- the three argument declarations
  have d1 := gSM_decl mv P Cp vv u64 (vU mv.nv ia) (a : Int) (a : Int) (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P Cp ia a hia ha64)
    (Ty.convert_of_valid _ _ (u64v a ha64))
  have a1 := (pexecM_prim mv fu _ _ _).trans d1
  have hib' : (Cp ++ [cu a])[ib]? = some (cu bb) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hib).1]; exact hib
  have d2 := gSM_decl mv P (Cp ++ [cu a]) vv u64 (vU mv.nv ib) (bb : Int) (bb : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ ib bb hib' hb64) (Ty.convert_of_valid _ _ (u64v bb hb64))
  have a2 := (pexecM_prim mv fu _ _ _).trans d2
  have e2 : Cp ++ [cu a] ++ [(⟨u64, (bb : Int)⟩ : Cell)] = Cp ++ [cu a, cu bb] := by simp [cu]
  rw [e2] at a2
  have him' : (Cp ++ [cu a, cu bb])[im]? = some (cu m) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp him).1]; exact him
  have d3 := gSM_decl mv P (Cp ++ [cu a, cu bb]) vv u64 (vU mv.nv im) (m : Int) (m : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ im m him' hm) (Ty.convert_of_valid _ _ (u64v m hm))
  have a3 := (pexecM_prim mv fu _ _ _).trans d3
  have e3 : Cp ++ [cu a, cu bb] ++ [(⟨u64, (m : Int)⟩ : Cell)] = Cp ++ [cu a, cu bb, cu m] := by simp [cu]
  rw [e3] at a3
  -- the rest of the block: result copies and the assignment
  have hr' : (CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0)[Cp.length + 3]? = some (cu ((a * bb) % m)) := by
    have := cellq Cp [cu a, cu bb, cu m, cu ((a * bb) % m), cu (mrun m 64 (0, a, bb)).2.1, cu 0] Cp.length 3 rfl
    simpa using this
  have d4 := gSM_decl mv P (CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0) vv u64 (vU mv.nv (Cp.length + 3)) (((a * bb) % m : Nat) : Int)
    (((a * bb) % m : Nat) : Int) (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ _ _ hr' hr) (Ty.convert_of_valid _ _ (u64v _ hr))
  have a4 := (pexecM_prim mv fu _ _ _).trans d4
  have e4 : CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [(⟨u64, (((a * bb) % m : Nat) : Int)⟩ : Cell)] =
      CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [cu ((a * bb) % m)] := rfl
  rw [e4] at a4
  have hr6 : (CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [cu ((a * bb) % m)])[Cp.length + 6]? =
      some (cu ((a * bb) % m)) := by
    rw [List.getElem?_append_right (by simp)]; simp
  have d5 := gSM_decl mv P (CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [cu ((a * bb) % m)]) vv u64
    (vU mv.nv (Cp.length + 6)) (((a * bb) % m : Nat) : Int) (((a * bb) % m : Nat) : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ _ _ hr6 hr) (Ty.convert_of_valid _ _ (u64v _ hr))
  have a5 := (pexecM_prim mv fu _ _ _).trans d5
  have e5 : CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [cu ((a * bb) % m)] ++ [(⟨u64, (((a * bb) % m : Nat) : Int)⟩ : Cell)] =
      Cp ++ [cu a, cu bb, cu m, cu ((a * bb) % m), cu (mrun m 64 (0, a, bb)).2.1, cu 0, cu ((a * bb) % m), cu ((a * bb) % m)] := by
    simp [cu]
  rw [e5] at a5
  -- the assignment
  have hs7 : (Cp ++ [cu a, cu bb, cu m, cu ((a * bb) % m), cu (mrun m 64 (0, a, bb)).2.1, cu 0, cu ((a * bb) % m), cu ((a * bb) % m)])[Cp.length + 7]? =
      some (cu ((a * bb) % m)) := by
    rw [List.getElem?_append_right (by omega)]; simp
  have hst : (Cp ++ [cu a, cu bb, cu m, cu ((a * bb) % m), cu (mrun m 64 (0, a, bb)).2.1, cu 0, cu ((a * bb) % m), cu ((a * bb) % m)])[tgt]? =
      some (cu t0) := by
    rw [List.getElem?_append_left hitl]; exact ht
  obtain ⟨rA, hA, retA, psA, vvA, cA, nA, wA⟩ := copy_exec mv P
    (Cp ++ [cu a, cu bb, cu m, cu ((a * bb) % m), cu (mrun m 64 (0, a, bb)).2.1, cu 0, cu ((a * bb) % m), cu ((a * bb) % m)])
    tgt (Cp.length + 7) t0 ((a * bb) % m) hs7 hst hr ht0 vv fu K rK
    (by
      have : (Cp ++ [cu a, cu bb, cu m, cu ((a * bb) % m), cu (mrun m 64 (0, a, bb)).2.1, cu 0, cu ((a * bb) % m), cu ((a * bb) % m)]).set tgt
          (cu ((a * bb) % m)) = callCells Cp tgt a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 := by
        unfold callCells
        rw [List.set_append_left _ _ hitl]
      rw [this]; exact hK)
  have b5 := seqM_some a5 rfl hA
  have b4 := seqM_some a4 rfl b5
  obtain ⟨rM, hM, retM, psM, vvM, cM, nM, wM⟩ := mul_block mv P Cp Cp.length a bb m rfl hab hbb hm vv fu hfu _ _ b4
  have b3 := seqM_some a3 rfl hM
  have b2 := seqM_some a2 rfl b3
  have b1 := seqM_some a1 rfl b2
  refine ⟨_, b1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [retM, retA]
  · rw [psM, psA]
  · rw [vvM, vvA]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cM cA ⊢; omega
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at nM nA ⊢; omega
  · simp [wM, wA]

/-! ### The exponentiation loop -/

abbrev CLp (C0 : List Cell) (x y m pm bb e : Nat) : List Cell := C0 ++ [cu x, cu y, cu m, cu pm, cu bb, cu e]

set_option maxHeartbeats 64000000 in
theorem pow_iter (mv : MV) (P C0 : List Cell) (b x y m pm bb e : Nat) (hC : C0.length = b) (hpm : pm < m) (hbb : bb < m)
    (hm : m < M64) (he : e < M64) (vv : Nat → List Int) (fu : Nat) (hfu : 65 ≤ fu) :
    ∃ res : PRM, pexecM mv fu (powLoop mv.nv b) (gS P (CLp C0 x y m pm bb e)) vv = some res ∧ res.ret = none ∧
      res.ps = gS P (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2)) ∧ res.vv = vv ∧
      res.cost ≤ 2 * (64 * 420 + 300) + 400 ∧ res.need ≤ P.length + 2 * b + 400 ∧ res.wk = 0 := by
  have hm0 : 0 < m := by omega
  have hlen : (CLp C0 x y m pm bb e).length = b + 6 := by simp [hC]
  have h5 := cellq C0 [cu x, cu y, cu m, cu pm, cu bb, cu e] b 5 hC
  have h4 := cellq C0 [cu x, cu y, cu m, cu pm, cu bb, cu e] b 4 hC
  have h3 := cellq C0 [cu x, cu y, cu m, cu pm, cu bb, cu e] b 3 hC
  have h2 := cellq C0 [cu x, cu y, cu m, cu pm, cu bb, cu e] b 2 hC
  have hc := odd_cell mv vv P (CLp C0 x y m pm bb e) (b + 5) e (by simpa using h5) he
  have hpm' : (if e % 2 = 1 then (pm * bb) % m else pm) < m := by
    split
    · exact Nat.mod_lt _ hm0
    · exact hpm
  have hpm'64 : (if e % 2 = 1 then (pm * bb) % m else pm) < M64 := by omega
  -- the first part
  obtain ⟨rr, hs1, ret1, ps1, vv1, cst1, nd1, wk1⟩ : ∃ rr : PRM,
      pexecM mv fu (.branch (oddE mv.nv (b + 5)) (.sequence (.scope (callMul mv.nv (b + 6) (b + 3) (b + 4) (b + 2) (b + 3) Sk)) Sk) Sk)
        (gS P (CLp C0 x y m pm bb e)) vv = some rr ∧ rr.ret = none ∧
        rr.ps = gS P (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) bb e) ∧ rr.vv = vv ∧
        rr.cost ≤ 64 * 420 + 400 ∧ rr.need ≤ P.length + 2 * b + 300 ∧ rr.wk = 0 := by
    by_cases hodd : e % 2 = 1
    · rw [if_pos hodd] at hc
      have hcp3 : (CLp C0 x y m pm bb e)[b + 3]? = some (cu pm) := by simpa using h3
      have hcp4 : (CLp C0 x y m pm bb e)[b + 4]? = some (cu bb) := by simpa using h4
      have hcp2 : (CLp C0 x y m pm bb e)[b + 2]? = some (cu m) := by simpa using h2
      have hsk := pexecM_skip mv fu (gS P (callCells (CLp C0 x y m pm bb e) (b + 3) pm bb m ((pm * bb) % m) (mrun m 64 (0, pm, bb)).2.1)) vv
      obtain ⟨rc, hcr, retc, psc, vvc, cc, nc, wc⟩ := mulcall_exec mv P (CLp C0 x y m pm bb e) (b + 3) (b + 4) (b + 2) (b + 3) pm bb m pm
        hcp3 hcp4 hcp2 hcp3 hpm hbb hm (by omega) vv fu hfu Sk _ hsk
      have hlenC : (CLp C0 x y m pm bb e).length = b + 6 := hlen
      rw [hlenC] at hcr
      have t1 := pexecM_scope mv fu _ _ _ _ hcr
      have hset : (CLp C0 x y m pm bb e).set (b + 3) (cu ((pm * bb) % m)) = CLp C0 x y m ((pm * bb) % m) bb e := by
        unfold CLp; rw [cells_set C0 _ b 3 _ hC]; simp
      have tk : (⟨(gS P (callCells (CLp C0 x y m pm bb e) (b + 3) pm bb m ((pm * bb) % m) (mrun m 64 (0, pm, bb)).2.1)).mem.take
          (gS P (CLp C0 x y m pm bb e)).mem.length,
          (gS P (callCells (CLp C0 x y m pm bb e) (b + 3) pm bb m ((pm * bb) % m) (mrun m 64 (0, pm, bb)).2.1)).bs.take
            (gS P (CLp C0 x y m pm bb e)).bs.length⟩ : PS) = gS P (CLp C0 x y m ((pm * bb) % m) bb e) := by
        unfold callCells
        rw [hset]
        exact gS_takeC P (CLp C0 x y m pm bb e) (CLp C0 x y m ((pm * bb) % m) bb e)
          [cu pm, cu bb, cu m, cu ((pm * bb) % m), cu (mrun m 64 (0, pm, bb)).2.1, cu 0, cu ((pm * bb) % m), cu ((pm * bb) % m)] (by simp)
      simp only [psc] at t1
      simp only [tk] at t1
      have t2 := seqM_some t1 (by simp [retc]) (pexecM_skip mv fu _ _)
      have t3 := pexecM_branch_true mv fu _ _ Sk _ _ 1 hc (by decide) _ t2
      refine ⟨_, t3, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hodd]
      · simpa using vvc
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cc ⊢; omega
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at nc ⊢; omega
      · simp [wc]
    · rw [if_neg hodd] at hc
      have t3 := pexecM_branch_false mv fu _ (.sequence (.scope (callMul mv.nv (b + 6) (b + 3) (b + 4) (b + 2) (b + 3) Sk)) Sk) Sk
        _ _ hc _ (pexecM_skip mv fu _ _)
      refine ⟨_, t3, rfl, ?_, rfl, ?_, ?_, rfl⟩
      · simp [hodd]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  -- the second part
  have hbb' : bb < m := hbb
  have hCp' : (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) bb e).length = b + 6 := by simp [hC]
  have g4 := cellq C0 [cu x, cu y, cu m, cu (if e % 2 = 1 then (pm * bb) % m else pm), cu bb, cu e] b 4 hC
  have g2 := cellq C0 [cu x, cu y, cu m, cu (if e % 2 = 1 then (pm * bb) % m else pm), cu bb, cu e] b 2 hC
  have g5 := cellq C0 [cu x, cu y, cu m, cu (if e % 2 = 1 then (pm * bb) % m else pm), cu bb, cu e] b 5 hC
  have hbbm : (bb * bb) % m < M64 := by have := Nat.mod_lt (bb * bb) hm0; omega
  -- halving the exponent in the extended state
  have hsetE : ((CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) bb e).set (b + 4) (cu ((bb * bb) % m)) ++
      [cu bb, cu bb, cu m, cu ((bb * bb) % m), cu (mrun m 64 (0, bb, bb)).2.1, cu 0, cu ((bb * bb) % m), cu ((bb * bb) % m)]).set (b + 5)
        (cu (e / 2)) =
      CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2) ++
        [cu bb, cu bb, cu m, cu ((bb * bb) % m), cu (mrun m 64 (0, bb, bb)).2.1, cu 0, cu ((bb * bb) % m), cu ((bb * bb) % m)] := by
    rw [List.set_append_left _ _ (by simp [hC])]
    unfold CLp
    rw [cells_set C0 _ b 4 _ hC, cells_set C0 _ b 5 _ hC]
    simp
  have hcE : (callCells (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) bb e) (b + 4) bb bb m ((bb * bb) % m)
      (mrun m 64 (0, bb, bb)).2.1)[b + 5]? = some (cu e) := by
    unfold callCells
    rw [List.getElem?_append_left (by simp [hC])]
    rw [List.getElem?_set_ne (by omega)]
    simpa using g5
  obtain ⟨rh, hh, reth, psh, vvh, ch, nh, wh⟩ := halve_exec mv P
    (callCells (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) bb e) (b + 4) bb bb m ((bb * bb) % m)
      (mrun m 64 (0, bb, bb)).2.1) (b + 5) e hcE he vv fu Sk
    ⟨gS P (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2) ++
        [cu bb, cu bb, cu m, cu ((bb * bb) % m), cu (mrun m 64 (0, bb, bb)).2.1, cu 0, cu ((bb * bb) % m), cu ((bb * bb) % m)]), vv, none, 0,
      (gS P (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2) ++
        [cu bb, cu bb, cu m, cu ((bb * bb) % m), cu (mrun m 64 (0, bb, bb)).2.1, cu 0, cu ((bb * bb) % m), cu ((bb * bb) % m)])).mem.length +
      (gS P (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2) ++
        [cu bb, cu bb, cu m, cu ((bb * bb) % m), cu (mrun m 64 (0, bb, bb)).2.1, cu 0, cu ((bb * bb) % m), cu ((bb * bb) % m)])).bs.length, 0⟩
    (by
      unfold callCells
      rw [hsetE]
      exact pexecM_skip mv fu _ _)
  have g4' : (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) bb e)[b + 4]? = some (cu bb) := by simpa using g4
  have g2' : (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) bb e)[b + 2]? = some (cu m) := by simpa using g2
  obtain ⟨rc2, hc2, retc2, psc2, vvc2, cc2, nc2, wc2⟩ := mulcall_exec mv P
    (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) bb e) (b + 4) (b + 4) (b + 2) (b + 4) bb bb m bb g4' g4' g2' g4' hbb hbb hm
    (by omega) vv fu hfu _ rh hh
  rw [hCp'] at hc2
  have s1 := seqM_some hs1 ret1 (by rw [ps1, vv1]; exact hc2)
  have s2 := pexecM_scope mv fu _ _ _ _ s1
  simp only [psc2, psh] at s2
  have tk2 : (⟨(gS P (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2) ++
        [cu bb, cu bb, cu m, cu ((bb * bb) % m), cu (mrun m 64 (0, bb, bb)).2.1, cu 0, cu ((bb * bb) % m), cu ((bb * bb) % m)])).mem.take
        (gS P (CLp C0 x y m pm bb e)).mem.length,
      (gS P (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2) ++
        [cu bb, cu bb, cu m, cu ((bb * bb) % m), cu (mrun m 64 (0, bb, bb)).2.1, cu 0, cu ((bb * bb) % m), cu ((bb * bb) % m)])).bs.take
        (gS P (CLp C0 x y m pm bb e)).bs.length⟩ : PS) =
      gS P (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2)) :=
    gS_takeC P (CLp C0 x y m pm bb e) (CLp C0 x y m (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2))
      [cu bb, cu bb, cu m, cu ((bb * bb) % m), cu (mrun m 64 (0, bb, bb)).2.1, cu 0, cu ((bb * bb) % m), cu ((bb * bb) % m)] (by simp)
  simp only [tk2] at s2
  have hret2 : rc2.ret = none := by rw [retc2]; exact reth
  have s3 := seqM_some s2 (by simp [hret2]) (pexecM_skip mv fu _ _)
  refine ⟨_, s3, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show rc2.vv = vv
    rw [vvc2]
    exact vvh
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cst1 cc2 ch ⊢; omega
  · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at nd1 nc2 nh ⊢; omega
  · simp [wk1, wc2, wh]

def pstep (m : Nat) (s : Nat × Nat × Nat) : Nat × Nat × Nat :=
  ((if s.2.2 % 2 = 1 then (s.1 * s.2.1) % m else s.1), (s.2.1 * s.2.1) % m, s.2.2 / 2)

def prun (m : Nat) : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, s => s
  | k + 1, s => if s.2.2 = 0 then s else prun m k (pstep m s)

theorem powstep_mod (m pm bb e : Nat) :
    ((if e % 2 = 1 then (pm * bb) % m else pm) * (((bb * bb) % m) ^ (e / 2))) % m = (pm * bb ^ e) % m := by
  have hee : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
  have hpow : (bb * bb) ^ (e / 2) = bb ^ (2 * (e / 2)) := by rw [← Nat.pow_two, ← Nat.pow_mul]
  have hc : ((bb * bb) % m) ^ (e / 2) % m = (bb * bb) ^ (e / 2) % m := (Nat.pow_mod _ _ _).symm
  by_cases hodd : e % 2 = 1
  · rw [if_pos hodd, Nat.mul_mod, Nat.mod_mod, hc, ← Nat.mul_mod, Nat.mul_assoc, hpow]
    have : pm * (bb * bb ^ (2 * (e / 2))) = pm * bb ^ e := by
      congr 1
      conv_rhs => rw [hee, hodd]
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [this]
  · have h0 : e % 2 = 0 := by omega
    rw [if_neg hodd, Nat.mul_mod, hc, ← Nat.mul_mod, hpow]
    have : bb ^ (2 * (e / 2)) = bb ^ e := by conv_rhs => rw [hee, h0]; simp
    rw [this]

theorem prun_spec (m : Nat) (hm : 0 < m) : ∀ (k pm bb e : Nat), pm < m → bb < m → e < 2 ^ k →
    (prun m k (pm, bb, e)).1 < m ∧ (prun m k (pm, bb, e)).1 = (pm * bb ^ e) % m ∧ (prun m k (pm, bb, e)).2.1 < m ∧
      (prun m k (pm, bb, e)).2.2 = 0 := by
  intro k
  induction k with
  | zero =>
    intro pm bb e hp hb he
    have : e = 0 := by simpa using he
    subst this
    simp [prun]
    exact ⟨hp, (Nat.mod_eq_of_lt hp).symm, hb⟩
  | succ k ih =>
    intro pm bb e hp hb he
    by_cases h0 : e = 0
    · subst h0
      simp [prun]
      exact ⟨hp, (Nat.mod_eq_of_lt hp).symm, hb⟩
    · simp only [prun, if_neg h0]
      have he' : e / 2 < 2 ^ k := by rw [Nat.pow_succ] at he; omega
      have hp' : (if e % 2 = 1 then (pm * bb) % m else pm) < m := by
        split
        · exact Nat.mod_lt _ hm
        · exact hp
      obtain ⟨h1, h2, h3, h4⟩ := ih (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2) hp' (Nat.mod_lt _ hm) he'
      have eq : pstep m (pm, bb, e) = ((if e % 2 = 1 then (pm * bb) % m else pm), (bb * bb) % m, e / 2) := rfl
      rw [eq]
      exact ⟨h1, by rw [h2]; exact powstep_mod m pm bb e, h3, h4⟩

def CPW (n : Nat) : Nat := 2 * (64 * 420 + 300) + 460

set_option maxHeartbeats 128000000 in
/-- The loop `while (e != 0)` of the exponentiation. -/
theorem pow_while (mv : MV) (P C0 : List Cell) (b x y m : Nat) (hC : C0.length = b) (hm : m < M64) (vv : Nat → List Int) (G : Nat) (hG : CPW 0 ≤ G) :
    ∀ (k pm bb e fu : Nat), e < 2 ^ k → pm < m → bb < m → e < M64 → k + 65 ≤ fu →
      ∃ res : PRM, pexecM mv fu (.whileLoop (.binary bT .ne (vU mv.nv (b + 5)) zU) (powLoop mv.nv b))
        (gS P (CLp C0 x y m pm bb e)) vv = some res ∧ res.ret = none ∧
        res.ps = gS P (CLp C0 x y m (prun m k (pm, bb, e)).1 (prun m k (pm, bb, e)).2.1 (prun m k (pm, bb, e)).2.2) ∧
        res.vv = vv ∧ res.cost ≤ k * G + 30 ∧ res.need ≤ P.length + 2 * b + 400 ∧ res.wk = 0 := by
  intro k
  induction k with
  | zero =>
    intro pm bb e fu he0 hp hb he hfu
    have he' : e = 0 := by simpa using he0
    subst he'
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have h5 := cellq C0 [cu x, cu y, cu m, cu pm, cu bb, cu 0] b 5 hC
    have hc := ne_zero_cell mv vv P (CLp C0 x y m pm bb 0) (b + 5) 0 (by simpa using h5) he
    rw [if_neg (by simp)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  | succ k ih =>
    intro pm bb e fu hek hp hb he hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have h5 := cellq C0 [cu x, cu y, cu m, cu pm, cu bb, cu e] b 5 hC
    have hc := ne_zero_cell mv vv P (CLp C0 x y m pm bb e) (b + 5) e (by simpa using h5) he
    by_cases hz : e = 0
    · subst hz
      rw [if_neg (by simp)] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
      · simp [prun]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly]; omega
    · rw [if_pos hz] at hc
      obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := pow_iter mv P C0 b x y m pm bb e hC hp hb hm he vv (fu' + 1) (by omega)
      have hp' : (if e % 2 = 1 then (pm * bb) % m else pm) < m := by
        split
        · exact Nat.mod_lt _ (by omega)
        · exact hp
      have he2 : e / 2 < 2 ^ k := by rw [Nat.pow_succ] at hek; omega
      obtain ⟨r2, h2, ret2, ps2, vv2, c2, n2, w2⟩ := ih (if e % 2 = 1 then (pm * bb) % m else pm) ((bb * bb) % m) (e / 2) fu' he2
        hp' (Nat.mod_lt _ (by omega)) (by omega) (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false]
      rw [h1]
      simp only [ret1, ps1, vv1]
      rw [h2]
      simp only
      refine ⟨_, rfl, ret2, ?_, vv2, ?_, ?_, ?_⟩
      · rw [ps2]
        have e : prun m (k + 1) (pm, bb, e) = prun m k (pstep m (pm, bb, e)) := by simp [prun, hz]
        rw [e]; rfl
      · rw [Nat.succ_mul]
        have hCPW : CPW 0 = 2 * (64 * 420 + 300) + 460 := rfl
        simp [vwp, NExpr.nodes, NExpr.scalarOnly] at c1 c2 ⊢; omega
      · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at n1 n2 ⊢; omega
      · simp [w1, w2]

/-! ### The exponentiation block and the calls with a declared result -/

set_option maxHeartbeats 64000000 in
theorem pow_block (mv : MV) (P C0 : List Cell) (b x y m : Nat) (hC : C0.length = b) (hx : x < m) (hm : 2 ≤ m) (hm64 : m < M64)
    (hy : y < M64) (vv : Nat → List Int) (fu : Nat) (hfu : 64 + 65 ≤ fu) (rest : Command) (rR : PRM)
    (hrest : pexecM mv fu rest (gS P (CLp C0 x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0)) vv = some rR) :
    ∃ res : PRM, pexecM mv fu (powBody mv.nv b rest) (gS P (C0 ++ [cu x, cu y, cu m])) vv = some res ∧
      res.ret = rR.ret ∧ res.ps = rR.ps ∧ res.vv = rR.vv ∧ res.cost ≤ rR.cost + 64 * CPW 0 + 200 ∧
      res.need ≤ max rR.need (P.length + 2 * b + 400) ∧ res.wk = rR.wk := by
  have hm0 : 0 < m := by omega
  have hx64 : x < M64 := by omega
  have hl3 : (C0 ++ [cu x, cu y, cu m]).length = b + 3 := by simp [hC]
  have hone : 1 < m := by omega
  have d1 := gSM_decl mv P (C0 ++ [cu x, cu y, cu m]) vv u64 oU 1 1 (by rw [vdenM_scalar mv vv _ _ rfl]; exact oU_den _)
    (Ty.convert_of_valid _ _ (u64v 1 (by decide)))
  have a1 := (pexecM_prim mv fu _ _ _).trans d1
  have e1 : C0 ++ [cu x, cu y, cu m] ++ [(⟨u64, 1⟩ : Cell)] = C0 ++ [cu x, cu y, cu m, cu 1] := by simp [cu]
  rw [e1] at a1
  have hxa : (vU mv.nv b).denote (penvN mv.nv (gS P (C0 ++ [cu x, cu y, cu m, cu 1]))) = some (x : Int) :=
    var_den mv P _ b x (by have := cellq C0 [cu x, cu y, cu m, cu 1] b 0 hC; simpa using this) hx64
  have d2 := gSM_decl mv P (C0 ++ [cu x, cu y, cu m, cu 1]) vv u64 (vU mv.nv b) (x : Int) (x : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact hxa) (Ty.convert_of_valid _ _ (u64v x hx64))
  have a2 := (pexecM_prim mv fu _ _ _).trans d2
  have e2 : C0 ++ [cu x, cu y, cu m, cu 1] ++ [(⟨u64, (x : Int)⟩ : Cell)] = C0 ++ [cu x, cu y, cu m, cu 1, cu x] := by simp [cu]
  rw [e2] at a2
  have hyb : (vU mv.nv (b + 1)).denote (penvN mv.nv (gS P (C0 ++ [cu x, cu y, cu m, cu 1, cu x]))) = some (y : Int) :=
    var_den mv P _ (b + 1) y (by have := cellq C0 [cu x, cu y, cu m, cu 1, cu x] b 1 hC; simpa using this) hy
  have d3 := gSM_decl mv P (C0 ++ [cu x, cu y, cu m, cu 1, cu x]) vv u64 (vU mv.nv (b + 1)) (y : Int) (y : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact hyb) (Ty.convert_of_valid _ _ (u64v y hy))
  have a3 := (pexecM_prim mv fu _ _ _).trans d3
  have e3 : C0 ++ [cu x, cu y, cu m, cu 1, cu x] ++ [(⟨u64, (y : Int)⟩ : Cell)] = CLp C0 x y m 1 x y := by simp [cu]
  rw [e3] at a3
  obtain ⟨rw_, hw, retw, psw, vvw, cw, nw, ww⟩ := pow_while mv P C0 b x y m hC hm64 vv (CPW 0) (Nat.le_refl _) 64 1 x y fu (by rw [pow64]; exact hy) hone hx hy
    (by omega)
  have hspec := prun_spec m hm0 64 1 x y hone hx (by rw [pow64]; exact hy)
  have hps : rw_.ps = gS P (CLp C0 x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0) := by
    rw [psw, hspec.2.2.2, hspec.2.1]; simp
  have hrest' : pexecM mv fu rest rw_.ps rw_.vv = some rR := by rw [hps, vvw]; exact hrest
  have b3 := seqM_some hw retw hrest'
  have b2 := seqM_some a3 rfl b3
  have b1 := seqM_some a2 rfl b2
  have b0 := seqM_some a1 rfl b1
  refine ⟨_, b0, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cw ⊢; omega
  · simp [gS_mem_len, gS_bs_len, hC, vwp, NExpr.nodes, NExpr.scalarOnly] at nw ⊢; omega
  · simp [ww]

abbrev callCellsD (Cp : List Cell) (a bb m r xf : Nat) : List Cell :=
  Cp ++ [cu a, cu bb, cu m, cu r, cu xf, cu 0, cu r, cu r]

set_option maxHeartbeats 64000000 in
theorem mulcallD_exec (mv : MV) (P Cp : List Cell) (ia ib im a bb m : Nat) (hia : Cp[ia]? = some (cu a))
    (hib : Cp[ib]? = some (cu bb)) (him : Cp[im]? = some (cu m)) (hab : a < m) (hbb : bb < m)
    (hm : m < M64) (vv : Nat → List Int) (fu : Nat) (hfu : 65 ≤ fu) (K : Command) (rK : PRM)
    (hK : pexecM mv fu K (gS P (callCellsD Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1)) vv = some rK) :
    ∃ res : PRM, pexecM mv fu (callMulD mv.nv Cp.length ia ib im K) (gS P Cp) vv = some res ∧ res.ret = rK.ret ∧
      res.ps = rK.ps ∧ res.vv = rK.vv ∧ res.cost ≤ rK.cost + 64 * 420 + 300 ∧
      res.need ≤ max rK.need (P.length + 2 * Cp.length + 150) ∧ res.wk = rK.wk := by
  have ha64 : a < M64 := by omega
  have hb64 : bb < M64 := by omega
  have hm0 : 0 < m := by omega
  have hr : (a * bb) % m < M64 := by have := Nat.mod_lt (a * bb) hm0; omega
  have d1 := gSM_decl mv P Cp vv u64 (vU mv.nv ia) (a : Int) (a : Int) (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P Cp ia a hia ha64)
    (Ty.convert_of_valid _ _ (u64v a ha64))
  have a1 := (pexecM_prim mv fu _ _ _).trans d1
  have hib' : (Cp ++ [cu a])[ib]? = some (cu bb) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hib).1]; exact hib
  have d2 := gSM_decl mv P (Cp ++ [cu a]) vv u64 (vU mv.nv ib) (bb : Int) (bb : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ ib bb hib' hb64) (Ty.convert_of_valid _ _ (u64v bb hb64))
  have a2 := (pexecM_prim mv fu _ _ _).trans d2
  have e2 : Cp ++ [cu a] ++ [(⟨u64, (bb : Int)⟩ : Cell)] = Cp ++ [cu a, cu bb] := by simp [cu]
  rw [e2] at a2
  have him' : (Cp ++ [cu a, cu bb])[im]? = some (cu m) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp him).1]; exact him
  have d3 := gSM_decl mv P (Cp ++ [cu a, cu bb]) vv u64 (vU mv.nv im) (m : Int) (m : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ im m him' hm) (Ty.convert_of_valid _ _ (u64v m hm))
  have a3 := (pexecM_prim mv fu _ _ _).trans d3
  have e3 : Cp ++ [cu a, cu bb] ++ [(⟨u64, (m : Int)⟩ : Cell)] = Cp ++ [cu a, cu bb, cu m] := by simp [cu]
  rw [e3] at a3
  have hr' : (CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0)[Cp.length + 3]? = some (cu ((a * bb) % m)) := by
    have := cellq Cp [cu a, cu bb, cu m, cu ((a * bb) % m), cu (mrun m 64 (0, a, bb)).2.1, cu 0] Cp.length 3 rfl
    simpa using this
  have d4 := gSM_decl mv P (CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0) vv u64 (vU mv.nv (Cp.length + 3)) (((a * bb) % m : Nat) : Int)
    (((a * bb) % m : Nat) : Int) (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ _ _ hr' hr) (Ty.convert_of_valid _ _ (u64v _ hr))
  have a4 := (pexecM_prim mv fu _ _ _).trans d4
  have e4 : CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [(⟨u64, (((a * bb) % m : Nat) : Int)⟩ : Cell)] =
      CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [cu ((a * bb) % m)] := rfl
  rw [e4] at a4
  have hr6 : (CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [cu ((a * bb) % m)])[Cp.length + 6]? =
      some (cu ((a * bb) % m)) := by
    rw [List.getElem?_append_right (by simp)]; simp
  have d5 := gSM_decl mv P (CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [cu ((a * bb) % m)]) vv u64
    (vU mv.nv (Cp.length + 6)) (((a * bb) % m : Nat) : Int) (((a * bb) % m : Nat) : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ _ _ hr6 hr) (Ty.convert_of_valid _ _ (u64v _ hr))
  have a5 := (pexecM_prim mv fu _ _ _).trans d5
  have e5 : CLm Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 0 ++ [cu ((a * bb) % m)] ++ [(⟨u64, (((a * bb) % m : Nat) : Int)⟩ : Cell)] =
      callCellsD Cp a bb m ((a * bb) % m) (mrun m 64 (0, a, bb)).2.1 := by
    simp [cu]
  rw [e5] at a5
  have b5 := seqM_some a5 rfl hK
  have b4 := seqM_some a4 rfl b5
  obtain ⟨rM, hM, retM, psM, vvM, cM, nM, wM⟩ := mul_block mv P Cp Cp.length a bb m rfl hab hbb hm vv fu hfu _ _ b4
  have b3 := seqM_some a3 rfl hM
  have b2 := seqM_some a2 rfl b3
  have b1 := seqM_some a1 rfl b2
  refine ⟨_, b1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [retM]
  · rw [psM]
  · rw [vvM]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cM ⊢; omega
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at nM ⊢; omega
  · simp [wM]

abbrev callCellsP (Cp : List Cell) (x y m : Nat) : List Cell :=
  CLp Cp x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0 ++ [cu ((x ^ y) % m), cu ((x ^ y) % m)]

set_option maxHeartbeats 64000000 in
theorem powcallD_exec (mv : MV) (P Cp : List Cell) (ix iy im x y m : Nat) (hix : Cp[ix]? = some (cu x))
    (hiy : Cp[iy]? = some (cu y)) (him : Cp[im]? = some (cu m)) (hx : x < m) (hm2 : 2 ≤ m) (hm : m < M64) (hy : y < M64)
    (vv : Nat → List Int) (fu : Nat) (hfu : 64 + 65 ≤ fu) (K : Command) (rK : PRM)
    (hK : pexecM mv fu K (gS P (callCellsP Cp x y m)) vv = some rK) :
    ∃ res : PRM, pexecM mv fu (callPowD mv.nv Cp.length ix iy im K) (gS P Cp) vv = some res ∧ res.ret = rK.ret ∧
      res.ps = rK.ps ∧ res.vv = rK.vv ∧ res.cost ≤ rK.cost + 64 * CPW 0 + 300 ∧
      res.need ≤ max rK.need (P.length + 2 * Cp.length + 400) ∧ res.wk = rK.wk := by
  have hx64 : x < M64 := by omega
  have hm0 : 0 < m := by omega
  have hr : (x ^ y) % m < M64 := by have := Nat.mod_lt (x ^ y) hm0; omega
  have d1 := gSM_decl mv P Cp vv u64 (vU mv.nv ix) (x : Int) (x : Int) (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P Cp ix x hix hx64)
    (Ty.convert_of_valid _ _ (u64v x hx64))
  have a1 := (pexecM_prim mv fu _ _ _).trans d1
  have hiy' : (Cp ++ [cu x])[iy]? = some (cu y) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hiy).1]; exact hiy
  have d2 := gSM_decl mv P (Cp ++ [cu x]) vv u64 (vU mv.nv iy) (y : Int) (y : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ iy y hiy' hy) (Ty.convert_of_valid _ _ (u64v y hy))
  have a2 := (pexecM_prim mv fu _ _ _).trans d2
  have e2 : Cp ++ [cu x] ++ [(⟨u64, (y : Int)⟩ : Cell)] = Cp ++ [cu x, cu y] := by simp [cu]
  rw [e2] at a2
  have him' : (Cp ++ [cu x, cu y])[im]? = some (cu m) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp him).1]; exact him
  have d3 := gSM_decl mv P (Cp ++ [cu x, cu y]) vv u64 (vU mv.nv im) (m : Int) (m : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ im m him' hm) (Ty.convert_of_valid _ _ (u64v m hm))
  have a3 := (pexecM_prim mv fu _ _ _).trans d3
  have e3 : Cp ++ [cu x, cu y] ++ [(⟨u64, (m : Int)⟩ : Cell)] = Cp ++ [cu x, cu y, cu m] := by simp [cu]
  rw [e3] at a3
  have hr' : (CLp Cp x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0)[Cp.length + 3]? = some (cu ((x ^ y) % m)) := by
    have := cellq Cp [cu x, cu y, cu m, cu ((x ^ y) % m), cu (prun m 64 (1, x, y)).2.1, cu 0] Cp.length 3 rfl
    simpa using this
  have d4 := gSM_decl mv P (CLp Cp x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0) vv u64 (vU mv.nv (Cp.length + 3)) (((x ^ y) % m : Nat) : Int)
    (((x ^ y) % m : Nat) : Int) (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ _ _ hr' hr) (Ty.convert_of_valid _ _ (u64v _ hr))
  have a4 := (pexecM_prim mv fu _ _ _).trans d4
  have e4 : CLp Cp x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0 ++ [(⟨u64, (((x ^ y) % m : Nat) : Int)⟩ : Cell)] =
      CLp Cp x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0 ++ [cu ((x ^ y) % m)] := rfl
  rw [e4] at a4
  have hr6 : (CLp Cp x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0 ++ [cu ((x ^ y) % m)])[Cp.length + 6]? =
      some (cu ((x ^ y) % m)) := by
    rw [List.getElem?_append_right (by simp)]; simp
  have d5 := gSM_decl mv P (CLp Cp x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0 ++ [cu ((x ^ y) % m)]) vv u64
    (vU mv.nv (Cp.length + 6)) (((x ^ y) % m : Nat) : Int) (((x ^ y) % m : Nat) : Int)
    (by rw [vdenM_scalar mv vv _ _ rfl]; exact var_den mv P _ _ _ hr6 hr) (Ty.convert_of_valid _ _ (u64v _ hr))
  have a5 := (pexecM_prim mv fu _ _ _).trans d5
  have e5 : CLp Cp x y m ((x ^ y) % m) (prun m 64 (1, x, y)).2.1 0 ++ [cu ((x ^ y) % m)] ++ [(⟨u64, (((x ^ y) % m : Nat) : Int)⟩ : Cell)] =
      callCellsP Cp x y m := by
    simp [cu]
  rw [e5] at a5
  have b5 := seqM_some a5 rfl hK
  have b4 := seqM_some a4 rfl b5
  obtain ⟨rM, hM, retM, psM, vvM, cM, nM, wM⟩ := pow_block mv P Cp Cp.length x y m rfl hx hm2 hm hy vv fu hfu _ _ b4
  have b3 := seqM_some a3 rfl hM
  have b2 := seqM_some a2 rfl b3
  have b1 := seqM_some a1 rfl b2
  refine ⟨_, b1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [retM]
  · rw [psM]
  · rw [vvM]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at cM ⊢; omega
  · simp [gS_mem_len, gS_bs_len, vwp, NExpr.nodes, NExpr.scalarOnly] at nM ⊢; omega
  · simp [wM]

/-! ### `mr_witness` -/

abbrev cb (f : Bool) : Cell := ⟨bT, if f then 1 else 0⟩
abbrev cI (i : Nat) : Cell := ⟨i32, (i : Int)⟩

theorem i32vn (x : Nat) (h : x < 2147483648) : i32.valid (x : Int) = true := by
  exact Proofs.LowerBoundIndexCall.validN x h

theorem vari_den (mv : MV) (P cl : List Cell) (c i : Nat) (hc : cl[c]? = some (cI i)) (hi : i < 2147483648) :
    (NExpr.variable i32 (mv.nv + c)).denote (penvN mv.nv (gS P cl)) = some (i : Int) := by
  rw [den_variable]
  exact envs mv P cl c (cI i) hc (i32vn i hi)

theorem varb_den (mv : MV) (P cl : List Cell) (c : Nat) (f : Bool) (hc : cl[c]? = some (cb f)) :
    (NExpr.variable bT (mv.nv + c)).denote (penvN mv.nv (gS P cl)) = some (if f then 1 else 0) := by
  rw [den_variable]
  exact envs mv P cl c (cb f) hc (by cases f <;> decide)

theorem den_and_b (env : Nat → Ty → Option Int) (l r : NExpr) :
    (NExpr.logical true l r).denote env = (l.denote env).bind fun a =>
      if a == 0 then some 0 else (r.denote env).bind fun b => some (if b == 0 then 0 else 1) := by
  simp [NExpr.denote]

abbrev WS (n d r a pm bbf x : Nat) (w : Bool) : List Cell :=
  [cu n, cu d, cI r, cu a, cb w, cu a, cu d, cu n, cu pm, cu bbf, cu 0, cu pm, cu x]
abbrev Wc (n d r a pm bbf x : Nat) (w cf : Bool) (i : Nat) : List Cell := WS n d r a pm bbf x w ++ [cb cf, cI i]

abbrev witK (nv : Nat) : Command :=
  .sequence (.primitive (.assign (nv + 12) u64 (vU nv 22)))
    (.sequence (.branch (.binary bT .eq (vU nv 12) (.binary u64 .sub (vU nv 0) oU))
      (.sequence (.scope (.sequence (.primitive (.assign (nv + 13) bT (.literal bT 0))) Sk)) Sk) Sk)
    (.sequence (.primitive (.assign (nv + 14) i32 (.binary i32 .add (.variable i32 (nv + 14)) (.literal i32 1)))) Sk))

theorem cells_get (L : List Cell) (i : Nat) (c : Cell) (h : L[i]? = some c) (M : List Cell) : (L ++ M)[i]? = some c := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h

theorem inc_exec (mv : MV) (P cl : List Cell) (c i : Nat) (hc : cl[c]? = some (cI i)) (hi : i + 1 < 2147483648)
    (vv : Nat → List Int) (fu : Nat) (K : Command) (rK : PRM)
    (hK : pexecM mv fu K (gS P (cl.set c (cI (i + 1)))) vv = some rK) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (.assign (mv.nv + c) i32
        (.binary i32 .add (.variable i32 (mv.nv + c)) (.literal i32 1)))) K) (gS P cl) vv = some r ∧
      r.ret = rK.ret ∧ r.ps = rK.ps ∧ r.vv = rK.vv ∧ r.cost ≤ rK.cost + 20 ∧
      r.need ≤ max rK.need (P.length + 2 * cl.length + 20) ∧ r.wk = rK.wk := by
  have htl : c < cl.length := (List.getElem?_eq_some_iff.mp hc).1
  have env : penvN mv.nv (gS P cl) (mv.nv + c) i32 = some (i : Int) := envs mv P cl c (cI i) hc (i32vn i (by omega))
  have hv := Proofs.RunLengthExec.inc_val mv vv (penvN mv.nv (gS P cl)) (mv.nv + c) i env hi
  have s := gSM_assign mv P cl vv c htl i32 _ ((i + 1 : Nat) : Int) ((i + 1 : Nat) : Int) hv (cI i) hc rfl (i32vn i (by omega))
    (Ty.convert_of_valid _ _ (i32vn (i + 1) hi))
  have a1 := (pexecM_prim mv fu _ _ _).trans s
  have hK' : pexecM mv fu K ((⟨gS P (cl.set c ⟨i32, ((i + 1 : Nat) : Int)⟩), vv, none, (vwp (.binary i32 .add (.variable i32 (mv.nv + c)) (.literal i32 1))).1 + 1,
      P.length + 2 * cl.length + (vwp (.binary i32 .add (.variable i32 (mv.nv + c)) (.literal i32 1))).2 + 2, 0⟩ : PRM).ps)
      ((⟨gS P (cl.set c ⟨i32, ((i + 1 : Nat) : Int)⟩), vv, none, (vwp (.binary i32 .add (.variable i32 (mv.nv + c)) (.literal i32 1))).1 + 1,
      P.length + 2 * cl.length + (vwp (.binary i32 .add (.variable i32 (mv.nv + c)) (.literal i32 1))).2 + 2, 0⟩ : PRM).vv) = some rK := hK
  have s1 := seqM_some a1 rfl hK'
  refine ⟨_, s1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
  · simp

def wrun (n r : Nat) : Nat → Nat × Bool × Nat → Nat × Bool × Nat
  | 0, s => s
  | k + 1, (x, cf, i) =>
    if i + 1 < r ∧ cf = true then wrun n r k ((x * x) % n, decide ((x * x) % n ≠ n - 1), i + 1) else (x, cf, i)

def CWL : Nat := 64 * 420 + 1500
def CWr (r : Nat) : Nat := r * CWL

def mrwx (n r x : Nat) : Bool :=
  if x = 1 then false else if x = n - 1 then false else (wrun n r r (x, true, 0)).2.1

end Proofs.IsPrimeExec
