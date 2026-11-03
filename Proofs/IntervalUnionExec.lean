import Proofs.CompressExec
import Proofs.ForLoopB
import Proofs.IntervalUnionMath
import Proofs.Generated.IntervalUnion

namespace Proofs.IntervalUnionExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.MatMulExec (vdenM_binary idx_lt n_small)
open Proofs.CompressExec (rdM_valI pexecM_branch_true pexecM_branch_false idxC_den size_valMk)
open Proofs.IntervalUnionMath

abbrev cs64 (x : Int) : Cell := ⟨s64, x⟩

/-- The contents of the four vectors `l`, `r`, `ret_l`, `ret_r`. -/
def V4 (X0 X1 X2 X3 : List Int) : Nat → List Int := fun k =>
  if k = 0 then X0 else if k = 1 then X1 else if k = 2 then X2 else if k = 3 then X3 else []

theorem V4_get0 (X0 X1 X2 X3 : List Int) : V4 X0 X1 X2 X3 0 = X0 := by simp [V4]
theorem V4_get1 (X0 X1 X2 X3 : List Int) : V4 X0 X1 X2 X3 1 = X1 := by simp [V4]
theorem V4_get2 (X0 X1 X2 X3 : List Int) : V4 X0 X1 X2 X3 2 = X2 := by simp [V4]
theorem V4_get3 (X0 X1 X2 X3 : List Int) : V4 X0 X1 X2 X3 3 = X3 := by simp [V4]

theorem V4_upd0 (X0 X1 X2 X3 Y : List Int) : upd (V4 X0 X1 X2 X3) 0 Y = V4 Y X1 X2 X3 := by
  funext k; unfold upd V4
  by_cases h0 : k = 0
  · subst h0; simp
  · simp [h0]
theorem V4_upd1 (X0 X1 X2 X3 Y : List Int) : upd (V4 X0 X1 X2 X3) 1 Y = V4 X0 Y X2 X3 := by
  funext k; unfold upd V4
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · simp [h0, h1]
theorem V4_upd2 (X0 X1 X2 X3 Y : List Int) : upd (V4 X0 X1 X2 X3) 2 Y = V4 X0 X1 Y X3 := by
  funext k; unfold upd V4
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h2 : k = 2
      · subst h2; simp
      · simp [h0, h1, h2]
theorem V4_upd3 (X0 X1 X2 X3 Y : List Int) : upd (V4 X0 X1 X2 X3) 3 Y = V4 X0 X1 X2 Y := by
  funext k; unfold upd V4
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; simp
    · by_cases h2 : k = 2
      · subst h2; simp
      · by_cases h3 : k = 3
        · subst h3; simp
        · simp [h0, h1, h2, h3]

/-! ### The programs (nv = 4: slots 0 `l`, 1 `r`, 2 `ret_l`, 3 `ret_r`; variable 4 = `n`) -/

abbrev idxJ1 (v : Nat) : NExpr := .cast u64 (.binary i32 .sub (.variable i32 v) (.literal i32 1))
abbrev idxV (v : Nat) : NExpr := .cast u64 (.variable i32 v)
abbrev cmpE : NExpr := .logical false (.binary bT .lt (.variable s64 9) (.variable s64 8))
  (.logical true (.binary bT .eq (.variable s64 8) (.variable s64 9)) (.binary bT .lt (.variable s64 11) (.variable s64 10)))
abbrev stopGo : Command := .sequence (.scope (.sequence (.primitive (.assign 7 i32 (.literal i32 0))) (.primitive .skip))) (.primitive .skip)
abbrev swapThen : Command :=
  .sequence (.scope (.sequence (.primitive (.write (.local 0) s64 (idxJ1 6) (.variable s64 9)))
    (.sequence (.primitive (.write (.local 0) s64 (idxV 6) (.variable s64 8)))
      (.sequence (.primitive (.write (.local 1) s64 (idxJ1 6) (.variable s64 11)))
        (.sequence (.primitive (.write (.local 1) s64 (idxV 6) (.variable s64 10)))
          (.sequence (.primitive (.assign 6 i32 (.binary i32 .sub (.variable i32 6) (.literal i32 1))))
            (.sequence (.branch (.binary bT .eq (.variable i32 6) (.literal i32 0)) stopGo (.primitive .skip)) (.primitive .skip))))))))
    (.primitive .skip)
abbrev sinkBody : Command :=
  .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (idxJ1 6))))
    (.sequence (.primitive (.declare s64 true (.read s64 (.local 0) (idxV 6))))
      (.sequence (.primitive (.declare s64 true (.read s64 (.local 1) (idxJ1 6))))
        (.sequence (.primitive (.declare s64 true (.read s64 (.local 1) (idxV 6))))
          (.sequence (.primitive (.declare bT true cmpE))
            (.sequence (.branch (.variable bT 12) swapThen stopGo) (.primitive .skip))))))
abbrev sinkCond : NExpr := .binary bT .ne (.variable i32 7) (.literal i32 0)
abbrev sinkLoop : Command := .whileLoop sinkCond (.sequence (.scope sinkBody) (.primitive .skip))
abbrev sortB : Command :=
  .sequence (.primitive (.declare i32 true (.variable i32 5)))
    (.sequence (.primitive (.declare i32 true (.literal i32 1))) (.sequence sinkLoop (.primitive .skip)))
abbrev forStmtB1 (nv p b : Nat) (B : Command) : Command :=
  .scope (.sequence (.primitive (.declare i32 true (.literal i32 1))) (.sequence (forLoopB nv p b B) (.primitive .skip)))
abbrev mWrite : Command :=
  .sequence (.scope (.sequence (.primitive (.write (.local 2) s64 (idxV 5) (.variable s64 7)))
    (.sequence (.primitive (.write (.local 3) s64 (idxV 5) (.variable s64 8)))
      (.sequence (.primitive (.assign 5 i32 (.binary i32 .add (.variable i32 5) (.literal i32 1)))) (.primitive .skip)))))
    (.primitive .skip)
abbrev mExt : Command :=
  .sequence (.scope (.sequence (.branch (.binary bT .lt (.variable s64 9) (.variable s64 8))
    (.sequence (.scope (.sequence (.primitive (.write (.local 3) s64 (idxJ1 5) (.variable s64 8))) (.primitive .skip)))
      (.primitive .skip)) (.primitive .skip)) (.primitive .skip))) (.primitive .skip)
abbrev mElse : Command :=
  .sequence (.scope (.sequence (.primitive (.declare s64 true (.read s64 (.local 3) (idxJ1 5))))
    (.sequence (.branch (.binary bT .lt (.variable s64 9) (.variable s64 7)) mWrite mExt) (.primitive .skip))))
    (.primitive .skip)
abbrev mergeB : Command :=
  .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (idxV 6))))
    (.sequence (.primitive (.declare s64 true (.read s64 (.local 1) (idxV 6))))
      (.sequence (.branch (.binary bT .eq (.variable i32 5) (.literal i32 0)) mWrite mElse) (.primitive .skip)))
abbrev progIU (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.cast i32 (.size (.integer s64) (.local 0)))))
    (.sequence (forStmtB1 nv 1 0 sortB)
      (.sequence (.primitive (.declare i32 true (.literal i32 0)))
        (.sequence (forStmtB nv 2 0 mergeB) (.sequence (.primitive (.ret (.variable i32 5))) (.primitive .skip)))))

theorem body_eqIU : Proofs.IntervalUnionInstance.interval_union_inclusive_std_vector_long_long.body = progIU 4 := rfl

theorem bT_conv (c : Prop) [Decidable c] : bT.convert (if c then 1 else 0) = some (if c then 1 else 0) := by
  by_cases h : c <;> simp [h, bT, Ty.convert, Ty.valid]

theorem cmp_den (env : Nat → Ty → Option Int) (a b c d : Int) (h8 : env 8 s64 = some a) (h9 : env 9 s64 = some b)
    (h10 : env 10 s64 = some c) (h11 : env 11 s64 = some d) :
    cmpE.denote env = some (if b < a ∨ (a = b ∧ d < c) then 1 else 0) := by
  have lt1 : bT.convert (binaryValue .lt b a) = some (if b < a then 1 else 0) := by
    show bT.convert (if b < a then 1 else 0) = _
    by_cases h : b < a <;> simp [h, bT, Ty.convert, Ty.valid]
  have eq1 : bT.convert (binaryValue .eq a b) = some (if a = b then 1 else 0) := by
    show bT.convert (if a == b then 1 else 0) = _
    by_cases h : a = b <;> simp [h, bT, Ty.convert, Ty.valid]
  have lt2 : bT.convert (binaryValue .lt d c) = some (if d < c then 1 else 0) := by
    show bT.convert (if d < c then 1 else 0) = _
    by_cases h : d < c <;> simp [h, bT, Ty.convert, Ty.valid]
  simp only [cmpE, NExpr.denote, h8, h9, h10, h11, Option.bind_some, lt1, eq1, lt2]
  by_cases h1 : b < a
  · simp [h1]
  · by_cases h2 : a = b
    · by_cases h3 : d < c <;> simp [h1, h2, h3]
    · simp [h1, h2]

theorem idxJ1_den (env : Nat → Ty → Option Int) (slot j : Nat) (h : env slot i32 = some (j : Int)) (hj1 : 1 ≤ j)
    (hj : j < 2147483648) : (idxJ1 slot).denote env = some ((j - 1 : Nat) : Int) := by
  have hl : i32.valid 1 = true := by decide
  have hv : i32.valid ((j - 1 : Nat) : Int) = true := by
    simp only [i32, Ty.valid]; simp; omega
  have hsub : binaryValue .sub (j : Int) 1 = ((j - 1 : Nat) : Int) := by
    show (j : Int) - 1 = _
    omega
  rw [idxJ1, den_cast, den_binary, den_variable, h, den_literal, if_pos hl]
  show ((Option.bind (some (j : Int)) fun a => (some (1 : Int)).bind fun b => i32.convert (binaryValue .sub a b)).bind
    u64.convert) = _
  rw [Option.bind_some, Option.bind_some, hsub, Ty.convert_of_valid _ _ hv, Option.bind_some]
  have hlt : ((j - 1 : Nat) : Int) < 18446744073709551616 := by omega
  rw [convert_u64, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]

theorem map_get_y (f : Int × Int → Int) (U W : List (Int × Int)) (x y : Int × Int) :
    ((U ++ y :: x :: W).map f)[U.length]? = some (f y) := by
  simp [List.getElem?_append_right]

theorem map_get_x (f : Int × Int → Int) (U W : List (Int × Int)) (x y : Int × Int) :
    ((U ++ y :: x :: W).map f)[U.length + 1]? = some (f x) := by
  simp [List.getElem?_append_right]

theorem map_swap (f : Int × Int → Int) (U W : List (Int × Int)) (x y : Int × Int) :
    (((U ++ y :: x :: W).map f).set U.length (f x)).set (U.length + 1) (f y) = (U ++ x :: y :: W).map f := by
  induction U with
  | nil => simp
  | cons u U ih => simpa using ih

abbrev PV (S : List (Int × Int)) (RL RR : List Int) : Nat → List Int := V4 (S.map Prod.fst) (S.map Prod.snd) RL RR

abbrev C4 (n i j g : Nat) : List Cell := [ci n, ci i, ci j, ci g]

/-- The value of the flag `before` as computed by `cmpE`. -/
def bvOf (x y : Int × Int) : Int := if x.1 < y.1 ∨ (y.1 = x.1 ∧ x.2 < y.2) then 1 else 0

theorem PLt_iff (x y : Int × Int) : PLt x y ↔ (x.1 < y.1 ∨ (y.1 = x.1 ∧ x.2 < y.2)) := by
  unfold PLt; omega

/-- The five declarations of the body of the inner loop; `R` is the rest. -/
abbrev sinkChain (R : Command) : Command :=
  .sequence (.primitive (.declare s64 true (.read s64 (.local 0) (idxJ1 6))))
    (.sequence (.primitive (.declare s64 true (.read s64 (.local 0) (idxV 6))))
      (.sequence (.primitive (.declare s64 true (.read s64 (.local 1) (idxJ1 6))))
        (.sequence (.primitive (.declare s64 true (.read s64 (.local 1) (idxV 6))))
          (.sequence (.primitive (.declare bT true cmpE)) R))))

abbrev C9 (n i j g : Nat) (x y : Int × Int) : List Cell :=
  C4 n i j g ++ [cs64 y.1, cs64 x.1, cs64 y.2, cs64 x.2, ⟨bT, bvOf x y⟩]

theorem sink_chain (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (RL RR : List Int)
    (U W : List (Int × Int)) (x y : Int × Int) (P : List Cell) (n i j g : Nat) (hj : U.length + 1 = j)
    (hjb : j < 2147483648) (hn : n < 2147483648) (hi : i < 2147483648) (hg : g < 2147483648)
    (hxy : s64.valid x.1 = true ∧ s64.valid x.2 = true ∧ s64.valid y.1 = true ∧ s64.valid y.2 = true)
    (fu : Nat) (R : Command) (rr : PRM) (hR : pexecM mv fu R (gS P (C9 n i j g x y)) (PV (U ++ y :: x :: W) RL RR) = some rr)
    (hret : rr.ret = none) :
    ∃ (r : PRM), pexecM mv fu (sinkChain R) (gS P (C4 n i j g)) (PV (U ++ y :: x :: W) RL RR) = some r ∧
      r.ps = rr.ps ∧ r.vv = rr.vv ∧ r.ret = none ∧ r.cost ≤ rr.cost + 80 ∧ r.need ≤ max (P.length + 40) rr.need ∧
      r.wk = rr.wk := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hxy
  have hjv : j = U.length + 1 := hj.symm
  set vv := PV (U ++ y :: x :: W) RL RR with hvv
  have hv0 : vv 0 = (U ++ y :: x :: W).map Prod.fst := by simp [hvv, V4_get0]
  have hv1 : vv 1 = (U ++ y :: x :: W).map Prod.snd := by simp [hvv, V4_get1]
  have hj1 : 1 ≤ j := by omega
  -- the environment of the cells `n i j g`
  have ej := gSM_env mv.nv P (C4 n i j g) 2 (ci j) rfl (validN j hjb)
  rw [show mv.nv + 2 = 6 by omega] at ej
  -- a = l[j-1]
  have id1 := idxJ1_den (penvN mv.nv (gS P (C4 n i j g))) 6 j ej hj1 hjb
  have rd1 : vdenM mv vv (penvN mv.nv (gS P (C4 n i j g))) (.read s64 (.local 0) (idxJ1 6)) = some y.1 := by
    refine rdM_valI mv vv _ 0 (by omega) s64 hty0.symm _ rfl rfl (j - 1) id1 y.1 ?_ (by rw [hty0]; exact hy1)
    rw [hv0, show j - 1 = U.length by omega]; exact map_get_y Prod.fst U W x y
  have d1 := gSM_decl mv P (C4 n i j g) vv s64 (.read s64 (.local 0) (idxJ1 6)) y.1 y.1 rd1 (conv_signed s64 rfl rfl _ hy1)
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  -- b = l[j]
  have ej2 := gSM_env mv.nv P (C4 n i j g ++ [cs64 y.1]) 2 (ci j) rfl (validN j hjb)
  rw [show mv.nv + 2 = 6 by omega] at ej2
  have id2 := idxC_den (penvN mv.nv (gS P (C4 n i j g ++ [cs64 y.1]))) 6 j ej2 hjb
  have rd2 : vdenM mv vv (penvN mv.nv (gS P (C4 n i j g ++ [cs64 y.1]))) (.read s64 (.local 0) (idxV 6)) = some x.1 := by
    refine rdM_valI mv vv _ 0 (by omega) s64 hty0.symm _ rfl rfl j id2 x.1 ?_ (by rw [hty0]; exact hx1)
    rw [hv0, hjv]; exact map_get_x Prod.fst U W x y
  have d2 := gSM_decl mv P (C4 n i j g ++ [cs64 y.1]) vv s64 (.read s64 (.local 0) (idxV 6)) x.1 x.1 rd2
    (conv_signed s64 rfl rfl _ hx1)
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  -- c = r[j-1]
  have ej3 := gSM_env mv.nv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1]) 2 (ci j) rfl (validN j hjb)
  rw [show mv.nv + 2 = 6 by omega] at ej3
  have id3 := idxJ1_den (penvN mv.nv (gS P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1]))) 6 j ej3 hj1 hjb
  have rd3 : vdenM mv vv (penvN mv.nv (gS P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1]))) (.read s64 (.local 1) (idxJ1 6)) =
      some y.2 := by
    refine rdM_valI mv vv _ 1 (by omega) s64 hty1.symm _ rfl rfl (j - 1) id3 y.2 ?_ (by rw [hty1]; exact hy2)
    rw [hv1, show j - 1 = U.length by omega]; exact map_get_y Prod.snd U W x y
  have d3 := gSM_decl mv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1]) vv s64 (.read s64 (.local 1) (idxJ1 6)) y.2 y.2 rd3
    (conv_signed s64 rfl rfl _ hy2)
  have q3 := (pexecM_prim mv fu _ _ _).trans d3
  -- d = r[j]
  have ej4 := gSM_env mv.nv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2]) 2 (ci j) rfl
    (validN j hjb)
  rw [show mv.nv + 2 = 6 by omega] at ej4
  have id4 := idxC_den (penvN mv.nv (gS P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2]))) 6 j ej4 hjb
  have rd4 : vdenM mv vv (penvN mv.nv (gS P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2]))) (.read s64 (.local 1) (idxV 6)) =
      some x.2 := by
    refine rdM_valI mv vv _ 1 (by omega) s64 hty1.symm _ rfl rfl j id4 x.2 ?_ (by rw [hty1]; exact hx2)
    rw [hv1, hjv]; exact map_get_x Prod.snd U W x y
  have d4 := gSM_decl mv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2]) vv s64 (.read s64 (.local 1) (idxV 6)) x.2 x.2
    rd4 (conv_signed s64 rfl rfl _ hx2)
  have q4 := (pexecM_prim mv fu _ _ _).trans d4
  -- before = b < a || (a == b && d < c)
  have e8 := gSM_env mv.nv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2] ++ [cs64 x.2]) 4 (cs64 y.1) rfl hy1
  have e9 := gSM_env mv.nv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2] ++ [cs64 x.2]) 5 (cs64 x.1) rfl hx1
  have e10 := gSM_env mv.nv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2] ++ [cs64 x.2]) 6 (cs64 y.2) rfl hy2
  have e11 := gSM_env mv.nv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2] ++ [cs64 x.2]) 7 (cs64 x.2) rfl hx2
  rw [show mv.nv + 4 = 8 by omega] at e8
  rw [show mv.nv + 5 = 9 by omega] at e9
  rw [show mv.nv + 6 = 10 by omega] at e10
  rw [show mv.nv + 7 = 11 by omega] at e11
  have hcmp := cmp_den (penvN mv.nv (gS P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2] ++ [cs64 x.2]))) y.1 x.1 y.2 x.2
    e8 e9 e10 e11
  have hcmp' : vdenM mv vv (penvN mv.nv (gS P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2] ++ [cs64 x.2]))) cmpE =
      some (bvOf x y) := by
    rw [vdenM_scalar _ _ _ _ rfl, hcmp]; rfl
  have d5 := gSM_decl mv P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2] ++ [cs64 x.2]) vv bT cmpE (bvOf x y) (bvOf x y) hcmp'
    (by unfold bvOf; exact bT_conv _)
  have q5 := (pexecM_prim mv fu _ _ _).trans d5
  have hps9 : gS P (C4 n i j g ++ [cs64 y.1] ++ [cs64 x.1] ++ [cs64 y.2] ++ [cs64 x.2] ++ [⟨bT, bvOf x y⟩]) =
      gS P (C9 n i j g x y) := rfl
  rw [hps9] at q5
  have s5 := seqM_some q5 rfl hR
  have s4 := seqM_some q4 rfl s5
  have s3 := seqM_some q3 rfl s4
  have s2 := seqM_some q2 rfl s3
  have s1 := seqM_some q1 rfl s2
  refine ⟨_, s1, rfl, rfl, hret, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]
    omega
  · simp

theorem scope_wrap (mv : MV) (fu : Nat) (B : Command) (P C C' cs' : List Cell) (vv : Nat → List Int) (r : PRM)
    (hr : pexecM mv fu B (gS P C) vv = some r) (hps : r.ps = gS P (C' ++ cs')) (hl : C.length = C'.length) :
    pexecM mv fu (.scope B) (gS P C) vv = some ⟨gS P C', r.vv, r.ret, r.cost + 1, r.need, r.wk⟩ := by
  have := pexecM_scope mv fu B (gS P C) vv r hr
  rw [hps] at this
  simp only [gS_takeC P C C' cs' hl] at this
  exact this

theorem sub1_den (env : Nat → Ty → Option Int) (slot j : Nat) (h : env slot i32 = some (j : Int)) (hj1 : 1 ≤ j)
    (hj : j < 2147483648) :
    (NExpr.binary i32 .sub (.variable i32 slot) (.literal i32 1)).denote env = some ((j - 1 : Nat) : Int) := by
  have hl : i32.valid 1 = true := by decide
  have hv : i32.valid ((j - 1 : Nat) : Int) = true := by
    simp only [i32, Ty.valid]; simp; omega
  have hsub : binaryValue .sub (j : Int) 1 = ((j - 1 : Nat) : Int) := by
    show (j : Int) - 1 = _
    omega
  rw [den_binary, den_variable, h, den_literal, if_pos hl, Option.bind_some, Option.bind_some, hsub,
    Ty.convert_of_valid _ _ hv]

theorem eq0_den (env : Nat → Ty → Option Int) (slot t : Nat) (h : env slot i32 = some (t : Int)) :
    (NExpr.binary bT .eq (.variable i32 slot) (.literal i32 0)).denote env = some (if t = 0 then 1 else 0) := by
  have hl : i32.valid 0 = true := by decide
  rw [den_binary, den_variable, h, den_literal, if_pos hl, Option.bind_some, Option.bind_some]
  show bT.convert (if (t : Int) == 0 then 1 else 0) = _
  by_cases ht : t = 0
  · subst ht; simp [bT, Ty.convert, Ty.valid]
  · have : ¬ ((t : Int) = 0) := by omega
    simp [ht, this, bT, Ty.convert, Ty.valid]

theorem wr_step (mv : MV) (ps : PS) (vv : Nat → List Int) (k : Nat) (hk : k < mv.nv) (hty : mv.ty k = s64) (iE vE : NExpr)
    (x : Int) (p : Nat) (hx : vdenM mv vv (penvN mv.nv ps) vE = some x) (hp : vdenM mv vv (penvN mv.nv ps) iE = some (p : Int))
    (hlt : p < (vv k).length) (hv : s64.valid x = true) :
    pstmtM mv (.write (.local k) s64 iE vE) ps vv =
      some ⟨ps, upd vv k ((vv k).set p x), none, (vwp vE).1 + (vwp iE).1 + 3,
        ps.mem.length + ps.bs.length + iE.nodes + vE.nodes + (vwp vE).2 + (vwp iE).2 + 5, 1⟩ := by
  have := pstmtM_write_ok mv ps vv k hk iE vE x p hx hp hlt (by rw [hty]; exact hv)
  rw [hty] at this
  exact this

theorem swapW_chain (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (RL RR : List Int)
    (U W : List (Int × Int)) (x y : Int × Int) (P : List Cell) (n i j : Nat) (hj : U.length + 1 = j)
    (hjb : j < 2147483648) (hn : n < 2147483648) (hi : i < 2147483648)
    (hxy : s64.valid x.1 = true ∧ s64.valid x.2 = true ∧ s64.valid y.1 = true ∧ s64.valid y.2 = true)
    (fu : Nat) (R : Command) (rr : PRM)
    (hR : pexecM mv fu R (gS P (C9 n i j 1 x y)) (PV (U ++ x :: y :: W) RL RR) = some rr) (hret : rr.ret = none) :
    ∃ r : PRM, pexecM mv fu (.sequence (.primitive (.write (.local 0) s64 (idxJ1 6) (.variable s64 9)))
      (.sequence (.primitive (.write (.local 0) s64 (idxV 6) (.variable s64 8)))
      (.sequence (.primitive (.write (.local 1) s64 (idxJ1 6) (.variable s64 11)))
      (.sequence (.primitive (.write (.local 1) s64 (idxV 6) (.variable s64 10))) R))))
      (gS P (C9 n i j 1 x y)) (PV (U ++ y :: x :: W) RL RR) = some r ∧ r.ret = none ∧ r.ps = rr.ps ∧
      r.vv = rr.vv ∧ r.cost ≤ rr.cost + 120 ∧ r.need ≤ max (P.length + 60) rr.need ∧ r.wk ≤ rr.wk + 4 := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hxy
  have hjv : j = U.length + 1 := hj.symm
  have hj1 : 1 ≤ j := by omega
  set ps := gS P (C9 n i j 1 x y) with hps
  have ej := gSM_env mv.nv P (C9 n i j 1 x y) 2 (ci j) rfl (validN j hjb)
  rw [show mv.nv + 2 = 6 by omega] at ej
  have e8 := gSM_env mv.nv P (C9 n i j 1 x y) 4 (cs64 y.1) rfl hy1
  have e9 := gSM_env mv.nv P (C9 n i j 1 x y) 5 (cs64 x.1) rfl hx1
  have e10 := gSM_env mv.nv P (C9 n i j 1 x y) 6 (cs64 y.2) rfl hy2
  have e11 := gSM_env mv.nv P (C9 n i j 1 x y) 7 (cs64 x.2) rfl hx2
  rw [show mv.nv + 4 = 8 by omega] at e8
  rw [show mv.nv + 5 = 9 by omega] at e9
  rw [show mv.nv + 6 = 10 by omega] at e10
  rw [show mv.nv + 7 = 11 by omega] at e11
  have id1 := idxJ1_den (penvN mv.nv ps) 6 j ej hj1 hjb
  have id2 := idxC_den (penvN mv.nv ps) 6 j ej hjb
  have hlen : (U ++ y :: x :: W).length = U.length + 2 + W.length := by simp; omega
  have hlenL : ((U ++ y :: x :: W).map Prod.fst).length = U.length + 2 + W.length := by simpa using hlen
  have hlenR : ((U ++ y :: x :: W).map Prod.snd).length = U.length + 2 + W.length := by simpa using hlen
  -- w0: l[j-1] = b
  have w0 := wr_step mv ps (PV (U ++ y :: x :: W) RL RR) 0 (by omega) hty0 (idxJ1 6) (.variable s64 9) x.1 (j - 1)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e9)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact id1)
    (by simp [PV, V4_get0, hlen]; omega) hx1
  rw [PV, V4_get0, V4_upd0] at w0
  have q0 := (pexecM_prim mv fu _ _ _).trans w0
  -- w1: l[j] = a
  have w1 := wr_step mv ps (V4 (((U ++ y :: x :: W).map Prod.fst).set (j - 1) x.1) ((U ++ y :: x :: W).map Prod.snd) RL RR)
    0 (by omega) hty0 (idxV 6) (.variable s64 8) y.1 j
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e8)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact id2)
    (by simp [V4_get0, hlenL]; omega) hy1
  rw [V4_get0, V4_upd0] at w1
  have q1 := (pexecM_prim mv fu _ _ _).trans w1
  -- w2: r[j-1] = d
  have w2 := wr_step mv ps (V4 ((((U ++ y :: x :: W).map Prod.fst).set (j - 1) x.1).set j y.1)
    ((U ++ y :: x :: W).map Prod.snd) RL RR)
    1 (by omega) hty1 (idxJ1 6) (.variable s64 11) x.2 (j - 1)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e11)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact id1)
    (by simp [V4_get1, hlenR]; omega) hx2
  rw [V4_get1, V4_upd1] at w2
  have q2 := (pexecM_prim mv fu _ _ _).trans w2
  -- w3: r[j] = c
  have w3 := wr_step mv ps (V4 ((((U ++ y :: x :: W).map Prod.fst).set (j - 1) x.1).set j y.1)
    (((U ++ y :: x :: W).map Prod.snd).set (j - 1) x.2) RL RR)
    1 (by omega) hty1 (idxV 6) (.variable s64 10) y.2 j
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e10)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact id2)
    (by simp [V4_get1, hlenR]; omega) hy2
  rw [V4_get1, V4_upd1] at w3
  have q3 := (pexecM_prim mv fu _ _ _).trans w3
  have hfin : V4 ((((U ++ y :: x :: W).map Prod.fst).set (j - 1) x.1).set j y.1)
      ((((U ++ y :: x :: W).map Prod.snd).set (j - 1) x.2).set j y.2) RL RR = PV (U ++ x :: y :: W) RL RR := by
    have e1 : j - 1 = U.length := by omega
    rw [e1, hjv, PV]
    have m1 := map_swap Prod.fst U W x y
    have m2 := map_swap Prod.snd U W x y
    rw [m1, m2]
  rw [hfin] at q3
  have q4 := seqM_some q3 rfl hR
  have q5 := seqM_some q2 rfl q4
  have q6 := seqM_some q1 rfl q5
  have q7 := seqM_some q0 rfl q6
  refine ⟨_, q7, hret, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    omega
  · simp [hps, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, C9, C4]
    omega
  · simp
    omega

theorem assign_lit (mv : MV) (var slot : Nat) (hv : var = mv.nv + slot) (P cs : List Cell) (vv : Nat → List Int)
    (hslot : slot < cs.length) (ty : Ty) (e : NExpr) (v v' : Int) (hev : vdenM mv vv (penvN mv.nv (gS P cs)) e = some v)
    (c : Cell) (hc : cs[slot]? = some c) (hct : c.type = ty) (hcv : ty.valid c.value = true) (hconv : ty.convert v = some v') :
    pstmtM mv (.assign var ty e) (gS P cs) vv =
      some ⟨gS P (cs.set slot ⟨ty, v'⟩), vv, none, (vwp e).1 + 1, P.length + 2 * cs.length + (vwp e).2 + 2, 0⟩ := by
  subst hv
  exact gSM_assign mv P cs vv slot hslot ty e v v' hev c hc hct hcv hconv

/-- The tail of the swap branch: `j--; if (j == 0) go = 0;`. -/
abbrev swapTail : Command :=
  .sequence (.primitive (.assign 6 i32 (.binary i32 .sub (.variable i32 6) (.literal i32 1))))
    (.sequence (.branch (.binary bT .eq (.variable i32 6) (.literal i32 0)) stopGo (.primitive .skip)) (.primitive .skip))

theorem swapTail_exec (mv : MV) (hnv : mv.nv = 4) (x y : Int × Int) (P : List Cell) (n i j : Nat) (vv : Nat → List Int)
    (hj1 : 1 ≤ j) (hjb : j < 2147483648) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu swapTail (gS P (C9 n i j 1 x y)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C9 n i (j - 1) (if j - 1 = 0 then 0 else 1) x y) ∧ r.vv = vv ∧ r.cost ≤ 60 ∧
      r.need ≤ P.length + 60 ∧ r.wk = 0 := by
  have ej := gSM_env mv.nv P (C9 n i j 1 x y) 2 (ci j) rfl (validN j hjb)
  rw [show mv.nv + 2 = 6 by omega] at ej
  have hsub := sub1_den (penvN mv.nv (gS P (C9 n i j 1 x y))) 6 j ej hj1 hjb
  have a1 := assign_lit mv 6 2 (by omega) P (C9 n i j 1 x y) vv (by simp [C9, C4]) i32 (.binary i32 .sub (.variable i32 6) (.literal i32 1)) ((j - 1 : Nat) : Int)
    ((j - 1 : Nat) : Int) (by rw [vdenM_scalar _ _ _ _ rfl]; exact hsub) (ci j) rfl rfl (validN j hjb)
    (conv_signed i32 rfl rfl _ (validN (j - 1) (by omega)))
  have hset : (C9 n i j 1 x y).set 2 ⟨i32, ((j - 1 : Nat) : Int)⟩ = C9 n i (j - 1) 1 x y := rfl
  rw [hset] at a1
  have q1 := (pexecM_prim mv fu _ _ _).trans a1
  have ej' := gSM_env mv.nv P (C9 n i (j - 1) 1 x y) 2 (ci (j - 1)) rfl (validN (j - 1) (by omega))
  rw [show mv.nv + 2 = 6 by omega] at ej'
  have hc := eq0_den (penvN mv.nv (gS P (C9 n i (j - 1) 1 x y))) 6 (j - 1) ej'
  by_cases h0 : j - 1 = 0
  · rw [if_pos h0] at hc
    have hcond : vdenM mv vv (penvN mv.nv (gS P (C9 n i (j - 1) 1 x y)))
        (.binary bT .eq (.variable i32 6) (.literal i32 0)) = some 1 := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact hc
    have z := assign_lit mv 7 3 (by omega) P (C9 n i (j - 1) 1 x y) vv (by simp [C9, C4]) i32 (.literal i32 0) 0 0
      (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]) (ci 1) rfl rfl
      (validN 1 (by omega)) (conv_signed i32 rfl rfl _ (validN 0 (by omega)))
    have hset2 : (C9 n i (j - 1) 1 x y).set 3 ⟨i32, (0 : Int)⟩ = C9 n i (j - 1) 0 x y := rfl
    rw [hset2] at z
    have z1 := (pexecM_prim mv fu _ _ _).trans z
    have z2 := seqM_some z1 rfl (pexecM_skip mv fu _ _)
    have z3 := scope_wrap mv fu _ P (C9 n i (j - 1) 1 x y) (C9 n i (j - 1) 0 x y) [] vv _ z2 (by simp) (by simp [C9, C4])
    have z4 := seqM_some z3 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu _ stopGo (.primitive .skip) _ vv 1 hcond (by decide) _ z4
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q1 rfl b2
    refine ⟨_, b3, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · simp [h0]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, C9, C4]
    · simp
  · rw [if_neg h0] at hc
    have hcond : vdenM mv vv (penvN mv.nv (gS P (C9 n i (j - 1) 1 x y)))
        (.binary bT .eq (.variable i32 6) (.literal i32 0)) = some 0 := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact hc
    have b1 := pexecM_branch_false mv fu _ stopGo (.primitive .skip) _ vv hcond _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := seqM_some q1 rfl b2
    refine ⟨_, b3, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · simp [h0]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, C9, C4]
    · simp

theorem stopGo_exec (mv : MV) (hnv : mv.nv = 4) (P : List Cell) (n i j : Nat) (x y : Int × Int)
    (vv : Nat → List Int) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu stopGo (gS P (C9 n i j 1 x y)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C9 n i j 0 x y) ∧ r.vv = vv ∧ r.cost ≤ 20 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 := by
  have z := assign_lit mv 7 3 (by omega) P (C9 n i j 1 x y) vv (by simp [C9, C4]) i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]) (ci 1) rfl rfl
    (validN 1 (by omega)) (conv_signed i32 rfl rfl _ (validN 0 (by omega)))
  have hset2 : (C9 n i j 1 x y).set 3 ⟨i32, (0 : Int)⟩ = C9 n i j 0 x y := rfl
  rw [hset2] at z
  have z1 := (pexecM_prim mv fu _ _ _).trans z
  have z2 := seqM_some z1 rfl (pexecM_skip mv fu _ _)
  have z3 := scope_wrap mv fu _ P (C9 n i j 1 x y) (C9 n i j 0 x y) [] vv _ z2 (by simp) (by simp [C9, C4])
  have z4 := seqM_some z3 rfl (pexecM_skip mv fu _ _)
  refine ⟨_, z4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, C9, C4]
  · simp

/-- One iteration of the sinking loop when `x` is below `y`: swap, decrement `j`, stop at the front. -/
theorem sink_iter_swap (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (RL RR : List Int)
    (U W : List (Int × Int)) (x y : Int × Int) (P : List Cell) (n i j : Nat) (hj : U.length + 1 = j)
    (hjb : j < 2147483648) (hn : n < 2147483648) (hi : i < 2147483648)
    (hxy : s64.valid x.1 = true ∧ s64.valid x.2 = true ∧ s64.valid y.1 = true ∧ s64.valid y.2 = true)
    (hlt : PLt x y) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (.sequence (.scope sinkBody) (.primitive .skip)) (gS P (C4 n i j 1))
        (PV (U ++ y :: x :: W) RL RR) = some r ∧ r.ret = none ∧
      r.ps = gS P (C4 n i (j - 1) (if j - 1 = 0 then 0 else 1)) ∧ r.vv = PV (U ++ x :: y :: W) RL RR ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 := by
  have hj1 : 1 ≤ j := by omega
  have hbv : bvOf x y = 1 := by unfold bvOf; rw [if_pos ((PLt_iff x y).mp hlt)]
  -- the tail and the writes
  obtain ⟨rt, hrt, hrtret, hrtps, hrtvv, hrtc, hrtn, hrtw⟩ := swapTail_exec mv hnv x y P n i j (PV (U ++ x :: y :: W) RL RR)
    hj1 hjb fu
  obtain ⟨rw4, hrw4, hrw4ret, hrw4ps, hrw4vv, hrw4c, hrw4n, hrw4w⟩ := swapW_chain mv hnv hty0 hty1 RL RR U W x y P n i j hj hjb hn hi
    hxy fu swapTail rt hrt hrtret
  have sc := scope_wrap mv fu _ P (C9 n i j 1 x y) (C9 n i (j - 1) (if j - 1 = 0 then 0 else 1) x y) [] _ _ hrw4
    (by rw [hrw4ps, hrtps]; simp) (by simp [C9, C4])
  have sc2 := seqM_some sc hrw4ret (pexecM_skip mv fu _ _)
  -- the branch on the flag
  have e12 := gSM_env mv.nv P (C9 n i j 1 x y) 8 ⟨bT, bvOf x y⟩ rfl (by simp [hbv, bT, Ty.valid])
  rw [show mv.nv + 8 = 12 by omega] at e12
  have hcond : vdenM mv (PV (U ++ y :: x :: W) RL RR) (penvN mv.nv (gS P (C9 n i j 1 x y))) (.variable bT 12) = some 1 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; rw [← hbv]; exact e12
  have b1 := pexecM_branch_true mv fu (.variable bT 12) swapThen stopGo _ _ 1 hcond (by decide) _ sc2
  have b2 := seqM_some b1 (by simp [hrw4ret]) (pexecM_skip mv fu _ _)
  obtain ⟨rc, hrc, hrcret, hrcps, hrcvv, hrcc, hrcn, hrcw⟩ : ∃ rc : PRM, pexecM mv fu (.sequence (.branch (.variable bT 12) swapThen stopGo)
      (.primitive .skip)) (gS P (C9 n i j 1 x y)) (PV (U ++ y :: x :: W) RL RR) = some rc ∧ rc.ret = none ∧
      rc.ps = gS P (C9 n i (j - 1) (if j - 1 = 0 then 0 else 1) x y) ∧ rc.vv = PV (U ++ x :: y :: W) RL RR ∧
      rc.cost ≤ 250 ∧ rc.need ≤ P.length + 80 ∧ rc.wk ≤ 4 := by
    refine ⟨_, b2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hrw4ret
    · simp [hrw4ps, hrtps]
    · simp [hrw4vv, hrtvv]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at *; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, C9, C4] at *; omega
    · simp [hrw4w, hrtw] at *; omega
  obtain ⟨rs, hrs, hrsps, hrsvv, hrsret, hrsc, hrsn, hrsw⟩ := sink_chain mv hnv hty0 hty1 RL RR U W x y P n i j 1 hj hjb hn hi
    (by omega) hxy fu _ rc hrc hrcret
  have sc3 := scope_wrap mv fu sinkBody P (C4 n i j 1) (C4 n i (j - 1) (if j - 1 = 0 then 0 else 1))
    [cs64 y.1, cs64 x.1, cs64 y.2, cs64 x.2, ⟨bT, bvOf x y⟩] _ _ hrs (by rw [hrsps, hrcps]) (by simp [C4])
  have sc4 := seqM_some sc3 hrsret (pexecM_skip mv fu _ _)
  refine ⟨_, sc4, by simpa using hrsret, by simp, by simp [hrsvv, hrcvv], ?_, ?_, ?_⟩
  · simp at *; omega
  · simp [gS_size, C4] at *; omega
  · simp at *; omega

/-- One iteration of the sinking loop when `x` is not below `y`: the loop stops (`go = 0`). -/
theorem sink_iter_stop (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (RL RR : List Int)
    (U W : List (Int × Int)) (x y : Int × Int) (P : List Cell) (n i j : Nat) (hj : U.length + 1 = j)
    (hjb : j < 2147483648) (hn : n < 2147483648) (hi : i < 2147483648)
    (hxy : s64.valid x.1 = true ∧ s64.valid x.2 = true ∧ s64.valid y.1 = true ∧ s64.valid y.2 = true)
    (hnlt : ¬ PLt x y) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (.sequence (.scope sinkBody) (.primitive .skip)) (gS P (C4 n i j 1))
        (PV (U ++ y :: x :: W) RL RR) = some r ∧ r.ret = none ∧
      r.ps = gS P (C4 n i j 0) ∧ r.vv = PV (U ++ y :: x :: W) RL RR ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 := by
  have hbv : bvOf x y = 0 := by unfold bvOf; rw [if_neg (fun h => hnlt ((PLt_iff x y).mpr h))]
  obtain ⟨rt, hrt, hrtret, hrtps, hrtvv, hrtc, hrtn, hrtw⟩ := stopGo_exec mv hnv P n i j x y (PV (U ++ y :: x :: W) RL RR) fu
  have e12 := gSM_env mv.nv P (C9 n i j 1 x y) 8 ⟨bT, bvOf x y⟩ rfl (by simp [hbv, bT, Ty.valid])
  rw [show mv.nv + 8 = 12 by omega] at e12
  have hcond : vdenM mv (PV (U ++ y :: x :: W) RL RR) (penvN mv.nv (gS P (C9 n i j 1 x y))) (.variable bT 12) = some 0 := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; rw [← hbv]; exact e12
  have b1 := pexecM_branch_false mv fu (.variable bT 12) swapThen stopGo _ _ hcond _ hrt
  have b2 := seqM_some b1 hrtret (pexecM_skip mv fu _ _)
  obtain ⟨rs, hrs, hrsps, hrsvv, hrsret, hrsc, hrsn, hrsw⟩ := sink_chain mv hnv hty0 hty1 RL RR U W x y P n i j 1 hj hjb hn hi
    (by omega) hxy fu _ _ b2 (by simpa using hrtret)
  have sc3 := scope_wrap mv fu sinkBody P (C4 n i j 1) (C4 n i j 0)
    [cs64 y.1, cs64 x.1, cs64 y.2, cs64 x.2, ⟨bT, bvOf x y⟩] _ _ hrs (by rw [hrsps]; simp [hrtps]) (by simp [C4])
  have sc4 := seqM_some sc3 hrsret (pexecM_skip mv fu _ _)
  refine ⟨_, sc4, by simpa using hrsret, by simp, by simp [hrsvv, hrtvv], ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at *; omega
  · simp [hrtps, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, C4, C9] at *; omega
  · simp at *; omega

theorem sinkCond_den (env : Nat → Ty → Option Int) (t : Nat) (h : env 7 i32 = some (t : Int)) :
    sinkCond.denote env = some (if t = 0 then 0 else 1) := by
  have hl : i32.valid 0 = true := by decide
  rw [sinkCond, den_binary, den_variable, h, den_literal, if_pos hl, Option.bind_some, Option.bind_some]
  show bT.convert (if (t : Int) != 0 then 1 else 0) = _
  by_cases ht : t = 0
  · subst ht; simp [bT, Ty.convert, Ty.valid]
  · have : ¬ ((t : Int) = 0) := by omega
    simp [ht, this, bT, Ty.convert, Ty.valid]

theorem vwp_sinkCond : vwp sinkCond = (3, 3) := by simp [vwp, NExpr.nodes]

theorem while_exit (mv : MV) (fu : Nat) (c : NExpr) (b : Command) (ps : PS) (vv : Nat → List Int)
    (hc : vdenM mv vv (penvN mv.nv ps) c = some 0) :
    pexecM mv (fu + 1) (.whileLoop c b) ps vv =
      some ⟨ps, vv, none, (vwp c).1 + 1, ps.mem.length + ps.bs.length + (vwp c).2 + 2, 0⟩ := by
  rw [pexecM_while, hc]
  simp [Bind.bind, Option.bind]

theorem while_step (mv : MV) (fu : Nat) (c : NExpr) (b : Command) (ps : PS) (vv : Nat → List Int)
    (hc : vdenM mv vv (penvN mv.nv ps) c = some 1) (r1 r2 : PRM) (h1 : pexecM mv (fu + 1) b ps vv = some r1)
    (hret : r1.ret = none) (h2 : pexecM mv fu (.whileLoop c b) r1.ps r1.vv = some r2) :
    pexecM mv (fu + 1) (.whileLoop c b) ps vv =
      some ⟨r2.ps, r2.vv, r2.ret, (vwp c).1 + 1 + r1.cost + r2.cost,
        max (ps.mem.length + ps.bs.length + (vwp c).2 + 2) (max r1.need r2.need), r1.wk + r2.wk⟩ := by
  rw [pexecM_while, hc]
  simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, hret, h2]

theorem sinkCond_val (mv : MV) (hnv : mv.nv = 4) (P : List Cell) (n i j g : Nat) (hg : g < 2147483648) (vv : Nat → List Int) :
    vdenM mv vv (penvN mv.nv (gS P (C4 n i j g))) sinkCond = some (if g = 0 then 0 else 1) := by
  have e7 := gSM_env mv.nv P (C4 n i j g) 3 (ci g) rfl (validN g hg)
  rw [show mv.nv + 3 = 7 by omega] at e7
  rw [vdenM_scalar _ _ _ _ rfl]
  exact sinkCond_den _ g e7

theorem sink_loop (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (RL RR : List Int)
    (x : Int × Int) (P : List Cell) (n i : Nat) (hn : n < 2147483648) (hi : i < 2147483648)
    (hx : s64.valid x.1 = true ∧ s64.valid x.2 = true) :
    ∀ (k : Nat) (A B T : List (Int × Int)), A.length = k → 1 ≤ k → k < 2147483648 → Sorted (A ++ B) → Sorted (x :: B) →
      (∀ p ∈ A, s64.valid p.1 = true ∧ s64.valid p.2 = true) → ∀ fu, k + 1 ≤ fu →
      ∃ (r : PRM) (A' B' : List (Int × Int)),
        pexecM mv fu sinkLoop (gS P (C4 n i k 1)) (PV (A ++ x :: (B ++ T)) RL RR) = some r ∧
        r.ret = none ∧ r.ps = gS P (C4 n i A'.length 0) ∧ r.vv = PV (A' ++ x :: (B' ++ T)) RL RR ∧
        Sorted (A' ++ x :: B') ∧ (A' ++ B').Perm (A ++ B) ∧ r.cost ≤ 410 * k + 10 ∧ r.need ≤ P.length + 100 ∧
        r.wk ≤ 4 * k := by
  intro k
  induction k with
  | zero => intro A B T _ h1; omega
  | succ k ih =>
    intro A B T hA _ hk hsAB hxB hvalid fu hfu
    rcases List.eq_nil_or_concat A with h | ⟨U, y, h⟩
    · subst h; simp at hA
    rw [List.concat_eq_append] at h
    subst h
    have hU : U.length = k := by simp at hA; omega
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    obtain ⟨fu'', rfl⟩ : ∃ fu'', fu' = fu'' + 1 := ⟨fu' - 1, by omega⟩
    have hyv := hvalid y (by simp)
    have hxy : s64.valid x.1 = true ∧ s64.valid x.2 = true ∧ s64.valid y.1 = true ∧ s64.valid y.2 = true :=
      ⟨hx.1, hx.2, hyv.1, hyv.2⟩
    have hS : U ++ [y] ++ x :: (B ++ T) = U ++ y :: x :: (B ++ T) := by simp
    have hsAB' : Sorted (U ++ y :: B) := by simpa using hsAB
    have hcond := sinkCond_val mv hnv P n i (k + 1) 1 (by omega) (PV (U ++ [y] ++ x :: (B ++ T)) RL RR)
    simp only [if_neg (show ¬ (1 = 0) by omega)] at hcond
    by_cases hlt : PLt x y
    · obtain ⟨r1, hr1, hr1ret, hr1ps, hr1vv, hr1c, hr1n, hr1w⟩ := sink_iter_swap mv hnv hty0 hty1 RL RR U (B ++ T) x y P n i (k + 1)
        (by omega) (by omega) hn hi hxy hlt (fu'' + 1 + 1)
      rw [hS] at hcond ⊢
      by_cases hk0 : k = 0
      · subst hk0
        have hU0 : U = [] := List.eq_nil_of_length_eq_zero hU
        subst hU0
        have hg : (if 0 + 1 - 1 = 0 then 0 else 1) = 0 := by simp
        have hexit := while_exit mv fu'' sinkCond (.sequence (.scope sinkBody) (.primitive .skip)) r1.ps r1.vv (by
          rw [hr1ps, sinkCond_val mv hnv P n i (0 + 1 - 1) _ (by omega)]; simp)
        have hst := while_step mv (fu'' + 1) sinkCond (.sequence (.scope sinkBody) (.primitive .skip)) _ _ hcond r1 _ hr1 hr1ret hexit
        refine ⟨_, [], y :: B, hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp
        · simp [hexit, hr1ps]
        · simp [hr1vv]
        · simpa using sorted_cons_cons hlt hxB (sorted_tail_of_append hsAB')
        · simp
        · simp [vwp_sinkCond]; omega
        · simp [hr1ps, vwp_sinkCond, gS_size, C4]; omega
        · simp [hr1w]
      · obtain ⟨r2, A', B', hr2, hr2ret, hr2ps, hr2vv, hr2s, hr2p, hr2c, hr2n, hr2w⟩ := ih U (y :: B) T hU (by omega) (by omega)
          hsAB' (sorted_cons_cons hlt hxB (sorted_tail_of_append hsAB'))
          (fun p hp => hvalid p (by simp [hp])) (fu'' + 1) (by omega)
        have hg : (if k + 1 - 1 = 0 then 0 else 1) = 1 := by simp; omega
        have hr1ps' : r1.ps = gS P (C4 n i k 1) := by
          have hk1 : k + 1 - 1 = k := by omega
          rw [hr1ps, hk1, if_neg hk0]
        have hr1vv' : r1.vv = PV (U ++ x :: ((y :: B) ++ T)) RL RR := by rw [hr1vv]; simp
        have hr2' : pexecM mv (fu'' + 1) sinkLoop r1.ps r1.vv = some r2 := by rw [hr1ps', hr1vv']; exact hr2
        have hst := while_step mv (fu'' + 1) sinkCond (.sequence (.scope sinkBody) (.primitive .skip)) _ _ hcond r1 _ hr1 hr1ret hr2'
        refine ⟨_, A', B', hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using hr2ret
        · simpa using hr2ps
        · simpa using hr2vv
        · exact hr2s
        · simpa using hr2p
        · simp [vwp_sinkCond]; omega
        · simp [vwp_sinkCond, gS_size, C4]; omega
        · simp; omega
    · obtain ⟨r1, hr1, hr1ret, hr1ps, hr1vv, hr1c, hr1n, hr1w⟩ := sink_iter_stop mv hnv hty0 hty1 RL RR U (B ++ T) x y P n i (k + 1)
        (by omega) (by omega) hn hi hxy hlt (fu'' + 1 + 1)
      rw [hS] at hcond ⊢
      have hexit := while_exit mv fu'' sinkCond (.sequence (.scope sinkBody) (.primitive .skip)) r1.ps r1.vv (by
        rw [hr1ps, sinkCond_val mv hnv P n i (k + 1) 0 (by omega)]; simp)
      have hst := while_step mv (fu'' + 1) sinkCond (.sequence (.scope sinkBody) (.primitive .skip)) _ _ hcond r1 _ hr1 hr1ret hexit
      refine ⟨_, U ++ [y], B, hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp [hexit, hr1ps, hU]
      · simp [hr1vv]
      · simpa using sink_stop hsAB' hxB hlt
      · simp
      · simp [vwp_sinkCond]; omega
      · simp [hr1ps, vwp_sinkCond, gS_size, C4]; omega
      · simp; omega

theorem one_lit_val (mv : MV) (vv : Nat → List Int) (ps : PS) :
    vdenM mv vv (penvN mv.nv ps) (.literal i32 1) = some 1 := by
  rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)]

/-- Like `for_stmt_runB`, but the counter starts at 1: `for (int t = 1; t < n; t++) B` with `1 ≤ n`. -/
theorem for_stmt_runB1 (mv : MV) (P : List Cell) (p b n : Nat) (hb : b < p) (hn : n < 2147483647) (hn1 : 1 ≤ n) (B : Command)
    (Inv : Nat → (Nat → List Int) → List Cell → Prop) (cB nB wB fB : Nat) (hnB : 2 * p + 12 ≤ nB)
    (hbody : ∀ (t : Nat) (vv : Nat → List Int) (C : List Cell) (fu : Nat), t < n → C.length = p → C[b]? = some (ci n) →
      Inv t vv C → fB ≤ fu →
      ∃ (r : PRM) (cs' C' : List Cell), pexecM mv fu B (gS P (C ++ [ci t])) vv = some r ∧ r.ret = none ∧
        r.ps = gS P (C' ++ [ci t] ++ cs') ∧ C'.length = p ∧ C'[b]? = some (ci n) ∧ Inv (t + 1) r.vv C' ∧
        r.cost ≤ cB ∧ r.need ≤ P.length + nB ∧ r.wk ≤ wB)
    (vv : Nat → List Int) (C : List Cell) (hCp : C.length = p) (h0 : C[b]? = some (ci n)) (hI : Inv 1 vv C) (fu : Nat)
    (hfu : fB + n + 1 ≤ fu) :
    ∃ (res : PRM) (C2 : List Cell), pexecM mv fu (forStmtB1 mv.nv p b B) (gS P C) vv = some res ∧ res.ps = gS P C2 ∧
      C2.length = p ∧ Inv n res.vv C2 ∧ res.ret = none ∧ res.cost ≤ (cB + 20) * n + 30 ∧ res.need ≤ P.length + nB ∧
      res.wk ≤ wB * n := by
  have d := gSM_decl mv P C vv i32 _ 1 1 (one_lit_val mv vv _) (conv_signed i32 rfl rfl _ rfl)
  have q := (pexecM_prim mv fu (.declare i32 true (.literal i32 1)) _ _).trans d
  obtain ⟨r, C2, hr, hps, hC2, hIn, hret, hc, hnd, hw⟩ :=
    for_loop_runB mv P p b n hb hn B Inv cB nB wB fB hnB hbody (n - 1) 1 (by omega) hn1 vv C hCp h0 hI fu (by omega)
  have hps0 : gS P (C ++ [(⟨i32, 1⟩ : Cell)]) = gS P (C ++ [ci 1]) := rfl
  rw [hps0] at q
  have t1 := seqM_some hr hret (pexecM_skip mv fu _ _)
  have t0 := seqM_some q rfl (by simpa using t1)
  have sc := pexecM_scope mv fu _ _ vv _ t0
  rw [hps] at sc
  have tk := gS_takeC P C C2 [ci n] (by simp [hCp, hC2])
  simp only [tk] at sc
  refine ⟨_, C2, sc, rfl, hC2, ?_, ?_, ?_, ?_, ?_⟩
  · exact hIn
  · rfl
  · show (vwp (NExpr.literal i32 1)).1 + 1 + r.cost + 1 ≤ _
    simp [vwp, NExpr.nodes] at *
    have : (cB + 20) * (n - 1) ≤ (cB + 20) * n := Nat.mul_le_mul_left _ (by omega)
    omega
  · show max (P.length + 2 * C.length + (vwp (NExpr.literal i32 1)).2 + 4)
      (max r.need ((gS P (C2 ++ [ci n])).mem.length + (gS P (C2 ++ [ci n])).bs.length)) ≤ _
    simp [vwp, NExpr.nodes, gS_size, hCp, hC2] at *
    omega
  · show 0 + r.wk ≤ _
    have : wB * (n - 1) ≤ wB * n := Nat.mul_le_mul_left _ (by omega)
    omega

/-- The invariant of the sorting loop at counter `i`: the first `i` pairs are sorted, the rest is untouched. -/
def OInv (n : Nat) (P0 : List (Int × Int)) (RL RR : List Int) (i : Nat) (vv : Nat → List Int) (C : List Cell) : Prop :=
  ∃ S : List (Int × Int), S.length = n ∧ vv = PV S RL RR ∧ C = [ci n] ∧ Sorted (S.take i) ∧ S.Perm P0 ∧
    S.drop i = P0.drop i

theorem sorted_short (S : List (Int × Int)) (h : S.length ≤ 1) : Sorted S := by
  unfold Sorted
  match S, h with
  | [], _ => exact List.Pairwise.nil
  | [a], _ => exact List.pairwise_singleton _ _

theorem sortB_exec (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (RL RR : List Int)
    (P0 : List (Int × Int)) (hvalid : ∀ p ∈ P0, s64.valid p.1 = true ∧ s64.valid p.2 = true) (P : List Cell) (n : Nat)
    (hn : n < 2147483647) (i : Nat) (vv : Nat → List Int) (C : List Cell) (fu : Nat) (hi : i < n) (hi1 : 1 ≤ i)
    (hI : OInv n P0 RL RR i vv C) (hfu : n + 2 ≤ fu) :
    ∃ (r : PRM) (cs' C' : List Cell), pexecM mv fu sortB (gS P (C ++ [ci i])) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C' ++ [ci i] ++ cs') ∧ C'.length = 1 ∧ C'[0]? = some (ci n) ∧ OInv n P0 RL RR (i + 1) r.vv C' ∧
      r.cost ≤ 410 * n + 100 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 * n := by
  obtain ⟨S, hSl, rfl, rfl, hSs, hSp, hSd⟩ := hI
  have hn2 : n < 2147483648 := by omega
  have hiS : i < S.length := by omega
  obtain ⟨x, hx⟩ : ∃ x, S[i]? = some x := ⟨S[i], by simp [hiS]⟩
  have hSsplit : S = S.take i ++ x :: S.drop (i + 1) := by
    have h1 := List.take_append_drop i S
    have h2 : S.drop i = x :: S.drop (i + 1) := by
      have hxe : S[i] = x := by
        have := hx
        rw [List.getElem?_eq_getElem hiS] at this
        exact Option.some.inj this
      rw [List.drop_eq_getElem_cons hiS, hxe]
    rw [← h2]; exact h1.symm
  set A := S.take i with hA
  set T := S.drop (i + 1) with hT
  have hAl : A.length = i := by simp [hA]; omega
  have hmemS : ∀ p ∈ S, s64.valid p.1 = true ∧ s64.valid p.2 = true := fun p hp => hvalid p (hSp.subset hp)
  have hxv := hmemS x (by rw [hSsplit]; simp)
  have hAv : ∀ p ∈ A, s64.valid p.1 = true ∧ s64.valid p.2 = true := fun p hp => hmemS p (List.mem_of_mem_take hp)
  -- j = i
  have hn32 : n < 2147483648 := hn2
  have ei := gSM_env mv.nv P [ci n, ci i] 1 (ci i) rfl (validN i (by omega))
  rw [show mv.nv + 1 = 5 by omega] at ei
  have d1 := gSM_decl mv P ([ci n] ++ [ci i]) (PV S RL RR) i32 (.variable i32 5) (i : Int) (i : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact ei) (conv_signed i32 rfl rfl _ (validN i (by omega)))
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have d2 := gSM_decl mv P ([ci n] ++ [ci i] ++ [ci i]) (PV S RL RR) i32 (.literal i32 1) 1 1 (one_lit_val mv _ _)
    (conv_signed i32 rfl rfl _ rfl)
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  have hC4 : [ci n] ++ [ci i] ++ [ci i] ++ [(⟨i32, 1⟩ : Cell)] = C4 n i i 1 := rfl
  rw [hC4] at q2
  have hSeq : S = A ++ x :: ([] ++ T) := by simpa using hSsplit
  have hloop := sink_loop mv hnv hty0 hty1 RL RR x P n i hn32 (by omega) hxv i A [] T hAl hi1 (by omega)
    (by simpa using hSs) (sorted_short [x] (by simp)) hAv fu (by omega)
  rw [← hSeq] at hloop
  obtain ⟨rl, A', B', hrl, hrlret, hrlps, hrlvv, hrls, hrlp, hrlc, hrln, hrlw⟩ := hloop
  have s3 := seqM_some hrl hrlret (pexecM_skip mv fu _ _)
  have s2 := seqM_some q2 rfl s3
  have s1 := seqM_some q1 rfl (by simpa using s2)
  have hlen : A'.length + B'.length = i := by
    have := hrlp.length_eq
    simp at this
    omega
  have hS'l : (A' ++ x :: (B' ++ T)).length = n := by
    simp [hT]; omega
  have hS'eq : A' ++ x :: (B' ++ T) = (A' ++ x :: B') ++ T := by simp
  refine ⟨_, [ci A'.length, ci 0], [ci n], s1, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using hrlret
  · simp [hrlps]
  · refine ⟨A' ++ x :: (B' ++ T), hS'l, ?_, rfl, ?_, ?_, ?_⟩
    · simp [hrlvv]
    · rw [hS'eq, List.take_left' (by simp; omega)]
      exact hrls
    · have h1 : (A' ++ x :: (B' ++ T)).Perm (x :: (A' ++ B' ++ T)) := by
        rw [hS'eq]
        exact (List.perm_middle.append_right T).trans (by simp [List.Perm.refl])
      have h2 : S.Perm (x :: (A ++ T)) := by
        rw [hSsplit]
        exact List.perm_middle
      have h3 : (x :: (A' ++ B' ++ T)).Perm (x :: (A ++ T)) := by
        refine List.Perm.cons x ?_
        exact (hrlp.append_right T).trans (by simp [List.Perm.refl])
      exact h1.trans (h3.trans (h2.symm.trans hSp))
    · have hd : (A' ++ x :: (B' ++ T)).drop (i + 1) = T := by
        rw [hS'eq, List.drop_left' (by simp; omega)]
      rw [hd]
      have : S.drop (i + 1) = P0.drop (i + 1) := by
        rw [← List.drop_drop, hSd, List.drop_drop]
      exact this
  · simp [vwp, NExpr.nodes] at *; omega
  · simp [hrlps, vwp, NExpr.nodes, gS_size, C4] at *; omega
  · simp at *; omega

theorem sort_exec (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (RL RR : List Int)
    (P0 : List (Int × Int)) (hvalid : ∀ p ∈ P0, s64.valid p.1 = true ∧ s64.valid p.2 = true) (P : List Cell) (n : Nat)
    (hn : n < 2147483647) (hlen : P0.length = n) (fu : Nat) (hfu : 2 * n + 3 ≤ fu) :
    ∃ (r : PRM) (S' : List (Int × Int)), pexecM mv fu (forStmtB1 mv.nv 1 0 sortB) (gS P [ci n]) (PV P0 RL RR) = some r ∧
      r.ret = none ∧ r.ps = gS P [ci n] ∧ r.vv = PV S' RL RR ∧ Sorted S' ∧ S'.Perm P0 ∧
      r.cost ≤ (410 * n + 120) * n + 30 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 * n * n := by
  by_cases hn0 : n = 0
  · subst hn0
    have hP0 : P0 = [] := List.eq_nil_of_length_eq_zero hlen
    subst hP0
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have d := gSM_decl mv P [ci 0] (PV [] RL RR) i32 _ 1 1 (one_lit_val mv _ _) (conv_signed i32 rfl rfl _ rfl)
    have q := (pexecM_prim mv (fu' + 1) (.declare i32 true (.literal i32 1)) _ _).trans d
    have hps0 : gS P ([ci 0] ++ [(⟨i32, 1⟩ : Cell)]) = gS P ([ci 0] ++ [ci 1]) := rfl
    rw [hps0] at q
    have hc := forCondB_val mv (PV [] RL RR) P [ci 0] 1 0 0 1 rfl rfl (by omega) (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    have hx := while_exit mv fu' (forCondB mv.nv 1 0) (forBody mv.nv 1 sortB) _ _ hc
    have t1 := seqM_some hx rfl (pexecM_skip mv (fu' + 1) _ _)
    have t0 := seqM_some q rfl (by simpa using t1)
    have sc := pexecM_scope mv (fu' + 1) _ _ (PV [] RL RR) _ t0
    have tk := gS_takeC P [ci 0] [ci 0] [ci 1] rfl
    simp only [List.append_assoc, List.singleton_append] at sc tk ⊢
    refine ⟨_, [], sc, rfl, ?_, rfl, sorted_short [] (by simp), List.Perm.refl _, ?_, ?_, ?_⟩
    · simp [tk]
    · simp [vwp, NExpr.nodes, vwp_forCondB]
    · simp [vwp, NExpr.nodes, vwp_forCondB, gS_size]
    · simp
  · have hn1 : 1 ≤ n := by omega
    obtain ⟨res, C2, hr, hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB1 mv P 1 0 n (by omega) hn hn1 sortB
      (fun t vv C => 1 ≤ t ∧ OInv n P0 RL RR t vv C) (410 * n + 100) 100 (4 * n) (n + 2) (by omega)
      (by
        intro t vv C fu' ht hCl hC0 hI hfu'
        obtain ⟨ht1, hOI⟩ := hI
        obtain ⟨r, cs', C', hr, hret, hps, hC'l, hC'0, hOI', hc, hn', hw⟩ := sortB_exec mv hnv hty0 hty1 RL RR P0 hvalid P n hn t vv C fu'
          ht ht1 hOI (by omega)
        exact ⟨r, cs', C', hr, hret, hps, hC'l, hC'0, ⟨by omega, hOI'⟩, hc, hn', hw⟩)
      (PV P0 RL RR) [ci n] rfl rfl
      ⟨by omega, P0, hlen, rfl, rfl, sorted_short _ (by simp [List.length_take]), List.Perm.refl _, rfl⟩ fu (by omega)
    obtain ⟨_, hOI⟩ := hIn
    obtain ⟨S, hSl, hvv, hCe, hSs, hSp, hSd⟩ := hOI
    refine ⟨res, S, hr, hret, by rw [hps, hCe], hvv, ?_, hSp, ?_, ?_, ?_⟩
    · rw [List.take_of_length_le (by omega)] at hSs; exact hSs
    · omega
    · omega
    · omega

/-! ### The merge pass -/

/-- The four vectors during the merge pass: the sorted input, and the result `M` followed by the untouched tail. -/
def PW (S M : List (Int × Int)) (RL RR : List Int) : Nat → List Int :=
  V4 (S.map Prod.fst) (S.map Prod.snd) (M.map Prod.fst ++ RL.drop M.length) (M.map Prod.snd ++ RR.drop M.length)

theorem set_app (f : Int × Int → Int) (M : List (Int × Int)) (R : List Int) (p : Int × Int) (hlen : M.length < R.length) :
    (M.map f ++ R.drop M.length).set M.length (f p) = (M ++ [p]).map f ++ R.drop (M.length + 1) := by
  have h1 : R.drop M.length = R[M.length] :: R.drop (M.length + 1) := List.drop_eq_getElem_cons hlen
  simp [List.set_append, List.length_map]
  rw [h1]
  rfl

theorem add1_den (env : Nat → Ty → Option Int) (slot j : Nat) (h : env slot i32 = some (j : Int)) (hj : j + 1 < 2147483648) :
    (NExpr.binary i32 .add (.variable i32 slot) (.literal i32 1)).denote env = some ((j + 1 : Nat) : Int) := by
  have hl : i32.valid 1 = true := by decide
  have hv : i32.valid ((j + 1 : Nat) : Int) = true := by
    simp only [i32, Ty.valid]; simp; omega
  have hsum : binaryValue .add (j : Int) 1 = ((j + 1 : Nat) : Int) := by
    show (j : Int) + 1 = _
    omega
  rw [den_binary, den_variable, h, den_literal, if_pos hl, Option.bind_some, Option.bind_some, hsum,
    Ty.convert_of_valid _ _ hv]

/-- A cell list of the body of the merge loop: `n`, `m`, `i`, `a`, `b` and possibly more. -/
abbrev D5 (n m i : Nat) (p : Int × Int) : List Cell := [ci n, ci m, ci i, cs64 p.1, cs64 p.2]

theorem mWrite_exec (mv : MV) (hnv : mv.nv = 4) (hty2 : mv.ty 2 = s64) (hty3 : mv.ty 3 = s64) (S M : List (Int × Int))
    (RL RR : List Int) (p : Int × Int) (hp : s64.valid p.1 = true ∧ s64.valid p.2 = true) (P : List Cell) (n i : Nat)
    (hm : M.length < n) (hi : i < n) (hn : n < 2147483648) (hRL : n ≤ RL.length) (hRR : n ≤ RR.length)
    (E : List Cell) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu mWrite (gS P (D5 n M.length i p ++ E)) (PW S M RL RR) = some r ∧ r.ret = none ∧
      r.ps = gS P (D5 n (M.length + 1) i p ++ E) ∧ r.vv = PW S (M ++ [p]) RL RR ∧ r.cost ≤ 80 ∧
      r.need ≤ P.length + 2 * (5 + E.length) + 40 ∧ r.wk ≤ 2 := by
  obtain ⟨hp1, hp2⟩ := hp
  have hmn : M.length < 2147483648 := by omega
  set vv := PW S M RL RR with hvv
  have ps_eq : gS P (D5 n M.length i p ++ E) = gS P (D5 n M.length i p ++ E) := rfl
  have e1 := gSM_env mv.nv P (D5 n M.length i p ++ E) 1 (ci M.length) (by simp [D5]) (validN _ hmn)
  rw [show mv.nv + 1 = 5 by omega] at e1
  have e3 := gSM_env mv.nv P (D5 n M.length i p ++ E) 3 (cs64 p.1) (by simp [D5]) hp1
  have e4 := gSM_env mv.nv P (D5 n M.length i p ++ E) 4 (cs64 p.2) (by simp [D5]) hp2
  rw [show mv.nv + 3 = 7 by omega] at e3
  rw [show mv.nv + 4 = 8 by omega] at e4
  have idm := idxC_den (penvN mv.nv (gS P (D5 n M.length i p ++ E))) 5 M.length e1 hmn
  have hv2 : vv 2 = M.map Prod.fst ++ RL.drop M.length := by simp [hvv, PW, V4_get2]
  have hv3 : vv 3 = M.map Prod.snd ++ RR.drop M.length := by simp [hvv, PW, V4_get3]
  have hl2 : (M.map Prod.fst ++ RL.drop M.length).length = RL.length := by
    simp; omega
  have hl3 : (M.map Prod.snd ++ RR.drop M.length).length = RR.length := by
    simp; omega
  -- ret_l[m] = a
  have w2 := wr_step mv (gS P (D5 n M.length i p ++ E)) vv 2 (by omega) hty2 (idxV 5) (.variable s64 7) p.1 M.length
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e3)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact idm)
    (by rw [hv2, hl2]; omega) hp1
  rw [hvv, PW, V4_get2, V4_upd2] at w2
  have q2 := (pexecM_prim mv fu _ _ _).trans w2
  -- ret_r[m] = b
  have w3 := wr_step mv (gS P (D5 n M.length i p ++ E))
    (V4 (S.map Prod.fst) (S.map Prod.snd) ((M.map Prod.fst ++ RL.drop M.length).set M.length p.1) (M.map Prod.snd ++ RR.drop M.length))
    3 (by omega) hty3 (idxV 5) (.variable s64 8) p.2 M.length
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e4)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact idm)
    (by rw [V4_get3, hl3]; omega) hp2
  rw [V4_get3, V4_upd3] at w3
  have q3 := (pexecM_prim mv fu _ _ _).trans w3
  have hfin : V4 (S.map Prod.fst) (S.map Prod.snd) ((M.map Prod.fst ++ RL.drop M.length).set M.length p.1)
      ((M.map Prod.snd ++ RR.drop M.length).set M.length p.2) = PW S (M ++ [p]) RL RR := by
    have m1 := set_app Prod.fst M RL p (by omega)
    have m2 := set_app Prod.snd M RR p (by omega)
    rw [m1, m2]
    simp [PW]
  rw [hfin] at q3
  -- m++
  have hadd := add1_den (penvN mv.nv (gS P (D5 n M.length i p ++ E))) 5 M.length e1 (by omega)
  have a1 := assign_lit mv 5 1 (by omega) P (D5 n M.length i p ++ E) (PW S (M ++ [p]) RL RR) (by simp [D5]) i32
    (.binary i32 .add (.variable i32 5) (.literal i32 1)) ((M.length + 1 : Nat) : Int) ((M.length + 1 : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact hadd) (ci M.length) (by simp [D5]) rfl (validN _ hmn)
    (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have hset : (D5 n M.length i p ++ E).set 1 ⟨i32, ((M.length + 1 : Nat) : Int)⟩ = D5 n (M.length + 1) i p ++ E := rfl
  rw [hset] at a1
  have q4 := (pexecM_prim mv fu _ _ _).trans a1
  have q5 := seqM_some q4 rfl (pexecM_skip mv fu _ _)
  have q6 := seqM_some q3 rfl q5
  have q7 := seqM_some q2 rfl q6
  have sc := scope_wrap mv fu _ P (D5 n M.length i p ++ E) (D5 n (M.length + 1) i p ++ E) [] _ _ q7 (by simp) (by simp [D5])
  have q8 := seqM_some sc rfl (pexecM_skip mv fu _ _)
  refine ⟨_, q8, rfl, by simp, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, D5]
    omega
  · simp

theorem mstep_snoc (M0 : List (Int × Int)) (q p : Int × Int) :
    mstep (M0 ++ [q]) p = if q.2 < p.1 then M0 ++ [q] ++ [p] else if q.2 < p.2 then M0 ++ [(q.1, p.2)] else M0 ++ [q] := by
  unfold mstep
  rw [List.getLast?_concat, List.dropLast_concat]

theorem set_last (M0 : List (Int × Int)) (q : Int × Int) (R : List Int) (b : Int) :
    ((M0 ++ [q]).map Prod.snd ++ R).set M0.length b = (M0 ++ [(q.1, b)]).map Prod.snd ++ R := by
  simp [List.set_append]

theorem lt_den (env : Nat → Ty → Option Int) (x y : Nat) (u v : Int) (hx : env x s64 = some u) (hy : env y s64 = some v) :
    (NExpr.binary bT .lt (.variable s64 x) (.variable s64 y)).denote env = some (if u < v then 1 else 0) := by
  rw [den_binary, den_variable, den_variable, hx, hy, Option.bind_some, Option.bind_some]
  show bT.convert (if u < v then 1 else 0) = _
  exact bT_conv _

theorem mExt_exec (mv : MV) (hnv : mv.nv = 4) (hty3 : mv.ty 3 = s64) (S M0 : List (Int × Int)) (q : Int × Int)
    (RL RR : List Int) (p : Int × Int) (hp : s64.valid p.1 = true ∧ s64.valid p.2 = true)
    (hq : s64.valid q.2 = true) (P : List Cell) (n i : Nat) (hm : M0.length + 1 < n) (hi : i < n) (hn : n < 2147483648)
    (hRR : n ≤ RR.length) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu mExt (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2])) (PW S (M0 ++ [q]) RL RR) = some r ∧
      r.ret = none ∧ r.ps = gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) ∧
      r.vv = PW S (if q.2 < p.2 then M0 ++ [(q.1, p.2)] else M0 ++ [q]) RL RR ∧ r.cost ≤ 100 ∧
      r.need ≤ P.length + 60 ∧ r.wk ≤ 1 := by
  obtain ⟨hp1, hp2⟩ := hp
  have hmn : M0.length + 1 < 2147483648 := by omega
  have e1 := gSM_env mv.nv P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) 1 (ci (M0.length + 1)) (by simp [D5]) (validN _ hmn)
  rw [show mv.nv + 1 = 5 by omega] at e1
  have e4 := gSM_env mv.nv P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) 4 (cs64 p.2) (by simp [D5]) hp2
  have e5 := gSM_env mv.nv P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) 5 (cs64 q.2) (by simp [D5]) hq
  rw [show mv.nv + 4 = 8 by omega] at e4
  rw [show mv.nv + 5 = 9 by omega] at e5
  have hcond := lt_den (penvN mv.nv (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2]))) 9 8 q.2 p.2 e5 e4
  by_cases hlt : q.2 < p.2
  · rw [if_pos hlt] at hcond ⊢
    have hc : vdenM mv (PW S (M0 ++ [q]) RL RR) (penvN mv.nv (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2])))
        (.binary bT .lt (.variable s64 9) (.variable s64 8)) = some 1 := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact hcond
    have id1 := idxJ1_den (penvN mv.nv (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2]))) 5 (M0.length + 1) e1 (by omega) hmn
    have hlen3 : ((M0 ++ [q]).map Prod.snd ++ RR.drop (M0 ++ [q]).length).length = RR.length := by simp; omega
    have w := wr_step mv (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2])) (PW S (M0 ++ [q]) RL RR) 3 (by omega) hty3
      (idxJ1 5) (.variable s64 8) p.2 (M0.length + 1 - 1)
      (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e4)
      (by rw [vdenM_scalar _ _ _ _ rfl]; exact id1)
      (by rw [PW, V4_get3, hlen3]; simp; omega) hp2
    rw [PW, V4_get3, V4_upd3] at w
    have hfin : V4 (S.map Prod.fst) (S.map Prod.snd) ((M0 ++ [q]).map Prod.fst ++ RL.drop (M0 ++ [q]).length)
        (((M0 ++ [q]).map Prod.snd ++ RR.drop (M0 ++ [q]).length).set (M0.length + 1 - 1) p.2) =
        PW S (M0 ++ [(q.1, p.2)]) RL RR := by
      have := set_last M0 q (RR.drop (M0 ++ [q]).length) p.2
      have h0 : M0.length + 1 - 1 = M0.length := by omega
      rw [h0, this]
      simp [PW]
    rw [hfin] at w
    have q1 := (pexecM_prim mv fu _ _ _).trans w
    have q2 := seqM_some q1 rfl (pexecM_skip mv fu _ _)
    have q3 := scope_wrap mv fu _ P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) (D5 n (M0.length + 1) i p ++ [cs64 q.2]) [] _ _ q2
      (by simp) rfl
    have q4 := seqM_some q3 rfl (pexecM_skip mv fu _ _)
    have b1 := pexecM_branch_true mv fu _ _ (.primitive .skip) _ _ 1 hc (by decide) _ q4
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := scope_wrap mv fu _ P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) (D5 n (M0.length + 1) i p ++ [cs64 q.2]) [] _ _ b2
      (by simp) rfl
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b4, rfl, by simp, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, D5, Container.nodes]
    · simp
  · rw [if_neg hlt] at hcond ⊢
    have hc : vdenM mv (PW S (M0 ++ [q]) RL RR) (penvN mv.nv (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2])))
        (.binary bT .lt (.variable s64 9) (.variable s64 8)) = some 0 := by
      rw [vdenM_scalar _ _ _ _ rfl]; exact hcond
    have b1 := pexecM_branch_false mv fu _ (.sequence (.scope (.sequence (.primitive (.write (.local 3) s64 (idxJ1 5) (.variable s64 8))) (.primitive .skip))) (.primitive .skip)) (.primitive .skip) _ _ hc _ (pexecM_skip mv fu _ _)
    have b2 := seqM_some b1 rfl (pexecM_skip mv fu _ _)
    have b3 := scope_wrap mv fu _ P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) (D5 n (M0.length + 1) i p ++ [cs64 q.2]) [] _ _ b2
      (by simp) rfl
    have b4 := seqM_some b3 rfl (pexecM_skip mv fu _ _)
    refine ⟨_, b4, rfl, by simp, rfl, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, D5]
    · simp

theorem mElse_exec (mv : MV) (hnv : mv.nv = 4) (hty2 : mv.ty 2 = s64) (hty3 : mv.ty 3 = s64) (S M0 : List (Int × Int))
    (q : Int × Int) (RL RR : List Int) (p : Int × Int) (hp : s64.valid p.1 = true ∧ s64.valid p.2 = true)
    (hq : s64.valid q.2 = true) (P : List Cell) (n i : Nat) (hm : M0.length + 1 < n) (hi : i < n) (hn : n < 2147483648)
    (hRL : n ≤ RL.length) (hRR : n ≤ RR.length) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu mElse (gS P (D5 n (M0.length + 1) i p)) (PW S (M0 ++ [q]) RL RR) = some r ∧ r.ret = none ∧
      r.ps = gS P (D5 n (mstep (M0 ++ [q]) p).length i p) ∧ r.vv = PW S (mstep (M0 ++ [q]) p) RL RR ∧
      r.cost ≤ 300 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  obtain ⟨hp1, hp2⟩ := hp
  have hmn : M0.length + 1 < 2147483648 := by omega
  have e1 := gSM_env mv.nv P (D5 n (M0.length + 1) i p) 1 (ci (M0.length + 1)) (by simp [D5]) (validN _ hmn)
  rw [show mv.nv + 1 = 5 by omega] at e1
  have id1 := idxJ1_den (penvN mv.nv (gS P (D5 n (M0.length + 1) i p))) 5 (M0.length + 1) e1 (by omega) hmn
  have hget : (PW S (M0 ++ [q]) RL RR 3)[M0.length + 1 - 1]? = some q.2 := by
    rw [PW, V4_get3]
    simp [List.getElem?_append_left, List.getElem?_append_right]
  have rdq : vdenM mv (PW S (M0 ++ [q]) RL RR) (penvN mv.nv (gS P (D5 n (M0.length + 1) i p)))
      (.read s64 (.local 3) (idxJ1 5)) = some q.2 :=
    rdM_valI mv _ _ 3 (by omega) s64 hty3.symm _ rfl rfl (M0.length + 1 - 1) id1 q.2 hget (by rw [hty3]; exact hq)
  have d1 := gSM_decl mv P (D5 n (M0.length + 1) i p) (PW S (M0 ++ [q]) RL RR) s64 (.read s64 (.local 3) (idxJ1 5)) q.2 q.2
    rdq (conv_signed s64 rfl rfl _ hq)
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have hcells : D5 n (M0.length + 1) i p ++ [(⟨s64, q.2⟩ : Cell)] = D5 n (M0.length + 1) i p ++ [cs64 q.2] := rfl
  rw [hcells] at q1
  have e3 := gSM_env mv.nv P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) 3 (cs64 p.1) (by simp [D5]) hp1
  have e5 := gSM_env mv.nv P (D5 n (M0.length + 1) i p ++ [cs64 q.2]) 5 (cs64 q.2) (by simp [D5]) hq
  rw [show mv.nv + 3 = 7 by omega] at e3
  rw [show mv.nv + 5 = 9 by omega] at e5
  have hcond := lt_den (penvN mv.nv (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2]))) 9 7 q.2 p.1 e5 e3
  -- the inner branch
  obtain ⟨rb, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ : ∃ rb : PRM,
      pexecM mv fu (.sequence (.branch (.binary bT .lt (.variable s64 9) (.variable s64 7)) mWrite mExt) (.primitive .skip))
        (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2])) (PW S (M0 ++ [q]) RL RR) = some rb ∧ rb.ret = none ∧
      rb.ps = gS P (D5 n (mstep (M0 ++ [q]) p).length i p ++ [cs64 q.2]) ∧ rb.vv = PW S (mstep (M0 ++ [q]) p) RL RR ∧
      rb.cost ≤ 250 ∧ rb.need ≤ P.length + 80 ∧ rb.wk ≤ 2 := by
    by_cases hlt : q.2 < p.1
    · rw [if_pos hlt] at hcond
      have hc : vdenM mv (PW S (M0 ++ [q]) RL RR) (penvN mv.nv (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2])))
          (.binary bT .lt (.variable s64 9) (.variable s64 7)) = some 1 := by
        rw [vdenM_scalar _ _ _ _ rfl]; exact hcond
      obtain ⟨rw1, hrw1, hrw1ret, hrw1ps, hrw1vv, hrw1c, hrw1n, hrw1w⟩ := mWrite_exec mv hnv hty2 hty3 S (M0 ++ [q]) RL RR p
        ⟨hp1, hp2⟩ P n i (by simp; omega) hi hn hRL hRR [cs64 q.2] fu
      have hms := mstep_snoc M0 q p
      rw [if_pos hlt] at hms
      have hL : (M0 ++ [q]).length = M0.length + 1 := by simp
      rw [hL] at hrw1 hrw1ps
      have b1 := pexecM_branch_true mv fu _ mWrite mExt _ _ 1 hc (by decide) _ hrw1
      have b2 := seqM_some b1 (by simpa using hrw1ret) (pexecM_skip mv fu _ _)
      refine ⟨_, b2, by simpa using hrw1ret, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hrw1ps, hms]; simp
      · rw [hrw1vv, hms]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
      · simp [hrw1ps, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, D5] at *; omega
      · simp; omega
    · rw [if_neg hlt] at hcond
      have hc : vdenM mv (PW S (M0 ++ [q]) RL RR) (penvN mv.nv (gS P (D5 n (M0.length + 1) i p ++ [cs64 q.2])))
          (.binary bT .lt (.variable s64 9) (.variable s64 7)) = some 0 := by
        rw [vdenM_scalar _ _ _ _ rfl]; exact hcond
      obtain ⟨rx, hrx, hrxret, hrxps, hrxvv, hrxc, hrxn, hrxw⟩ := mExt_exec mv hnv hty3 S M0 q RL RR p ⟨hp1, hp2⟩ hq P n i hm hi hn hRR fu
      have hms := mstep_snoc M0 q p
      rw [if_neg hlt] at hms
      have b1 := pexecM_branch_false mv fu _ mWrite mExt _ _ hc _ hrx
      have b2 := seqM_some b1 (by simpa using hrxret) (pexecM_skip mv fu _ _)
      refine ⟨_, b2, by simpa using hrxret, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hrxps, hms]
        by_cases h2 : q.2 < p.2 <;> simp [h2]
      · rw [hrxvv, hms]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
      · simp [hrxps, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, D5] at *; omega
      · simp; omega
  have s2 := seqM_some q1 rfl hrb
  have sc := scope_wrap mv fu _ P (D5 n (M0.length + 1) i p) (D5 n (mstep (M0 ++ [q]) p).length i p) [cs64 q.2] _ _ s2
    (by rw [hrbps]) (by simp [D5])
  have s3 := seqM_some sc (by simpa using hrbret) (pexecM_skip mv fu _ _)
  refine ⟨_, s3, by simpa using hrbret, rfl, by simpa using hrbvv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at *; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size, D5] at *; omega
  · simp at *; omega

/-- The invariant of the merge loop at counter `i`. -/
def MI (n : Nat) (S : List (Int × Int)) (RL RR : List Int) (i : Nat) (vv : Nat → List Int) (C : List Cell) : Prop :=
  ∃ M : List (Int × Int), MInv M (S.take i) ∧ M.length ≤ i ∧ (∀ q ∈ M, s64.valid q.1 = true ∧ s64.valid q.2 = true) ∧
    vv = PW S M RL RR ∧ C = [ci n, ci M.length]

theorem take_succ_getElem (S : List (Int × Int)) (i : Nat) (p : Int × Int) (h : S[i]? = some p) :
    S.take (i + 1) = S.take i ++ [p] := by
  rw [List.take_succ, h]; rfl

theorem mstep_facts (M0 : List (Int × Int)) (q p : Int × Int) (i : Nat) (hMl : M0.length + 1 ≤ i)
    (hMv : ∀ r ∈ M0 ++ [q], s64.valid r.1 = true ∧ s64.valid r.2 = true)
    (hpv : s64.valid p.1 = true ∧ s64.valid p.2 = true) :
    (mstep (M0 ++ [q]) p).length ≤ i + 1 ∧ ∀ r ∈ mstep (M0 ++ [q]) p, s64.valid r.1 = true ∧ s64.valid r.2 = true := by
  rw [mstep_snoc]
  have hq := hMv q (by simp)
  by_cases h1 : q.2 < p.1
  · rw [if_pos h1]
    refine ⟨by simp; omega, ?_⟩
    intro r hr
    simp at hr
    rcases hr with hr | hr | hr
    · exact hMv r (by simp [hr])
    · exact hMv r (by simp [hr])
    · rw [hr]; exact hpv
  · rw [if_neg h1]
    by_cases h2 : q.2 < p.2
    · rw [if_pos h2]
      refine ⟨by simp; omega, ?_⟩
      intro r hr
      simp at hr
      rcases hr with hr | hr
      · exact hMv r (by simp [hr])
      · rw [hr]; exact ⟨hq.1, hpv.2⟩
    · rw [if_neg h2]
      exact ⟨by simp; omega, hMv⟩

theorem mergeB_exec (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (S : List (Int × Int)) (hSl : S.length = n) (hSs : Sorted S)
    (hvalid : ∀ p ∈ S, s64.valid p.1 = true ∧ s64.valid p.2 = true) (hle : ∀ p ∈ S, p.1 ≤ p.2) (RL RR : List Int)
    (hRL : n ≤ RL.length) (hRR : n ≤ RR.length) (P : List Cell) (hn : n < 2147483647) (i : Nat) (vv : Nat → List Int)
    (C : List Cell) (fu : Nat) (hi : i < n) (hI : MI n S RL RR i vv C) :
    ∃ (r : PRM) (cs' C' : List Cell), pexecM mv fu mergeB (gS P (C ++ [ci i])) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (C' ++ [ci i] ++ cs') ∧ C'.length = 2 ∧ C'[0]? = some (ci n) ∧ MI n S RL RR (i + 1) r.vv C' ∧
      r.cost ≤ 400 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 2 := by
  obtain ⟨M, hMI, hMl, hMv, rfl, rfl⟩ := hI
  have hn2 : n < 2147483648 := by omega
  obtain ⟨p, hp⟩ : ∃ p, S[i]? = some p := ⟨S[i]'(by omega), by simp [hSl, hi]⟩
  have hpm : p ∈ S := List.mem_of_getElem? hp
  have hpv := hvalid p hpm
  have hple := hle p hpm
  have hmax : ∀ r ∈ S.take i, r.1 ≤ p.1 := by
    intro r hr
    have hsplit : S = S.take i ++ S.drop i := (List.take_append_drop i S).symm
    have hpd : p ∈ S.drop i := by
      rw [List.drop_eq_getElem_cons (by omega)]
      have : S[i] = p := by
        have := hp; rw [List.getElem?_eq_getElem (by omega)] at this; exact Option.some.inj this
      simp [this]
    have hsorted := hSs
    rw [hsplit] at hsorted
    have := (List.pairwise_append.mp hsorted).2.2 r hr p hpd
    unfold PLe PLt at this
    omega
  have hMn : M.length < n := by omega
  set vv := PW S M RL RR with hvv
  have hv0 : vv 0 = S.map Prod.fst := by simp [hvv, PW, V4_get0]
  have hv1 : vv 1 = S.map Prod.snd := by simp [hvv, PW, V4_get1]
  have ei := gSM_env mv.nv P [ci n, ci M.length, ci i] 2 (ci i) rfl (validN i (by omega))
  rw [show mv.nv + 2 = 6 by omega] at ei
  have idi := idxC_den (penvN mv.nv (gS P [ci n, ci M.length, ci i])) 6 i ei (by omega)
  have rda : vdenM mv vv (penvN mv.nv (gS P [ci n, ci M.length, ci i])) (.read s64 (.local 0) (idxV 6)) = some p.1 := by
    refine rdM_valI mv vv _ 0 (by omega) s64 hty0.symm _ rfl rfl i idi p.1 ?_ (by rw [hty0]; exact hpv.1)
    rw [hv0]; simp [List.getElem?_map, hp]
  have d1 := gSM_decl mv P [ci n, ci M.length, ci i] vv s64 (.read s64 (.local 0) (idxV 6)) p.1 p.1 rda
    (conv_signed s64 rfl rfl _ hpv.1)
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have ei2 := gSM_env mv.nv P [ci n, ci M.length, ci i, cs64 p.1] 2 (ci i) rfl (validN i (by omega))
  rw [show mv.nv + 2 = 6 by omega] at ei2
  have idi2 := idxC_den (penvN mv.nv (gS P [ci n, ci M.length, ci i, cs64 p.1])) 6 i ei2 (by omega)
  have rdb : vdenM mv vv (penvN mv.nv (gS P [ci n, ci M.length, ci i, cs64 p.1])) (.read s64 (.local 1) (idxV 6)) = some p.2 := by
    refine rdM_valI mv vv _ 1 (by omega) s64 hty1.symm _ rfl rfl i idi2 p.2 ?_ (by rw [hty1]; exact hpv.2)
    rw [hv1]; simp [List.getElem?_map, hp]
  have d2 := gSM_decl mv P [ci n, ci M.length, ci i, cs64 p.1] vv s64 (.read s64 (.local 1) (idxV 6)) p.2 p.2 rdb
    (conv_signed s64 rfl rfl _ hpv.2)
  have q2 := (pexecM_prim mv fu _ _ _).trans d2
  have hD5 : [ci n, ci M.length, ci i, cs64 p.1] ++ [(⟨s64, p.2⟩ : Cell)] = D5 n M.length i p := rfl
  rw [hD5] at q2
  -- the branch on `m == 0`
  have em := gSM_env mv.nv P (D5 n M.length i p) 1 (ci M.length) rfl (validN _ (by omega))
  rw [show mv.nv + 1 = 5 by omega] at em
  have hc0 := eq0_den (penvN mv.nv (gS P (D5 n M.length i p))) 5 M.length em
  have hD' : S.take (i + 1) = S.take i ++ [p] := take_succ_getElem S i p hp
  obtain ⟨M', rb, hM'I, hM'l, hM'v, hrb, hrbret, hrbps, hrbvv, hrbc, hrbn, hrbw⟩ : ∃ (M' : List (Int × Int)) (rb : PRM),
      MInv M' (S.take (i + 1)) ∧ M'.length ≤ i + 1 ∧ (∀ q ∈ M', s64.valid q.1 = true ∧ s64.valid q.2 = true) ∧
      pexecM mv fu (.sequence (.branch (.binary bT .eq (.variable i32 5) (.literal i32 0)) mWrite mElse) (.primitive .skip))
        (gS P (D5 n M.length i p)) vv = some rb ∧ rb.ret = none ∧ rb.ps = gS P (D5 n M'.length i p) ∧
      rb.vv = PW S M' RL RR ∧ rb.cost ≤ 350 ∧ rb.need ≤ P.length + 100 ∧ rb.wk ≤ 2 := by
    rcases List.eq_nil_or_concat M with hM | ⟨M0, q, hM⟩
    · -- the first interval
      subst hM
      have hz : (S.take i) = [] := by
        by_contra hne
        obtain ⟨d, D', hd⟩ : ∃ d D', S.take i = d :: D' := by
          cases h : S.take i with
          | nil => exact absurd h hne
          | cons d D' => exact ⟨d, D', rfl⟩
        have hdv : d ∈ S.take i := by rw [hd]; simp
        have hdle : d.1 ≤ d.2 := hle d (List.mem_of_mem_take hdv)
        have := (hMI.cov d.1).mpr ⟨d, hdv, Int.le_refl _, hdle⟩
        exact Cov_nil _ this
      rw [if_pos (by simp)] at hc0
      have hc : vdenM mv vv (penvN mv.nv (gS P (D5 n ([] : List (Int × Int)).length i p)))
          (.binary bT .eq (.variable i32 5) (.literal i32 0)) = some 1 := by
        rw [vdenM_scalar _ _ _ _ rfl]; exact hc0
      obtain ⟨rw1, hrw1, hrw1ret, hrw1ps, hrw1vv, hrw1c, hrw1n, hrw1w⟩ := mWrite_exec mv hnv hty2 hty3 S [] RL RR p hpv P n i
        (by simp; omega) hi hn2 hRL hRR [] fu
      simp only [List.append_nil] at hrw1 hrw1ps
      have b1 := pexecM_branch_true mv fu _ mWrite mElse _ _ 1 hc (by decide) _ hrw1
      have b2 := seqM_some b1 (by simpa using hrw1ret) (pexecM_skip mv fu _ _)
      have hms : mstep [] p = [p] := by unfold mstep; simp
      have hinv : MInv [p] (S.take (i + 1)) := by
        rw [hD', hz]; simpa [hms] using mstep_nil p hple
      refine ⟨[p], _, hinv, by simp, ?_, b2, by simpa using hrw1ret, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr; simp at hr; rw [hr]; exact hpv
      · rw [hrw1ps]; simp
      · simpa using hrw1vv
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
      · simp [hrw1ps, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, D5] at *; omega
      · simp; omega
    · -- extend or append to the last interval
      rw [List.concat_eq_append] at hM
      subst hM
      have hL : (M0 ++ [q]).length = M0.length + 1 := by simp
      have hqv := (hMv q (by simp)).2
      rw [hL] at hc0
      rw [if_neg (by omega)] at hc0
      have hc : vdenM mv vv (penvN mv.nv (gS P (D5 n (M0 ++ [q]).length i p)))
          (.binary bT .eq (.variable i32 5) (.literal i32 0)) = some 0 := by
        rw [vdenM_scalar _ _ _ _ rfl]; rw [hL]; exact hc0
      obtain ⟨re, hre, hreret, hreps, hrevv, hrec, hren, hrew⟩ := mElse_exec mv hnv hty2 hty3 S M0 q RL RR p hpv hqv P n i
        (by omega) hi hn2 hRL hRR fu
      rw [← hL] at hre
      have b1 := pexecM_branch_false mv fu _ mWrite mElse _ _ hc _ hre
      have b2 := seqM_some b1 (by simpa using hreret) (pexecM_skip mv fu _ _)
      have hinv : MInv (mstep (M0 ++ [q]) p) (S.take (i + 1)) := by
        rw [hD']; exact mstep_inv M0 q (S.take i) p hMI hmax hple
      have hf := mstep_facts M0 q p i (by omega) hMv hpv
      refine ⟨mstep (M0 ++ [q]) p, _, hinv, hf.1, hf.2, b2, by simpa using hreret, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using hreps
      · simpa using hrevv
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly]; omega
      · simp [hreps, vwp, NExpr.nodes, NExpr.scalarOnly, gS_size, D5] at *; omega
      · simp; omega
  have s2 := seqM_some q2 rfl hrb
  have s1 := seqM_some q1 rfl s2
  refine ⟨_, [cs64 p.1, cs64 p.2], [ci n, ci M'.length], s1, by simpa using hrbret, ?_, rfl, rfl,
    ⟨M', hM'I, hM'l, hM'v, by simpa using hrbvv, rfl⟩, ?_, ?_, ?_⟩
  · simpa using hrbps
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at *; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *; omega
  · simp at *; omega

theorem merge_exec (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (S : List (Int × Int)) (n : Nat) (hSl : S.length = n) (hSs : Sorted S)
    (hvalid : ∀ p ∈ S, s64.valid p.1 = true ∧ s64.valid p.2 = true) (hle : ∀ p ∈ S, p.1 ≤ p.2) (RL RR : List Int)
    (hRL : n ≤ RL.length) (hRR : n ≤ RR.length) (P : List Cell) (hn : n < 2147483647) (fu : Nat) (hfu : n + 1 ≤ fu) :
    ∃ (r : PRM) (M : List (Int × Int)), pexecM mv fu (forStmtB mv.nv 2 0 mergeB) (gS P [ci n, ci 0]) (PW S [] RL RR) = some r ∧
      r.ret = none ∧ r.ps = gS P [ci n, ci M.length] ∧ r.vv = PW S M RL RR ∧ MInv M S ∧ M.length ≤ n ∧
      (∀ q ∈ M, s64.valid q.1 = true ∧ s64.valid q.2 = true) ∧ r.cost ≤ (400 + 20) * n + 30 ∧
      r.need ≤ P.length + 100 ∧ r.wk ≤ 2 * n := by
  obtain ⟨res, C2, hr, hps, hC2, hIn, hret, hc, hnd, hw⟩ := for_stmt_runB mv P 2 0 n (by omega) hn mergeB
    (MI n S RL RR) 400 100 2 0 (by omega)
    (by
      intro t vv C fu' ht hCl hC0 hI hfu'
      exact mergeB_exec mv hnv hty0 hty1 hty2 hty3 S hSl hSs hvalid hle RL RR hRL hRR P hn t vv C fu' ht hI)
    (PW S [] RL RR) [ci n, ci 0] rfl rfl ⟨[], by simpa using ⟨⟨by simp, by simp⟩, fun x => Iff.rfl, by simp⟩, by simp, by simp, rfl, rfl⟩ fu
    (by omega)
  obtain ⟨M, hMI, hMl, hMv, hvv, hCe⟩ := hIn
  rw [List.take_of_length_le (by omega)] at hMI
  refine ⟨res, M, hr, hret, by rw [hps, hCe], hvv, hMI, hMl, hMv, hc, hnd, hw⟩

theorem zip_vv (L R RL RR : List Int) (h : L.length = R.length) : V4 L R RL RR = PV (L.zip R) RL RR := by
  simp [PV, List.map_fst_zip, List.map_snd_zip, h]

theorem prog_exec (mv : MV) (hnv : mv.nv = 4) (hty0 : mv.ty 0 = s64) (hty1 : mv.ty 1 = s64) (hty2 : mv.ty 2 = s64)
    (hty3 : mv.ty 3 = s64) (L R RL RR : List Int) (n : Nat) (hLl : L.length = n) (hRl : R.length = n)
    (hvalid : ∀ p ∈ L.zip R, s64.valid p.1 = true ∧ s64.valid p.2 = true) (hle : ∀ p ∈ L.zip R, p.1 ≤ p.2)
    (hRL : n ≤ RL.length) (hRR : n ≤ RR.length) (P : List Cell) (hn : n < 2147483647) (fu : Nat) (hfu : 3 * n + 5 ≤ fu) :
    ∃ (r : PRM) (S' M : List (Int × Int)), pexecM mv fu (progIU mv.nv) (gS P []) (V4 L R RL RR) = some r ∧
      r.ret = some (M.length : Int) ∧ r.ps = gS P [ci n, ci M.length] ∧ r.vv = PW S' M RL RR ∧ Sorted S' ∧
      S'.Perm (L.zip R) ∧ MInv M S' ∧ M.length ≤ n ∧ (∀ q ∈ M, s64.valid q.1 = true ∧ s64.valid q.2 = true) ∧
      r.cost ≤ (410 * n + 120) * n + 420 * n + 120 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 * n * n + 2 * n := by
  have hn2 : n < 2147483648 := by omega
  have hLR : L.length = R.length := by omega
  have hzl : (L.zip R).length = n := by simp [hLl, hRl]
  rw [zip_vv L R RL RR hLR]
  -- declare n
  have d0 := gSM_decl mv P [] (PV (L.zip R) RL RR) i32 (.cast i32 (.size (.integer s64) (.local 0))) (n : Int) (n : Int)
    (by
      have := size_valMk mv 0 (by omega) hty0 (PV (L.zip R) RL RR) (penvN mv.nv (gS P [])) (by simp [PV, V4_get0]; omega)
      simpa [PV, V4_get0, hLl, hRl] using this)
    (conv_signed i32 rfl rfl _ (validN _ hn2))
  have q0 := (pexecM_prim mv fu _ _ _).trans d0
  have hq0 : ([] ++ [(⟨i32, (n : Int)⟩ : Cell)]) = [ci n] := rfl
  rw [hq0] at q0
  -- the sort
  obtain ⟨rs, S', hrs, hrsret, hrsps, hrsvv, hS's, hS'p, hrsc, hrsn, hrsw⟩ := sort_exec mv hnv hty0 hty1 RL RR (L.zip R) hvalid P n hn hzl
    fu (by omega)
  have hS'l : S'.length = n := by rw [hS'p.length_eq]; exact hzl
  have hvalid' : ∀ p ∈ S', s64.valid p.1 = true ∧ s64.valid p.2 = true := fun p hp => hvalid p (hS'p.subset hp)
  have hle' : ∀ p ∈ S', p.1 ≤ p.2 := fun p hp => hle p (hS'p.subset hp)
  -- declare m
  have d1 := gSM_decl mv P [ci n] (PW S' [] RL RR) i32 (.literal i32 0) 0 0 (zero_lit_val mv _ _) (conv_signed i32 rfl rfl _ rfl)
  have q1 := (pexecM_prim mv fu _ _ _).trans d1
  have hq1 : [ci n] ++ [(⟨i32, 0⟩ : Cell)] = [ci n, ci 0] := rfl
  rw [hq1] at q1
  obtain ⟨rm, M, hrm, hrmret, hrmps, hrmvv, hMI, hMl, hMv, hrmc, hrmn, hrmw⟩ := merge_exec mv hnv hty0 hty1 hty2 hty3 S' n hS'l hS's
    hvalid' hle' RL RR hRL hRR P hn fu (by omega)
  -- return m
  have em := gSM_env mv.nv P [ci n, ci M.length] 1 (ci M.length) rfl (validN _ (by omega))
  rw [show mv.nv + 1 = 5 by omega] at em
  have hret : vdenM mv (PW S' M RL RR) (penvN mv.nv (gS P [ci n, ci M.length])) (.variable i32 5) = some (M.length : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact em
  have r5 := pstmtM_ret_ok mv (gS P [ci n, ci M.length]) (PW S' M RL RR) _ _ hret
  have q5 := seqM_ret (mv := mv) (fu := fu) (b := Sk) (a := .primitive (.ret (.variable i32 5))) (by rw [pexecM_prim, r5]) rfl
  have t4 := seqM_some hrm hrmret (by rw [hrmps, hrmvv]; exact q5)
  have hsrs : (PV S' RL RR) = PW S' [] RL RR := by simp [PV, PW]
  have t3 := seqM_some q1 rfl t4
  have t2 := seqM_some hrs hrsret (by rw [hrsps, hrsvv, hsrs]; exact t3)
  have t1 := seqM_some q0 rfl t2
  refine ⟨_, S', M, t1, rfl, rfl, rfl, hS's, hS'p, hMI, hMl, hMv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at *
    have : (400 + 20) * n + 30 ≤ 420 * n + 30 := by omega
    omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size] at *
    omega
  · simp at *
    omega

end Proofs.IntervalUnionExec
