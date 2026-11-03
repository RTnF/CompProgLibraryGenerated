import Proofs.BeatsExecP0
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.BellmanFordExec

/-- Cells of `pre ++ ext`. -/
theorem cell_at0 (pre ext : List Cell) (g : Nat) (c : Cell) (h : ext[g]? = some c) :
    (pre ++ ext)[pre.length + g]? = some c := by
  rw [List.getElem?_append_right (by omega)]
  simpa using h

theorem set_ext0 (pre ext : List Cell) (g : Nat) (c : Cell) :
    (pre ++ ext).set (pre.length + g) c = pre ++ ext.set g c := by
  rw [List.set_append_right _ _ (by omega)]
  simp

/-- `v[k]` as a value, for an `int` vector. -/
theorem den_rd32 (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (v : Nat) (hv : v < mv.nv)
    (hty : mv.ty v = i32) (a : Int) (iE : NExpr) (hiS : iE.scalarOnly = true) (k : Nat) (hk : k < (vv v).length)
    (hvk : (vv v).getD k 0 = a) (hvlist : ∀ w ∈ vv v, i32.valid w = true) (hd : iE.denote env = some (k : Int)) :
    vdenM mv vv env (.read i32 (.local v) iE) = some a := by
  apply rdM_val mv vv env v hv i32 hty.symm iE hiS (by simp [NExpr.scalarOnly]) k hd a
  · rw [← hvk]; exact vec_getI (vv v) k hk
  · rw [hty, ← hvk]
    exact hvlist _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _)

theorem getD_mem_valid32 (l : List Int) (k : Nat) (hk : k < l.length) (h : ∀ w ∈ l, i32.valid w = true) :
    i32.valid (l.getD k 0) = true :=
  h _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _)

/-- `T x = e;` for an existing cell, followed by the rest. -/
theorem seq_assign (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cl.length)
    (ty : Ty) (eA : NExpr) (v v' : Int) (c : Cell)
    (hv : vdenM mv vv (penvN mv.nv (gS P cl)) eA = some v) (hcc : cl[slot]? = some c) (hct : c.type = ty)
    (hcv : ty.valid c.value = true) (hconv : ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (cl.set slot ⟨ty, v'⟩)) vv = some r) (hret : r.ret = none) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) REST) (gS P cl) vv = some r2 ∧
      r2.ret = none ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ (vwp eA).1 + 1 + r.cost ∧
      r2.need ≤ max (P.length + 2 * cl.length + (vwp eA).2 + 4) r.need ∧ r2.wk ≤ r.wk := by
  have as1 := gSM_assign mv P cl vv slot hslot ty eA v v' hv c hcc hct hcv hconv
  have a1 := (pexecM_prim mv fu (.assign (mv.nv + slot) ty eA) (gS P cl) vv).trans as1
  have a2 := seqM_some a1 rfl hrest
  refine ⟨_, a2, hret, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp [gS_size]; omega
  · simp

/-- A binary operation with a representable result. -/
theorem den_binw (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (ty : Ty) (op : Binary) (l r : NExpr) (a b : Int)
    (hl : vdenM mv vv env l = some a) (hr : vdenM mv vv env r = some b) (hls : l.scalarOnly = true) (hrs : r.scalarOnly = true)
    (hc : ty.convert (binaryValue op a b) = some (binaryValue op a b)) :
    vdenM mv vv env (.binary ty op l r) = some (binaryValue op a b) := by
  have hs : (NExpr.binary ty op l r).scalarOnly = true := by simp [NExpr.scalarOnly, hls, hrs]
  rw [vdenM_scalar _ _ _ _ hs, den_binary, ← vdenM_scalar mv vv env l hls, ← vdenM_scalar mv vv env r hrs, hl, hr]
  simpa using hc

/-- `(x + y) / 2` is `int` division of a nonnegative value by 2. -/
theorem den_div2 (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (l : NExpr) (a : Int)
    (hl : vdenM mv vv env l = some a) (hls : l.scalarOnly = true) (ha : 0 ≤ a) (hv : i32.valid a = true) :
    vdenM mv vv env (.divrem i32 false l (.literal i32 2)) = some (a / 2) := by
  have hs : (NExpr.divrem i32 false l (.literal i32 2)).scalarOnly = true := by simp [NExpr.scalarOnly, hls]
  rw [vdenM_scalar _ _ _ _ hs, den_divrem, ← vdenM_scalar mv vv env l hls, hl]
  have h2 : (NExpr.literal i32 2).denote env = some 2 := by rw [den_literal, if_pos (by decide)]
  rw [Option.bind_some, h2, Option.bind_some]
  unfold checkedDivRem
  have : a.tdiv 2 = a / 2 := by rw [Int.tdiv_eq_ediv]; simp [ha]
  have hv2 : i32.valid (a / 2) = true := by
    simp only [Ty.valid, i32] at hv ⊢
    simp at hv ⊢
    omega
  simp [this, hv2]
  exact conv_i32 _ hv2

/-- `l || r` of two comparisons, as a 0/1 value. -/
theorem den_orw (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (l r : NExpr) (P Q : Prop) [Decidable P] [Decidable Q]
    (hl : vdenM mv vv env l = some (if P then 1 else 0)) (hr : vdenM mv vv env r = some (if Q then 1 else 0))
    (hls : l.scalarOnly = true) (hrs : r.scalarOnly = true) :
    vdenM mv vv env (.logical false l r) = some (if P ∨ Q then 1 else 0) := by
  have hs : (NExpr.logical false l r).scalarOnly = true := by simp [NExpr.scalarOnly, hls, hrs]
  rw [vdenM_scalar _ _ _ _ hs]
  rw [vdenM_scalar mv vv env l hls] at hl
  rw [vdenM_scalar mv vv env r hrs] at hr
  by_cases hp : P <;> by_cases hq : Q <;> simp [NExpr.denote, hp, hq, hl, hr]

/-- `x + d` as an index. -/
theorem den_idx_add (mv : MV) (P L : List Cell) (j c : Nat) (hc : c = mv.nv + j) (x d : Nat) (h : L[j]? = some (ci x))
    (hx : x + d < M31) (hd : i32.valid (d : Int) = true) :
    (NExpr.cast u64 (NExpr.binary i32 .add (NExpr.variable i32 c) (NExpr.literal i32 (d : Int)))).denote (penvN mv.nv (gS P L)) =
      some ((x + d : Nat) : Int) := by
  have e := envs mv P L j (ci x) h (Proofs.BellmanFordExec.i32_valid_nat x (by omega))
  rw [den_cast, den_binary, den_variable, hc, e, Option.bind_some, den_literal, if_pos hd, Option.bind_some]
  have hv : i32.valid ((x : Int) + d) = true := by
    have : x + d < 2147483648 := hx
    simp only [Ty.valid, i32]; simp; omega
  show (i32.convert (binaryValue .add (x : Int) d)).bind _ = _
  have h2 : i32.convert (binaryValue .add (x : Int) d) = some ((x : Int) + d) := conv_i32 _ hv
  rw [h2, Option.bind_some, convert_u64]
  have h31 : x + d < 2147483648 := hx
  have h3 : ((x : Int) + d) % 18446744073709551616 = ((x + d : Nat) : Int) := by
    push_cast
    exact Int.emod_eq_of_lt (by omega) (by omega)
  exact congrArg some h3


theorem le_conv (x y : Int) : bT.convert (binaryValue .le x y) = some (if x ≤ y then 1 else 0) := by
  by_cases h : x ≤ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem ge_conv (x y : Int) : bT.convert (binaryValue .ge x y) = some (if x ≥ y then 1 else 0) := by
  by_cases h : x ≥ y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

theorem sub_one_cast (N : Nat) (h : 0 < N) : ((N : Int) - 1) = ((N - 1 : Nat) : Int) := by omega

theorem i32_valid_div2 (a : Int) (h : i32.valid a = true) (h0 : 0 ≤ a) : i32.valid (a / 2) = true := by
  simp only [Ty.valid, i32] at h ⊢
  simp at h ⊢
  omega

theorem getD_set_same (l : List Int) (i : Nat) (a : Int) (h : i < l.length) : (l.set i a).getD i 0 = a := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_diff (l : List Int) (i j : Nat) (a : Int) (h : i ≠ j) : (l.set i a).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem valid_set (P : Int → Prop) (l : List Int) (i : Nat) (a : Int) (hl : ∀ w ∈ l, P w) (ha : P a) : ∀ w ∈ l.set i a, P w := by
  intro w hw
  rcases List.mem_or_eq_of_mem_set hw with h | h
  · exact hl w h
  · rw [h]; exact ha

theorem ne_id1 (w : Nat) : w ≠ 2 * w + 1 := by omega
theorem ne_id2 (w : Nat) : w ≠ 2 * w + 2 := by omega
theorem ne_12 (w : Nat) : 2 * w + 1 ≠ 2 * w + 2 := by omega
theorem ne_s (s : Nat) : s ≠ s + 1 := by omega

/-- A binary operation with a vector read as an operand. -/
theorem den_binr (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (ty : Ty) (op : Binary) (l r : NExpr) (a b : Int)
    (hl : vdenM mv vv env l = some a) (hr : vdenM mv vv env r = some b) (h : (NExpr.binary ty op l r).scalarOnly = false)
    (hc : ty.convert (binaryValue op a b) = some (binaryValue op a b)) :
    vdenM mv vv env (.binary ty op l r) = some (binaryValue op a b) := by
  rw [vdenM_binary _ _ _ _ _ _ _ h, hl, hr, Option.bind_some, Option.bind_some]
  exact hc

theorem set_getD_self (l : List Int) (i : Nat) (h : i < l.length) : l.set i (l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    by_cases hj : j = i
    · subst hj; simp [List.getD_eq_getElem?_getD, h]
    · rw [List.getElem_set_ne (Ne.symm hj)]

/-- Leaving a scope that declared the cells `loc` on top of `b1`. -/
theorem scope_take (P pre b0 b1 loc : List Cell) (h : b0.length = b1.length) :
    (⟨(gS P (pre ++ (b1 ++ loc))).mem.take (gS P (pre ++ b0)).mem.length,
      (gS P (pre ++ (b1 ++ loc))).bs.take (gS P (pre ++ b0)).bs.length⟩ : PS) = gS P (pre ++ b1) := by
  have e1 : (gS P (pre ++ b0)).mem.length = (gS P (pre ++ b1)).mem.length := by simp [gS_mem_len, h]
  have e2 : (gS P (pre ++ b0)).bs.length = (gS P (pre ++ b1)).bs.length := by simp [gS_bs_len, h]
  rw [e1, e2, ← List.append_assoc]
  exact gS_take P (pre ++ b1) loc

end Proofs.BeatsExec
