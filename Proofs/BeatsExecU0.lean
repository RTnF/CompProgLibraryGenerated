import Proofs.BeatsExecUM
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec

theorem gt_conv (x y : Int) : bT.convert (binaryValue .gt x y) = some (if x > y then 1 else 0) := by
  by_cases h : x > y
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]
  · simp [binaryValue, h, Ty.convert, bT, Ty.valid]

/-- A comparison of two scalar expressions, as a 0/1 value. -/
theorem den_cmpw (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (op : Binary) (l r : NExpr) (a b : Int)
    (p : Prop) [Decidable p] (hconv : bT.convert (binaryValue op a b) = some (if p then 1 else 0))
    (hl : vdenM mv vv env l = some a) (hr : vdenM mv vv env r = some b) (hls : l.scalarOnly = true) (hrs : r.scalarOnly = true) :
    vdenM mv vv env (.binary bT op l r) = some (if p then 1 else 0) := by
  rw [den_cmp mv vv env op l r a b hl hr hls hrs]; exact hconv

/-- A local cell variable of any type. -/
theorem den_cellvar_t (mv : MV) (P L : List Cell) (ty : Ty) (j c : Nat) (hc : c = mv.nv + j) (v : Int) (h : L[j]? = some ⟨ty, v⟩)
    (hv : ty.valid v = true) (vv : Nat → List Int) :
    vdenM mv vv (penvN mv.nv (gS P L)) (.variable ty c) = some v := by
  rw [vdenM_scalar _ _ _ _ rfl, den_variable, hc]
  exact envs mv P L j ⟨ty, v⟩ h hv

theorem den_lit32 (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (n : Int) (h : i32.valid n = true) :
    vdenM mv vv env (.literal i32 n) = some n := by
  rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos h]

theorem conv_i32 (v : Int) (h : i32.valid v = true) : i32.convert v = some v := conv_signed i32 rfl rfl _ h
theorem conv_s64 (v : Int) (h : s64.valid v = true) : s64.convert v = some v := conv_signed s64 rfl rfl _ h

theorem den_2kd (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (c : Nat) (k d : Nat)
    (hck : env c i32 = some (k : Int)) (hd : 2 * k + d < M31) (hd1 : 0 < d) :
    vdenM mv vv env (.binary i32 .add (.binary i32 .mul (.literal i32 2) (.variable i32 c)) (.literal i32 (d : Int))) =
      some (((2 * k + d : Nat)) : Int) := by
  have h31 : 2 * k + d < 2147483648 := hd
  have ld : i32.valid (d : Int) = true := by
    show Ty.valid ⟨32, true, false⟩ (d : Int) = true
    simp [Ty.valid]; omega
  have kv : i32.valid ((2 * k : Nat) : Int) = true := by
    show Ty.valid ⟨32, true, false⟩ ((2 * k : Nat) : Int) = true
    simp [Ty.valid]; omega
  have kd : i32.valid ((2 * k + d : Nat) : Int) = true := by
    show Ty.valid ⟨32, true, false⟩ ((2 * k + d : Nat) : Int) = true
    simp [Ty.valid]; omega
  have e1 : binaryValue .mul 2 (k : Int) = ((2 * k : Nat) : Int) := by simp [binaryValue]
  have e2 : binaryValue .add ((2 * k : Nat) : Int) (d : Int) = ((2 * k + d : Nat) : Int) := by simp [binaryValue]
  have l2 : i32.valid 2 = true := by decide
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_binary, den_literal, den_variable, hck, den_literal]
  rw [if_pos l2, if_pos ld, Option.bind_some, Option.bind_some]
  rw [e1, conv_i32 _ kv, Option.bind_some, Option.bind_some, e2, conv_i32 _ kd]

theorem base3_lookup (pre ext : List Cell) (inf : Int) (k n : Nat) :
    (pre ++ ([cs inf, ci n, ci k] : List Cell) ++ ext)[pre.length]? = some (cs inf) ∧
    (pre ++ ([cs inf, ci n, ci k] : List Cell) ++ ext)[pre.length + 2]? = some (ci k) := by
  refine ⟨?_, ?_⟩ <;>
  · rw [List.getElem?_append_left (by simp)]
    simp [List.getElem?_append_right]

theorem cell_at3 (pre ext : List Cell) (inf : Int) (j : Nat) (c : Cell) (h : ext[j]? = some c) (m n k : Nat)
    (hn : m = pre.length + 3 + j) :
    (pre ++ ([cs inf, ci n, ci k] : List Cell) ++ ext)[m]? = some c := by
  have := ext_lookup (pre ++ ([cs inf, ci n, ci k] : List Cell)) ext j c h
  rw [hn]; simpa [Nat.add_assoc] using this


/-- An `int` index cell `ci x` used through `(unsigned long long)`. -/
theorem den_idx (mv : MV) (P L : List Cell) (j c : Nat) (hc : c = mv.nv + j) (x : Nat) (h : L[j]? = some (ci x)) (hx : x < M31)
    (vv : Nat → List Int) :
    (NExpr.cast u64 (NExpr.variable i32 c)).denote (penvN mv.nv (gS P L)) = some (x : Int) := by
  have := envs mv P L j (ci x) h (Proofs.BellmanFordExec.i32_valid_nat x hx)
  rw [hc]
  exact cidx_den _ (mv.nv + j) x this hx


theorem set_ext3 (pre ext : List Cell) (inf : Int) (k n : Nat) (g j : Nat) (hg : g = j + 3) (c : Cell) (hj : j < ext.length) :
    ((pre ++ ([cs inf, ci n, ci k] : List Cell)) ++ ext).set (pre.length + g) c =
      (pre ++ ([cs inf, ci n, ci k] : List Cell)) ++ ext.set j c := by
  have : pre.length + g = (pre ++ ([cs inf, ci n, ci k] : List Cell)).length + j := by simp; omega
  rw [this]
  exact set_app_idx _ _ j c hj

/-- Like `seq_sbranch2`, with the old value of the cell given explicitly. -/
theorem seq_sbranch3 (mv : MV) (fu : Nat) (P cl : List Cell) (vv : Nat → List Int) (slot : Nat) (hslot : slot < cl.length)
    (ty : Ty) (cE eA : NExpr) (C : Prop) [Decidable C] (v v' x0 : Int) (c : Cell)
    (hc : vdenM mv vv (penvN mv.nv (gS P cl)) cE = some (if C then 1 else 0))
    (hv : C → vdenM mv vv (penvN mv.nv (gS P cl)) eA = some v) (hcc : cl[slot]? = some c) (hct : c.type = ty)
    (hcv : ty.valid c.value = true) (hx0 : c.value = x0) (hconv : C → ty.convert v = some v') (REST : Command) (r : PRM)
    (hrest : pexecM mv fu REST (gS P (cl.set slot ⟨ty, if C then v' else x0⟩)) vv = some r) (hret : r.ret = none)
    (c0 : Nat) (hc0 : (vwp eA).1 + (vwp cE).1 + 4 ≤ c0) (n0 : Nat)
    (hn0 : P.length + 2 * cl.length + (vwp eA).2 + (vwp cE).2 + 6 ≤ n0) :
    ∃ r2 : PRM, pexecM mv fu (.sequence (.branch cE (.sequence (.scope (.sequence (.primitive (.assign (mv.nv + slot) ty eA)) Sk)) Sk) Sk) REST)
        (gS P cl) vv = some r2 ∧ r2.ret = none ∧ r2.ps = r.ps ∧ r2.vv = r.vv ∧ r2.cost ≤ c0 + r.cost ∧
        r2.need ≤ max n0 r.need ∧ r2.wk ≤ r.wk := by
  subst hx0
  exact seq_sbranch2 mv fu P cl vv slot hslot ty cE eA C v v' c hc hv hcc hct hcv hconv REST r hrest hret c0 hc0 n0 hn0

end Proofs.BeatsExec
