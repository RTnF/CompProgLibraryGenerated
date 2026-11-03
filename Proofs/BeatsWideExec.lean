import Proofs.BeatsExecL0

namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.MultiVec Proofs.CppState
open Proofs.IntSim Proofs.DoublingNested Proofs.ForLoop
open Proofs.BellmanFordExec Proofs.ForLoopM Proofs.GenState
open Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt Proofs.VecWrite Proofs.VecKitW
open Proofs.MultiKit Proofs.ForLoopC Proofs.ForLoopB
open Proofs.QuotientSearch

theorem conv_u64 (v : Int) (h : u64.valid v = true) :
    u64.convert v = some v := Ty.convert_of_valid u64 v h

theorem u64_valid_nat (n : Nat) (h : n < 18446744073709551616) :
    u64.valid (n : Int) = true := by
  simp only [Ty.valid]
  simp
  omega

theorem den_lit64u (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (v : Int) (h : u64.valid v = true) :
    vdenM mv vv env (.literal u64 v) = some v := by
  rw [vdenM_scalar _ _ _ _ rfl, den_literal, ite_eq_left h]

theorem den_cast64u (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (e : NExpr) (v : Int) (he : vdenM mv vv env e = some v)
    (hs : e.scalarOnly = true) (hv : u64.valid v = true) :
    vdenM mv vv env (.cast u64 e) = some v := by
  have scalar : (NExpr.cast u64 e).scalarOnly = true := by simp [NExpr.scalarOnly, hs]
  rw [vdenM_scalar _ _ _ _ scalar, den_cast, ← vdenM_scalar mv vv env e hs, he]
  exact conv_u64 v hv

/-- The wide constructor's child expression. The cast precedes multiplication. -/
abbrev wideChild (slot d : Nat) : NExpr :=
  .binary u64 .add
    (.binary u64 .mul (.literal u64 2) (.cast u64 (.variable i32 slot)))
    (.literal u64 (d : Int))

theorem den_wide_child (env : Nat → Ty → Option Int) (slot k d : Nat)
    (hk : env slot i32 = some (k : Int)) (range : k < M31) (hd : d ≤ 2) :
    (wideChild slot d).denote env = some ((2*k+d : Nat) : Int) := by
  have km : k < 2147483648 := range
  have vd := u64_valid_nat d (by omega)
  have vm := u64_valid_nat (2*k) (by omega)
  have va := u64_valid_nat (2*k+d) (by omega)
  have cast := cidx_den env slot k hk range
  unfold wideChild
  rw [den_binary, den_binary, den_literal, ite_eq_left (by decide : u64.valid 2 = true),
    cast, Option.bind_some, Option.bind_some]
  have mul : binaryValue .mul 2 (k : Int) = ((2*k : Nat) : Int) := by simp [binaryValue]
  rw [mul, conv_u64 _ vm, Option.bind_some, den_literal, ite_eq_left vd, Option.bind_some]
  have add : binaryValue .add ((2*k : Nat) : Int) (d : Int) = ((2*k+d : Nat) : Int) := by
    simp [binaryValue]
  rw [add, conv_u64 _ va]

theorem vden_wide_child (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (slot k d : Nat) (hk : env slot i32 = some (k : Int)) (range : k < M31) (hd : d ≤ 2) :
    vdenM mv vv env (wideChild slot d) = some ((2*k+d : Nat) : Int) := by
  rw [vdenM_scalar _ _ _ _ rfl]
  exact den_wide_child env slot k d hk range hd

theorem den_wide_child_original_range (env : Nat → Ty → Option Int) (slot n k d : Nat)
    (hk : env slot i32 = some (k : Int)) (range : 4*n < M31)
    (scanned : k < 4*n) (hd : d ≤ 2) :
    (wideChild slot d).denote env = some ((2*k+d : Nat) : Int) ∧
    2*k+d < 8*n+8 := by
  exact ⟨den_wide_child env slot k d hk (by omega) hd, by omega⟩

/-- Reading a wide child local requires no signed-int bound on its value. -/
theorem den_idx64u (mv : MV) (P L : List Cell) (j c x : Nat)
    (hc : c = mv.nv+j) (h : L[j]? = some ⟨u64,(x : Int)⟩)
    (hx : x < 18446744073709551616) :
    (NExpr.variable u64 c).denote (penvN mv.nv (gS P L)) = some (x : Int) := by
  rw [den_variable, hc]
  exact envs mv P L j ⟨u64,(x : Int)⟩ h (u64_valid_nat x hx)

theorem den_idx64u_cast (mv : MV) (P L : List Cell) (j c x : Nat)
    (hc : c = mv.nv+j) (h : L[j]? = some ⟨u64,(x : Int)⟩)
    (hx : x < 18446744073709551616) :
    (NExpr.cast u64 (.variable u64 c)).denote (penvN mv.nv (gS P L)) = some (x : Int) := by
  rw [den_cast, den_idx64u mv P L j c x hc h hx, Option.bind_some]
  exact conv_u64 _ (u64_valid_nat x hx)

/-- The count expression emitted for each of the twelve node arrays. -/
abbrev wideCount (slot : Nat) : NExpr :=
  .cast u64 (.binary u64 .add
    (.binary u64 .mul (.literal u64 8) (.cast u64 (.size (.integer s64) (.local slot))))
    (.literal u64 8))

theorem vden_wide_count (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int)
    (slot : Nat) (hslot : slot < mv.nv) (hty : mv.ty slot = s64)
    (range : 4*(vv slot).length < M31) :
    vdenM mv vv env (wideCount slot) = some ((8*(vv slot).length+8 : Nat) : Int) := by
  let n := (vv slot).length
  have small : n < 2147483648 := by have : 4*n < 2147483648 := range; omega
  have vn := u64_valid_nat n (by omega)
  have vm := u64_valid_nat (8*n) (by omega)
  have va := u64_valid_nat (8*n+8) (by omega)
  have size : vdenM mv vv env (.size (.integer s64) (.local slot)) = some (n : Int) := by
    simp [vdenM, NExpr.scalarOnly, hslot, hty, n]
  have cast : vdenM mv vv env (.cast u64 (.size (.integer s64) (.local slot))) = some (n : Int) := by
    change (vdenM mv vv env (.size (.integer s64) (.local slot))).bind u64.convert = _
    rw [size]
    exact conv_u64 _ vn
  have literal := den_lit64u mv vv env 8 (by decide)
  have mul := den_binr mv vv env u64 .mul _ _ 8 (n : Int) literal cast rfl (conv_u64 _ vm)
  have add := den_binr mv vv env u64 .add _ _ (binaryValue .mul 8 (n : Int)) 8
    mul literal rfl (conv_u64 _ va)
  change (vdenM mv vv env (.binary u64 .add
    (.binary u64 .mul (.literal u64 8) (.cast u64 (.size (.integer s64) (.local slot))))
    (.literal u64 8))).bind u64.convert = _
  rw [add]
  exact conv_u64 _ va

end Proofs.BeatsExec
