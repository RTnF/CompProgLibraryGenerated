import Proofs.StraightLine
import Proofs.Mod61Body

namespace Proofs.IntSim
open Proofs.CppScalar Proofs.StraightLine Proofs.CppNestedProgram
open Proofs.DoublingNested

-- Conversion and validity for the standard unsigned widths, stated with literal moduli so that
-- simp never has to evaluate `2 ^ width` itself.
theorem p32 : (2 : Int) ^ 32 = 4294967296 := by decide
theorem p64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide

abbrev u32 : Ty := ⟨32,false,false⟩

@[simp] theorem convert_u32 (v : Int) : u32.convert v = some (v % 4294967296) := by
  unfold Ty.convert
  simp only [u32, p32]
  simp

@[simp] theorem convert_u64 (v : Int) : u64.convert v = some (v % 18446744073709551616) := by
  unfold Ty.convert
  simp only [u64, p64]
  simp

@[simp] theorem convert_bl (v : Int) : bl.convert v = some (if v == 0 then 0 else 1) := by
  unfold Ty.convert
  simp [bl]

theorem valid_u32 (v : Int) : u32.valid v = decide (0 ≤ v ∧ v < 4294967296) := by
  simp [Ty.valid, u32, p32]

theorem valid_u64 (v : Int) : u64.valid v = decide (0 ≤ v ∧ v < 18446744073709551616) := by
  simp [Ty.valid, u64, p64]

theorem p63 : (2 : Int) ^ 63 = 9223372036854775808 := by decide

abbrev s64 : Ty := ⟨64,true,false⟩

theorem valid_s64 (v : Int) : s64.valid v = decide (-9223372036854775808 ≤ v ∧ v < 9223372036854775808) := by
  simp [Ty.valid, s64, p63]

theorem convert_s64 (v : Int) (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) :
    s64.convert v = some v := by
  unfold Ty.convert
  simp only [s64]
  have hv : (⟨64,true,false⟩ : Ty).valid v = true := by
    simp only [Ty.valid]; simp [p63]; omega
  simp [hv]

theorem den_cast (env : Nat → Ty → Option Int) (ty : Ty) (e : NExpr) :
    (NExpr.cast ty e).denote env = (e.denote env).bind fun v => ty.convert v := by
  simp [NExpr.denote]

theorem den_literal (env : Nat → Ty → Option Int) (ty : Ty) (v : Int) :
    (NExpr.literal ty v).denote env = if ty.valid v = true then some v else none := by
  simp [NExpr.denote]

end Proofs.IntSim
