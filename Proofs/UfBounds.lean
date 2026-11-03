import Proofs.FenwickCall

namespace Proofs.UfBounds
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.DoublingNested Proofs.Mod61Body
open Proofs.VecExpr Proofs.VecStraight Proofs.VecWrite Proofs.VecKitW
open Proofs.PrefixSumsCall Proofs.VectorFillCall Proofs.QuotientSearch Proofs.IntSim
open Proofs.VectorSumCall (conv_signed i32_valid)

-- Split assertions preserve the original short-circuit domain without reading ps[a].
abbrev lower (j : Nat) : NExpr := .binary bT .le (.literal i32 0) (.variable i32 j)
abbrev limit : NExpr := .binary i32 .sub (.cast i32 (.size (.integer i32) (.local 0))) (.literal i32 1)
abbrev upper (j : Nat) : NExpr := .binary bT .lt (.variable i32 j) limit
abbrev checked (e : NExpr) (body : Command) : Command := .sequence (.primitive (.check e)) body
abbrev bounds (j : Nat) (body : Command) : Command := checked (lower j) (checked (upper j) body)

-- A successful check has no storage or scalar effects; charge its expression and check work.
def charged (ps : PS) (e : NExpr) (r : PRW) : PRW :=
  ⟨r.ps,r.vec,r.ret,(vwp e).1+1+r.cost,max (ps.mem.length+ps.bs.length+(vwp e).2+2) r.need,r.wk⟩

theorem prepend {ps : PS} {vec : List Int} {e : NExpr} {body : Command} {fu : Nat} {r : PRW}
    (value : vdenL i32 vec (penv1 ps) e = some 1)
    (run : pexecW i32 fu body ps vec = some r) :
    pexecW i32 fu (checked e body) ps vec = some (charged ps e r) := by
  have check : pexecW i32 fu (.primitive (.check e)) ps vec =
      some ⟨ps,vec,none,(vwp e).1+1,ps.mem.length+ps.bs.length+(vwp e).2+2,0⟩ := by
    rw [pexecW_prim]
    simp [pstmtW,value]
  simpa [charged] using seqW_some check rfl run

theorem lower_eval (ps : PS) (vec : List Int) (j : Nat) (a : Int)
    (value : penv1 ps j i32 = some a) :
    vdenL i32 vec (penv1 ps) (lower j) = some (if 0 ≤ a then 1 else 0) := by
  rw [vdenL_scalar _ _ _ _ rfl,den_binary,den_literal]
  simp only [show i32.valid 0 = true from rfl, ite_true,den_variable,value,Option.bind_some]
  by_cases nonneg : 0 ≤ a <;> simp [binaryValue,nonneg,Ty.convert]

theorem upper_eval (ps : PS) (vec : List Int) (j : Nat) (a : Int)
    (value : penv1 ps j i32 = some a) (length : vec.length < 2147483648)
    (nonempty : 0 < vec.length) :
    vdenL i32 vec (penv1 ps) (upper j) = some (if a < (vec.length : Int)-1 then 1 else 0) := by
  have size : vdenL i32 vec (penv1 ps) (.size (.integer i32) (.local 0)) = some (vec.length : Int) := by
    simp [vdenL,NExpr.scalarOnly]
  have cast : i32.convert (vec.length : Int) = some (vec.length : Int) :=
    conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))
  have sub : i32.convert ((vec.length : Int)-1) = some ((vec.length : Int)-1) :=
    conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))
  rw [vdenL_binary _ _ _ _ _ _ _ rfl,vdenL_scalar _ _ _ _ rfl,den_variable,value,Option.bind_some]
  rw [vdenL_binary _ _ _ _ _ _ _ rfl,vdenL_cast _ _ _ _ _ rfl,size,Option.bind_some,cast]
  rw [vdenL_scalar _ _ _ _ rfl,den_literal]
  simp only [show i32.valid 1 = true from rfl, ite_true,Option.bind_some]
  change ((i32.convert ((vec.length : Int)-1)).bind fun b => bT.convert (binaryValue .lt a b)) = some (if a < (vec.length : Int)-1 then 1 else 0)
  rw [sub,Option.bind_some]
  by_cases inside : a < (vec.length : Int)-1 <;> simp [binaryValue,inside,Ty.convert]

theorem lower_value (ps : PS) (vec : List Int) (j : Nat) (a : Int)
    (value : penv1 ps j i32 = some a) (nonneg : 0 ≤ a) :
    vdenL i32 vec (penv1 ps) (lower j) = some 1 := by
  simpa [nonneg] using lower_eval ps vec j a value

theorem upper_value (ps : PS) (vec : List Int) (j : Nat) (a : Int)
    (value : penv1 ps j i32 = some a) (length : vec.length < 2147483648)
    (nonempty : 0 < vec.length) (inside : a < (vec.length : Int)-1) :
    vdenL i32 vec (penv1 ps) (upper j) = some 1 := by
  simpa [inside] using upper_eval ps vec j a value length nonempty

-- Every invalid int index is rejected before the unchecked algorithm body executes.
theorem reject_bounds (ps : PS) (vec : List Int) (j : Nat) (a : Int) (body : Command) (fu : Nat)
    (value : penv1 ps j i32 = some a) (length : vec.length < 2147483648)
    (nonempty : 0 < vec.length) (invalid : a < 0 ∨ (vec.length : Int) ≤ a+1) :
    pexecW i32 fu (bounds j body) ps vec = none := by
  by_cases nonneg : 0 ≤ a
  · have low := lower_value ps vec j a value nonneg
    have outside : ¬ a < (vec.length : Int)-1 := by omega
    have high : vdenL i32 vec (penv1 ps) (upper j) = some 0 := by
      simpa [outside] using upper_eval ps vec j a value length nonempty
    simp [bounds,checked,pexecW,pstmtW,low,high]
  · have low : vdenL i32 vec (penv1 ps) (lower j) = some 0 := by
      simpa [nonneg] using lower_eval ps vec j a value
    simp [bounds,checked,pexecW,pstmtW,low]

def bounded (ps : PS) (r : PRW) : PRW :=
  ⟨r.ps,r.vec,r.ret,13+r.cost,max (ps.mem.length+ps.bs.length+10) r.need,r.wk⟩

theorem prepend_bounds {ps : PS} {vec : List Int} {j : Nat} {a : Int} {body : Command} {fu : Nat} {r : PRW}
    (value : penv1 ps j i32 = some a) (length : vec.length < 2147483648)
    (nonneg : 0 ≤ a) (inside : a+1 < (vec.length : Int))
    (run : pexecW i32 fu body ps vec = some r) :
    pexecW i32 fu (bounds j body) ps vec = some (bounded ps r) := by
  have h := prepend (lower_value ps vec j a value nonneg)
    (prepend (upper_value ps vec j a value length (by omega) (by omega)) run)
  simpa [bounds,charged,bounded,← Nat.add_assoc,vwp,NExpr.scalarOnly,NExpr.nodes,Container.nodes,Nat.max_assoc] using h

end Proofs.UfBounds
