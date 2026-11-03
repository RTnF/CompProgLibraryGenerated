import Proofs.VecKitW

namespace Proofs.GenState
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW
open Proofs.CppState (Cell)

/-- A scalar state whose local cells are `cs` (any types), each bound by one writable binding, after the cells `P`. -/
def gS (P cs : List Cell) : PS :=
  ⟨P ++ cs, (List.range cs.length).map fun j => ⟨P.length + j, true⟩⟩

theorem gS_mem (P cs : List Cell) : (gS P cs).mem = P ++ cs := rfl

theorem gS_mem_len (P cs : List Cell) : (gS P cs).mem.length = P.length + cs.length := by simp [gS]

theorem gS_bs_len (P cs : List Cell) : (gS P cs).bs.length = cs.length := by simp [gS]

theorem gS_size (P cs : List Cell) : (gS P cs).mem.length + (gS P cs).bs.length = P.length + 2 * cs.length := by
  simp [gS]; omega

theorem gS_bs_get (P cs : List Cell) (k : Nat) (hk : k < cs.length) :
    (gS P cs).bs[k]? = some ⟨P.length + k, true⟩ := by
  simp [gS, hk]

theorem gS_mem_get (P cs : List Cell) (k : Nat) (hk : k < cs.length) :
    (gS P cs).mem[P.length + k]? = cs[k]? := by
  simp only [gS_mem]
  rw [List.getElem?_append_right (by omega)]
  simp

/-- Reading variable `k + 1` (variable 0 is the vector) of a well-typed cell. -/
theorem gS_env (P cs : List Cell) (k : Nat) (c : Cell) (hk : cs[k]? = some c) (hv : c.type.valid c.value = true) :
    penv1 (gS P cs) (k + 1) c.type = some c.value := by
  have hlt : k < cs.length := (List.getElem?_eq_some_iff.mp hk).1
  show penv (gS P cs) k c.type = some c.value
  exact Proofs.PexecKit.penv_ok (gS P cs) k c.type ⟨P.length + k, true⟩ c (gS_bs_get P cs k hlt)
    (by rw [gS_mem_get P cs k hlt]; exact hk) rfl hv

theorem gS_decl (ty0 : Ty) (P cs : List Cell) (vec : List Int) (ty : Ty) (e : NExpr) (v v' : Int)
    (hv : vdenL ty0 vec (penv1 (gS P cs)) e = some v) (hc : ty.convert v = some v') :
    pstmtW ty0 (.declare ty true e) (gS P cs) vec =
      some ⟨gS P (cs ++ [⟨ty, v'⟩]), vec, none, (vwp e).1 + 1, P.length + 2 * cs.length + (vwp e).2 + 4, 0⟩ := by
  have h := pstmtW_declare_ok ty0 (gS P cs) vec ty true e v hv v' hc
  have hmem : (gS P cs).mem ++ [⟨ty, v'⟩] = (gS P (cs ++ [⟨ty, v'⟩])).mem := by
    simp [gS]
  have hbs : (gS P cs).bs ++ [⟨(gS P cs).mem.length, true⟩] = (gS P (cs ++ [⟨ty, v'⟩])).bs := by
    simp [gS, List.range_succ]
  rw [h, hmem, hbs]
  simp only [Option.some.injEq, PRW.mk.injEq, true_and, gS_mem_len, gS_bs_len]
  exact ⟨by omega, trivial⟩

theorem gS_assign (ty0 : Ty) (P cs : List Cell) (vec : List Int) (slot : Nat) (hslot : slot < cs.length) (ty : Ty)
    (e : NExpr) (v v' : Int) (hv : vdenL ty0 vec (penv1 (gS P cs)) e = some v) (c : Cell) (hc : cs[slot]? = some c)
    (hct : c.type = ty) (hcv : ty.valid c.value = true) (hconv : ty.convert v = some v') :
    pstmtW ty0 (.assign (slot + 1) ty e) (gS P cs) vec =
      some ⟨gS P (cs.set slot ⟨ty, v'⟩), vec, none, (vwp e).1 + 1, P.length + 2 * cs.length + (vwp e).2 + 2, 0⟩ := by
  have hb := gS_bs_get P cs slot hslot
  have hm : (gS P cs).mem[(⟨P.length + slot, true⟩ : CppState.Binding).address]? = some c := by
    show (gS P cs).mem[P.length + slot]? = some c
    rw [gS_mem_get P cs slot hslot]; exact hc
  have h := pstmtW_assign_ok ty0 (gS P cs) vec slot ty e v hv ⟨P.length + slot, true⟩ c hb hm hct hcv rfl v' hconv
  have key : (⟨(gS P cs).mem.set (P.length + slot) ⟨ty, v'⟩, (gS P cs).bs⟩ : PS) = gS P (cs.set slot ⟨ty, v'⟩) := by
    simp only [gS, List.length_set]
    rw [List.set_append_right _ _ (by omega)]
    simp
  rw [h]
  dsimp only
  rw [key]
  simp only [Option.some.injEq, PRW.mk.injEq, true_and, gS_mem_len, gS_bs_len]
  exact ⟨by omega, trivial⟩

end Proofs.GenState
