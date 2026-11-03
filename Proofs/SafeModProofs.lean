import Proofs.Generated.SafeMod

namespace Proofs.SafeModProofs
open Proofs.CppScalar Proofs.CppState

def signed64 : Ty := ⟨64, true, false⟩

theorem quotient_valid (x m : Int) (hx : signed64.valid x = true)
    (hm : signed64.valid m = true) (positive : 0 < m) :
    signed64.valid (x.tdiv m) = true := by
  have bx : -9223372036854775808 ≤ x ∧ x < 9223372036854775808 := of_decide_eq_true hx
  have bm : -9223372036854775808 ≤ m ∧ m < 9223372036854775808 := of_decide_eq_true hm
  have nonnegative : 0 ≤ m := by omega
  by_cases sign : 0 ≤ x
  · have low := Int.tdiv_nonneg sign nonnegative
    have high := Int.tdiv_le_self m sign
    show decide (-9223372036854775808 ≤ x.tdiv m ∧ x.tdiv m < 9223372036854775808) = true
    apply decide_eq_true
    omega
  · have negSign : 0 ≤ -x := by omega
    have low := Int.tdiv_nonneg negSign nonnegative
    have high := Int.tdiv_le_self m negSign
    rw [Int.neg_tdiv] at low high
    show decide (-9223372036854775808 ≤ x.tdiv m ∧ x.tdiv m < 9223372036854775808) = true
    apply decide_eq_true
    omega

theorem remainder_valid (x m : Int) (hm : signed64.valid m = true) (positive : 0 < m) :
    signed64.valid (x.tmod m) = true := by
  have bm : -9223372036854775808 ≤ m ∧ m < 9223372036854775808 := of_decide_eq_true hm
  have low := Int.lt_tmod_of_pos x positive
  have high := Int.tmod_lt_of_pos x positive
  show decide (-9223372036854775808 ≤ x.tmod m ∧ x.tmod m < 9223372036854775808) = true
  apply decide_eq_true
  omega

theorem normalized_remainder (x m : Int) (positive : 0 < m) :
    (if x.tmod m < 0 then x.tmod m + m else x.tmod m) = x % m := by
  have nonzero : m ≠ 0 := by omega
  have low := Int.emod_nonneg x nonzero
  have high := Int.emod_lt_of_pos x positive
  have habs : (m.natAbs : Int) = m := Int.natAbs_of_nonneg (by omega)
  have relation := Int.tmod_eq_emod (a := x) (b := m)
  by_cases h : 0 ≤ x ∨ m ∣ x
  · simp [h] at relation
    rw [relation]
    have hn : ¬x % m < 0 := by omega
    simp [hn]
  · simp [h, habs] at relation
    rw [relation]
    have hn : x % m - m < 0 := by omega
    simp [hn]

theorem safe_mod_correct (x m : Int) (memory : List Cell := [])
    (hx : signed64.valid x = true) (hm : signed64.valid m = true) (positive : 0 < m) :
    SafeModInstance.safe_mod.call memory [.value x, .value m] =
      some ⟨x % m, memory, if x.tmod m < 0 then 15 else 11, 8⟩ := by
  have htake : memory.take (memory.length + 2) = memory := List.take_of_length_le (by omega)
  have hn : ¬ memory.length + 1 < memory.length := by omega
  have hn2 : memory.length + 1 + 1 - memory.length = 2 := by omega
  have bx : -9223372036854775808 ≤ x ∧ x < 9223372036854775808 := of_decide_eq_true hx
  have bm : -9223372036854775808 ≤ m ∧ m < 9223372036854775808 := of_decide_eq_true hm
  have nonzero : m ≠ 0 := by omega
  have hq := quotient_valid x m hx hm positive
  have hr := remainder_valid x m hm positive
  have br : -9223372036854775808 ≤ x.tmod m ∧ x.tmod m < 9223372036854775808 := of_decide_eq_true hr
  have hchecked := checkedDivRem_remainder_exact signed64 x m nonzero hq hr
  simp only [signed64] at hchecked
  have norm := normalized_remainder x m positive
  by_cases negative : x.tmod m < 0
  · have rlow := Int.lt_tmod_of_pos x positive
    have badd : -9223372036854775808 ≤ x.tmod m + m ∧ x.tmod m + m < 9223372036854775808 := by omega
    have heq : x % m = x.tmod m + m := by simpa [negative] using norm.symm
    simp [SafeModInstance.safe_mod, StateProgram.call, bindArguments, bindArgument,
      Stmt.run, State.evaluate, State.environment, State.observe, Expr.eval, Expr.nodes,
      binaryValue, hchecked, Ty.convert, Ty.valid, List.getElem?_append, hn, hn2, List.take_append, htake,
      bx.1, bx.2, bm.1, bm.2, br.1, br.2, badd.1, badd.2,
      negative, heq]
  · have heq : x % m = x.tmod m := by simpa [negative] using norm.symm
    simp [SafeModInstance.safe_mod, StateProgram.call, bindArguments, bindArgument,
      Stmt.run, State.evaluate, State.environment, State.observe, Expr.eval, Expr.nodes,
      binaryValue, hchecked, Ty.convert, Ty.valid, List.getElem?_append, hn, hn2, List.take_append, htake,
      bx.1, bx.2, bm.1, bm.2, br.1, br.2,
      negative, heq]

theorem safe_mod_bounds (x m : Int) (memory : List Cell := [])
    (hx : signed64.valid x = true) (hm : signed64.valid m = true) (positive : 0 < m) :
    ∃ result, SafeModInstance.safe_mod.call memory [.value x, .value m] = some result ∧
      0 ≤ result.value ∧ result.value < m ∧ result.memory = memory ∧
      result.work ≤ 15 ∧ result.peak ≤ 8 := by
  refine ⟨_, safe_mod_correct x m memory hx hm positive, ?_, ?_, rfl, ?_, by simp⟩
  · exact Int.emod_nonneg x (by omega)
  · exact Int.emod_lt_of_pos x positive
  · dsimp
    split <;> decide

end Proofs.SafeModProofs
