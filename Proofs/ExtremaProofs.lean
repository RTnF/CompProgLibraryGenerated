import Proofs.ExtremaInstances

namespace Proofs.ExtremaProofs
open Proofs.CppScalar Proofs.CppState

def signed32 : Ty := ⟨32, true, false⟩
def unsigned32 : Ty := ⟨32, false, false⟩

theorem chmax_signed (a b : Int) (tail : List Cell := [])
    (ha : signed32.valid a = true) (hb : signed32.valid b = true) :
    ExtremaInstances.chmax__int__int.call ([⟨signed32, a⟩, ⟨signed32, b⟩] ++ tail)
      [.reference 0, .reference 1] =
    some ⟨if a < b then 1 else 0,
      [⟨signed32, max a b⟩, ⟨signed32, b⟩] ++ tail, if a < b then 9 else 7, 5⟩ := by
  have ha' : -2147483648 ≤ a ∧ a < 2147483648 := of_decide_eq_true ha
  have hb' : -2147483648 ≤ b ∧ b < 2147483648 := of_decide_eq_true hb
  have hbadA : ¬ (a < -2147483648 ∨ 2147483648 ≤ a) := by omega
  have hbadB : ¬ (b < -2147483648 ∨ 2147483648 ≤ b) := by omega
  by_cases h : a < b
  · have hn : ¬b ≤ a := by omega
    have hm : max a b = b := by omega
    simp [ExtremaInstances.chmax__int__int, StateProgram.call, bindArguments,
      bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
      Expr.eval, Expr.nodes, binaryValue, Ty.convert, signed32, Ty.valid,
      ha'.1, ha'.2, hb'.1, hb'.2, h, hn, hm, hbadA, hbadB]
  · have hn : b ≤ a := by omega
    have hm : max a b = a := by omega
    simp [ExtremaInstances.chmax__int__int, StateProgram.call, bindArguments,
      bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
      Expr.eval, Expr.nodes, binaryValue, Ty.convert, signed32, Ty.valid,
      ha'.1, ha'.2, hb'.1, hb'.2, h, hn, hm, hbadA, hbadB]

theorem chmin_signed (a b : Int) (tail : List Cell := [])
    (ha : signed32.valid a = true) (hb : signed32.valid b = true) :
    ExtremaInstances.chmin__int__int.call ([⟨signed32, a⟩, ⟨signed32, b⟩] ++ tail)
      [.reference 0, .reference 1] =
    some ⟨if b < a then 1 else 0,
      [⟨signed32, min a b⟩, ⟨signed32, b⟩] ++ tail, if b < a then 9 else 7, 5⟩ := by
  have ha' : -2147483648 ≤ a ∧ a < 2147483648 := of_decide_eq_true ha
  have hb' : -2147483648 ≤ b ∧ b < 2147483648 := of_decide_eq_true hb
  have hbadA : ¬ (a < -2147483648 ∨ 2147483648 ≤ a) := by omega
  have hbadB : ¬ (b < -2147483648 ∨ 2147483648 ≤ b) := by omega
  by_cases h : b < a
  · have hn : ¬a ≤ b := by omega
    have hm : min a b = b := by omega
    simp [ExtremaInstances.chmin__int__int, StateProgram.call, bindArguments,
      bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
      Expr.eval, Expr.nodes, binaryValue, Ty.convert, signed32, Ty.valid,
      ha'.1, ha'.2, hb'.1, hb'.2, h, hn, hm, hbadA, hbadB]
  · have hn : a ≤ b := by omega
    have hm : min a b = a := by omega
    simp [ExtremaInstances.chmin__int__int, StateProgram.call, bindArguments,
      bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
      Expr.eval, Expr.nodes, binaryValue, Ty.convert, signed32, Ty.valid,
      ha'.1, ha'.2, hb'.1, hb'.2, h, hn, hm, hbadA, hbadB]

theorem chmax_unsigned (a b : Int) (tail : List Cell := [])
    (ha : unsigned32.valid a = true) (hb : unsigned32.valid b = true) :
    ExtremaInstances.chmax__unsigned_int__unsigned_int.call ([⟨unsigned32, a⟩, ⟨unsigned32, b⟩] ++ tail)
      [.reference 0, .reference 1] =
    some ⟨if a < b then 1 else 0,
      [⟨unsigned32, max a b⟩, ⟨unsigned32, b⟩] ++ tail, if a < b then 9 else 7, 5⟩ := by
  have ha' : 0 ≤ a ∧ a < 4294967296 := of_decide_eq_true ha
  have hb' : 0 ≤ b ∧ b < 4294967296 := of_decide_eq_true hb
  have hbadA : ¬ (a < 0 ∨ 4294967296 ≤ a) := by omega
  have hbadB : ¬ (b < 0 ∨ 4294967296 ≤ b) := by omega
  have hmodB : b % 4294967296 = b := Int.emod_eq_of_lt hb'.1 hb'.2
  by_cases h : a < b
  · have hn : ¬b ≤ a := by omega
    have hm : max a b = b := by omega
    simp [ExtremaInstances.chmax__unsigned_int__unsigned_int, StateProgram.call, bindArguments,
      bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
      Expr.eval, Expr.nodes, binaryValue, Ty.convert, unsigned32, Ty.valid,
      ha'.1, ha'.2, hb'.1, hb'.2, h, hn, hm, hbadA, hbadB, hmodB]
  · have hn : b ≤ a := by omega
    have hm : max a b = a := by omega
    simp [ExtremaInstances.chmax__unsigned_int__unsigned_int, StateProgram.call, bindArguments,
      bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
      Expr.eval, Expr.nodes, binaryValue, Ty.convert, unsigned32, Ty.valid,
      ha'.1, ha'.2, hb'.1, hb'.2, h, hn, hm, hbadA, hbadB, hmodB]

theorem chmin_unsigned (a b : Int) (tail : List Cell := [])
    (ha : unsigned32.valid a = true) (hb : unsigned32.valid b = true) :
    ExtremaInstances.chmin__unsigned_int__unsigned_int.call ([⟨unsigned32, a⟩, ⟨unsigned32, b⟩] ++ tail)
      [.reference 0, .reference 1] =
    some ⟨if b < a then 1 else 0,
      [⟨unsigned32, min a b⟩, ⟨unsigned32, b⟩] ++ tail, if b < a then 9 else 7, 5⟩ := by
  have ha' : 0 ≤ a ∧ a < 4294967296 := of_decide_eq_true ha
  have hb' : 0 ≤ b ∧ b < 4294967296 := of_decide_eq_true hb
  have hbadA : ¬ (a < 0 ∨ 4294967296 ≤ a) := by omega
  have hbadB : ¬ (b < 0 ∨ 4294967296 ≤ b) := by omega
  have hmodB : b % 4294967296 = b := Int.emod_eq_of_lt hb'.1 hb'.2
  by_cases h : b < a
  · have hn : ¬a ≤ b := by omega
    have hm : min a b = b := by omega
    simp [ExtremaInstances.chmin__unsigned_int__unsigned_int, StateProgram.call, bindArguments,
      bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
      Expr.eval, Expr.nodes, binaryValue, Ty.convert, unsigned32, Ty.valid,
      ha'.1, ha'.2, hb'.1, hb'.2, h, hn, hm, hbadA, hbadB, hmodB]
  · have hn : a ≤ b := by omega
    have hm : min a b = a := by omega
    simp [ExtremaInstances.chmin__unsigned_int__unsigned_int, StateProgram.call, bindArguments,
      bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
      Expr.eval, Expr.nodes, binaryValue, Ty.convert, unsigned32, Ty.valid,
      ha'.1, ha'.2, hb'.1, hb'.2, h, hn, hm, hbadA, hbadB, hmodB]

theorem chmax_signed_alias (a : Int) (tail : List Cell := [])
    (ha : signed32.valid a = true) :
    ExtremaInstances.chmax__int__int.call ([⟨signed32, a⟩] ++ tail) [.reference 0, .reference 0] =
    some ⟨0, [⟨signed32, a⟩] ++ tail, 7, 5⟩ := by
  have ha' : -2147483648 ≤ a ∧ a < 2147483648 := of_decide_eq_true ha
  have hbadA : ¬ (a < -2147483648 ∨ 2147483648 ≤ a) := by omega
  simp [ExtremaInstances.chmax__int__int, StateProgram.call, bindArguments,
    bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
    Expr.eval, Expr.nodes, binaryValue, Ty.convert, signed32, Ty.valid,
    ha'.1, ha'.2, hbadA]

theorem chmin_signed_alias (a : Int) (tail : List Cell := [])
    (ha : signed32.valid a = true) :
    ExtremaInstances.chmin__int__int.call ([⟨signed32, a⟩] ++ tail) [.reference 0, .reference 0] =
    some ⟨0, [⟨signed32, a⟩] ++ tail, 7, 5⟩ := by
  have ha' : -2147483648 ≤ a ∧ a < 2147483648 := of_decide_eq_true ha
  have hbadA : ¬ (a < -2147483648 ∨ 2147483648 ≤ a) := by omega
  simp [ExtremaInstances.chmin__int__int, StateProgram.call, bindArguments,
    bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
    Expr.eval, Expr.nodes, binaryValue, Ty.convert, signed32, Ty.valid,
    ha'.1, ha'.2, hbadA]

theorem chmax_unsigned_alias (a : Int) (tail : List Cell := [])
    (ha : unsigned32.valid a = true) :
    ExtremaInstances.chmax__unsigned_int__unsigned_int.call ([⟨unsigned32, a⟩] ++ tail) [.reference 0, .reference 0] =
    some ⟨0, [⟨unsigned32, a⟩] ++ tail, 7, 5⟩ := by
  have ha' : 0 ≤ a ∧ a < 4294967296 := of_decide_eq_true ha
  have hbadA : ¬ (a < 0 ∨ 4294967296 ≤ a) := by omega
  simp [ExtremaInstances.chmax__unsigned_int__unsigned_int, StateProgram.call, bindArguments,
    bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
    Expr.eval, Expr.nodes, binaryValue, Ty.convert, unsigned32, Ty.valid,
    ha'.1, ha'.2, hbadA]

theorem chmin_unsigned_alias (a : Int) (tail : List Cell := [])
    (ha : unsigned32.valid a = true) :
    ExtremaInstances.chmin__unsigned_int__unsigned_int.call ([⟨unsigned32, a⟩] ++ tail) [.reference 0, .reference 0] =
    some ⟨0, [⟨unsigned32, a⟩] ++ tail, 7, 5⟩ := by
  have ha' : 0 ≤ a ∧ a < 4294967296 := of_decide_eq_true ha
  have hbadA : ¬ (a < 0 ∨ 4294967296 ≤ a) := by omega
  simp [ExtremaInstances.chmin__unsigned_int__unsigned_int, StateProgram.call, bindArguments,
    bindArgument, Stmt.run, State.evaluate, State.environment, State.observe,
    Expr.eval, Expr.nodes, binaryValue, Ty.convert, unsigned32, Ty.valid,
    ha'.1, ha'.2, hbadA]

theorem chmax_signed_bounds (a b : Int) (tail : List Cell := [])
    (ha : signed32.valid a = true) (hb : signed32.valid b = true) :
    ∃ result, ExtremaInstances.chmax__int__int.call
      ([⟨signed32, a⟩, ⟨signed32, b⟩] ++ tail) [.reference 0, .reference 1] = some result ∧
      result.work ≤ 9 ∧ result.peak ≤ 5 := by
  refine ⟨_, chmax_signed a b tail ha hb, ?_, by simp⟩
  dsimp
  split <;> decide

theorem chmin_signed_bounds (a b : Int) (tail : List Cell := [])
    (ha : signed32.valid a = true) (hb : signed32.valid b = true) :
    ∃ result, ExtremaInstances.chmin__int__int.call
      ([⟨signed32, a⟩, ⟨signed32, b⟩] ++ tail) [.reference 0, .reference 1] = some result ∧
      result.work ≤ 9 ∧ result.peak ≤ 5 := by
  refine ⟨_, chmin_signed a b tail ha hb, ?_, by simp⟩
  dsimp
  split <;> decide

theorem chmax_unsigned_bounds (a b : Int) (tail : List Cell := [])
    (ha : unsigned32.valid a = true) (hb : unsigned32.valid b = true) :
    ∃ result, ExtremaInstances.chmax__unsigned_int__unsigned_int.call
      ([⟨unsigned32, a⟩, ⟨unsigned32, b⟩] ++ tail) [.reference 0, .reference 1] = some result ∧
      result.work ≤ 9 ∧ result.peak ≤ 5 := by
  refine ⟨_, chmax_unsigned a b tail ha hb, ?_, by simp⟩
  dsimp
  split <;> decide

theorem chmin_unsigned_bounds (a b : Int) (tail : List Cell := [])
    (ha : unsigned32.valid a = true) (hb : unsigned32.valid b = true) :
    ∃ result, ExtremaInstances.chmin__unsigned_int__unsigned_int.call
      ([⟨unsigned32, a⟩, ⟨unsigned32, b⟩] ++ tail) [.reference 0, .reference 1] = some result ∧
      result.work ≤ 9 ∧ result.peak ≤ 5 := by
  refine ⟨_, chmin_unsigned a b tail ha hb, ?_, by simp⟩
  dsimp
  split <;> decide

end Proofs.ExtremaProofs
