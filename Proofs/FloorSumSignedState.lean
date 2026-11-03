import Proofs.FloorSumSignedCorrection
import Proofs.CppAssignment

namespace Proofs.FloorSumSignedState
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppAssignment
open Proofs.FloorSumSignedCorrection Proofs.FloorSumArithmetic Proofs.FloorSumState Proofs.SafeModProofs

def correctionState (n m a b ans temporary remainder : Int) (caller : List Cell)
    (work base peak : Nat) : State :=
  ⟨caller ++ [⟨signed64,n⟩,⟨signed64,m⟩,⟨signed64,a⟩,⟨signed64,b⟩,
    ⟨unsigned64,ans⟩,⟨signed64,temporary⟩,⟨unsigned64,remainder⟩],
    [⟨caller.length,true⟩,⟨caller.length+1,true⟩,⟨caller.length+2,true⟩,
      ⟨caller.length+3,true⟩,⟨caller.length+4,true⟩,⟨caller.length+5,false⟩,
      ⟨caller.length+6,true⟩],work,base,peak⟩

theorem correction_environment (n m a b ans temporary remainder : Int) (caller : List Cell)
    (work base peak : Nat) (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true)
    (hv : unsigned64.valid ans = true) (ht : signed64.valid temporary = true)
    (hr : unsigned64.valid remainder = true) :
    (correctionState n m a b ans temporary remainder caller work base peak).environment =
      some [n,m,a,b,ans,temporary,remainder] := by
  have outside (i : Nat) : ¬ caller.length+i < caller.length := by omega
  simp [correctionState,State.environment,List.getElem?_append,outside,hn,hm,ha,hb,hv,ht,hr]

theorem unsigned_mod_valid (value : Int) : unsigned64.valid (value%(wordLimit:Int)) = true := by
  have low := Int.emod_nonneg value (by decide : (wordLimit:Int) ≠ 0)
  have high := Int.emod_lt_of_pos value (by decide : 0 < (wordLimit:Int))
  show decide (0 ≤ value%18446744073709551616 ∧ value%18446744073709551616 < 18446744073709551616) = true
  simp only [wordLimit] at low high
  change 0 ≤ value%18446744073709551616 at low
  change value%18446744073709551616 < 18446744073709551616 at high
  exact decide_eq_true (And.intro low high)

theorem normalized_unsigned_valid (x : Int) (m : Nat) (hm : m < inputLimit) (positive : 0 < m) :
    unsigned64.valid (x%(m:Int)) = true := by
  have low := Int.emod_nonneg x (by omega : (m:Int) ≠ 0)
  have high := Int.emod_lt_of_pos x (by omega : 0 < (m:Int))
  show decide (0 ≤ x%(m:Int) ∧ x%(m:Int) < 18446744073709551616) = true
  apply decide_eq_true
  simp only [inputLimit] at hm
  omega

-- The generic write theorem isolates the state transition from the large
-- mathematical proof of the expression being assigned.
theorem assign_ans (n m a b ans temporary remainder value : Int) (caller : List Cell)
    (work base peak cost : Nat) (e : Expr)
    (evaluated : (correctionState n m a b ans temporary remainder caller work base peak).evaluate e =
      some ⟨value,cost⟩) (valid : unsigned64.valid value = true) (nodes : e.nodes = cost) :
    (Stmt.assign 4 e).run (correctionState n m a b ans temporary remainder caller work base peak) =
      some ⟨correctionState n m a b value temporary remainder caller (work+cost+1) base
        (max peak (caller.length+7-base+7+cost)),none,false⟩ := by
  have hb : (correctionState n m a b ans temporary remainder caller work base peak).bindings[4]? =
      some ⟨caller.length+4,true⟩ := rfl
  have hc : (correctionState n m a b ans temporary remainder caller work base peak).memory[caller.length+4]? =
      some ⟨unsigned64,ans⟩ := by simp [correctionState]
  have result := assign_runs _ 4 e ⟨caller.length+4,true⟩ ⟨unsigned64,ans⟩ ⟨value,cost⟩ value
    hb rfl hc evaluated (Ty.convert_of_valid unsigned64 value valid)
  simpa [correctionState,State.observe,List.set_append,nodes,Nat.add_assoc] using result

theorem a_assign_ans (n m : Nat) (a b ans temporary : Int) (caller : List Cell) (work base peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (negative : a < 0)
    (hv : unsigned64.valid ans = true) (ht : signed64.valid temporary = true) :
    (Stmt.assign 4 (ansUpdateExpression aCorrectionExpression)).run
      (correctionState n m a b ans temporary (a%(m:Int)) caller work base peak) =
      some ⟨correctionState n m a b
        ((ans-(triangle n:Int)*(-(a/(m:Int))))%(wordLimit:Int)) temporary (a%(m:Int)) caller
        (work+22) base (max peak (caller.length+7-base+28)),none,false⟩ := by
  have env := correction_environment n m a b ans temporary (a%(m:Int)) caller work base peak
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv ht (normalized_unsigned_valid a m hm positive)
  have expression := aAnsUpdate_eval n m a b ans temporary [] hn hm positive ha negative hv
  have evaluated : (correctionState n m a b ans temporary (a%(m:Int)) caller work base peak).evaluate
      (ansUpdateExpression aCorrectionExpression) = some ⟨(ans-(triangle n:Int)*(-(a/(m:Int))))%(wordLimit:Int),21⟩ := by
    simpa [State.evaluate,env] using expression
  simpa only [Nat.add_assoc] using assign_ans _ _ _ _ _ _ _ _ caller work base peak 21
    (ansUpdateExpression aCorrectionExpression) evaluated (unsigned_mod_valid _) (by decide)

theorem b_assign_ans (n m : Nat) (a b ans temporary : Int) (caller : List Cell) (work base peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (negative : b < 0)
    (hv : unsigned64.valid ans = true) (ht : signed64.valid temporary = true) :
    (Stmt.assign 4 (ansUpdateExpression bCorrectionExpression)).run
      (correctionState n m a b ans temporary (b%(m:Int)) caller work base peak) =
      some ⟨correctionState n m a b
        ((ans-(n:Int)*(-(b/(m:Int))))%(wordLimit:Int)) temporary (b%(m:Int)) caller
        (work+13) base (max peak (caller.length+7-base+19)),none,false⟩ := by
  have env := correction_environment n m a b ans temporary (b%(m:Int)) caller work base peak
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv ht (normalized_unsigned_valid b m hm positive)
  have expression := bAnsUpdate_eval n m a b ans temporary [] hn hm positive hb negative hv
  have evaluated : (correctionState n m a b ans temporary (b%(m:Int)) caller work base peak).evaluate
      (ansUpdateExpression bCorrectionExpression) = some ⟨(ans-(n:Int)*(-(b/(m:Int))))%(wordLimit:Int),12⟩ := by
    simpa [State.evaluate,env] using expression
  simpa only [Nat.add_assoc] using assign_ans _ _ _ _ _ _ _ _ caller work base peak 12
    (ansUpdateExpression bCorrectionExpression) evaluated (unsigned_mod_valid _) (by decide)


def normalizedExpression : Expr := .targetCast signed64 (.variable unsigned64 6)

theorem normalized_signed_valid (x : Int) (m : Nat) (hm : m < inputLimit) (positive : 0 < m) :
    signed64.valid (x%(m:Int)) = true := by
  have low := Int.emod_nonneg x (by omega : (m:Int) ≠ 0)
  have high := Int.emod_lt_of_pos x (by omega : 0 < (m:Int))
  show decide (-9223372036854775808 ≤ x%(m:Int) ∧ x%(m:Int) < 9223372036854775808) = true
  apply decide_eq_true
  simp only [inputLimit] at hm
  omega

theorem normalized_eval (env : List Int) (x : Int) (m : Nat)
    (slot : env[6]? = some (x%(m:Int))) (hm : m < inputLimit) (positive : 0 < m) :
    normalizedExpression.eval env = some ⟨x%(m:Int),2⟩ := by
  simp [normalizedExpression,Expr.eval,slot,normalized_unsigned_valid x m hm positive,
    normalized_targetCast x m hm positive]

theorem a_assign_normalized (n m : Nat) (a b ans temporary : Int) (caller : List Cell) (work base peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true)
    (hv : unsigned64.valid ans = true) (ht : signed64.valid temporary = true) :
    (Stmt.assign 2 normalizedExpression).run
      (correctionState n m a b ans temporary (a%(m:Int)) caller work base peak) =
      some ⟨correctionState n m (a%(m:Int)) b ans temporary (a%(m:Int)) caller
        (work+3) base (max peak (caller.length+7-base+9)),none,false⟩ := by
  have env := correction_environment n m a b ans temporary (a%(m:Int)) caller work base peak
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv ht (normalized_unsigned_valid a m hm positive)
  have expression := normalized_eval [(n:Int),(m:Int),a,b,ans,temporary,a%(m:Int)] a m rfl hm positive
  have evaluated : (correctionState n m a b ans temporary (a%(m:Int)) caller work base peak).evaluate
      normalizedExpression = some ⟨a%(m:Int),2⟩ := by
    simpa [State.evaluate,env] using expression
  have binding : (correctionState n m a b ans temporary (a%(m:Int)) caller work base peak).bindings[2]? =
      some ⟨caller.length+2,true⟩ := rfl
  have cell : (correctionState n m a b ans temporary (a%(m:Int)) caller work base peak).memory[caller.length+2]? =
      some ⟨signed64,a⟩ := by simp [correctionState]
  have result := assign_runs _ 2 normalizedExpression ⟨caller.length+2,true⟩ ⟨signed64,a⟩
    ⟨a%(m:Int),2⟩ (a%(m:Int)) binding rfl cell evaluated
    (Ty.convert_of_valid signed64 _ (normalized_signed_valid a m hm positive))
  simpa [correctionState,State.observe,List.set_append,normalizedExpression,Expr.nodes,Nat.add_assoc] using result

theorem b_assign_normalized (n m : Nat) (a b ans temporary : Int) (caller : List Cell) (work base peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true)
    (hv : unsigned64.valid ans = true) (ht : signed64.valid temporary = true) :
    (Stmt.assign 3 normalizedExpression).run
      (correctionState n m a b ans temporary (b%(m:Int)) caller work base peak) =
      some ⟨correctionState n m a (b%(m:Int)) ans temporary (b%(m:Int)) caller
        (work+3) base (max peak (caller.length+7-base+9)),none,false⟩ := by
  have env := correction_environment n m a b ans temporary (b%(m:Int)) caller work base peak
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv ht (normalized_unsigned_valid b m hm positive)
  have expression := normalized_eval [(n:Int),(m:Int),a,b,ans,temporary,b%(m:Int)] b m rfl hm positive
  have evaluated : (correctionState n m a b ans temporary (b%(m:Int)) caller work base peak).evaluate
      normalizedExpression = some ⟨b%(m:Int),2⟩ := by
    simpa [State.evaluate,env] using expression
  have binding : (correctionState n m a b ans temporary (b%(m:Int)) caller work base peak).bindings[3]? =
      some ⟨caller.length+3,true⟩ := rfl
  have cell : (correctionState n m a b ans temporary (b%(m:Int)) caller work base peak).memory[caller.length+3]? =
      some ⟨signed64,b⟩ := by simp [correctionState]
  have result := assign_runs _ 3 normalizedExpression ⟨caller.length+3,true⟩ ⟨signed64,b⟩
    ⟨b%(m:Int),2⟩ (b%(m:Int)) binding rfl cell evaluated
    (Ty.convert_of_valid signed64 _ (normalized_signed_valid b m hm positive))
  simpa [correctionState,State.observe,List.set_append,normalizedExpression,Expr.nodes,Nat.add_assoc] using result

def correctionTail (product : Expr) (slot : Nat) : Stmt :=
  .sequence (.assign 4 (ansUpdateExpression product)) (.sequence (.assign slot normalizedExpression) .skip)

theorem a_correction_tail (n m : Nat) (a b ans temporary : Int) (caller : List Cell) (work base peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (negative : a < 0)
    (hv : unsigned64.valid ans = true) (ht : signed64.valid temporary = true) :
    runFuel 3 (correctionTail aCorrectionExpression 2)
      (correctionState n m a b ans temporary (a%(m:Int)) caller work base peak) =
      .finished ⟨correctionState n m (a%(m:Int)) b ((ans-(triangle n:Int)*(-(a/(m:Int))))%(wordLimit:Int)) temporary (a%(m:Int)) caller
        (work+25) base (max peak (caller.length+7-base+28)),none,false⟩ := by
  have first := a_assign_ans n m a b ans temporary caller work base peak hn hm positive ha hb negative hv ht
  have second := a_assign_normalized n m a b ((ans-(triangle n:Int)*(-(a/(m:Int))))%(wordLimit:Int)) temporary caller
    (work+22) base (max peak (caller.length+7-base+28))
    hn hm positive ha hb (unsigned_mod_valid _) ht
  simp only [correctionTail,runFuel,liftChecked,first,bind,Outcome.bind,Option.isSome_none,
    Bool.false_or,second]
  simp [Stmt.run,correctionState,Nat.add_assoc]

theorem b_correction_tail (n m : Nat) (a b ans temporary : Int) (caller : List Cell) (work base peak : Nat)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (negative : b < 0)
    (hv : unsigned64.valid ans = true) (ht : signed64.valid temporary = true) :
    runFuel 3 (correctionTail bCorrectionExpression 3)
      (correctionState n m a b ans temporary (b%(m:Int)) caller work base peak) =
      .finished ⟨correctionState n m a (b%(m:Int)) ((ans-(n:Int)*(-(b/(m:Int))))%(wordLimit:Int)) temporary (b%(m:Int)) caller
        (work+16) base (max peak (caller.length+7-base+19)),none,false⟩ := by
  have first := b_assign_ans n m a b ans temporary caller work base peak hn hm positive ha hb negative hv ht
  have second := b_assign_normalized n m a b ((ans-(n:Int)*(-(b/(m:Int))))%(wordLimit:Int)) temporary caller
    (work+13) base (max peak (caller.length+7-base+19))
    hn hm positive ha hb (unsigned_mod_valid _) ht
  simp only [correctionTail,runFuel,liftChecked,first,bind,Outcome.bind,Option.isSome_none,
    Bool.false_or,second]
  simp [Stmt.run,correctionState,Nat.add_assoc]

end Proofs.FloorSumSignedState
