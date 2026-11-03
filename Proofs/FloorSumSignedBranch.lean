import Proofs.FloorSumSignedState
import Proofs.SafeModInvoke

namespace Proofs.FloorSumSignedBranch
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppInvokePreparation
open Proofs.FloorSumSignedState Proofs.FloorSumSignedCorrection Proofs.FloorSumState
open Proofs.FloorSumArithmetic Proofs.SafeModProofs

def mainState (n m a b ans : Int) (caller : List Cell) (work base peak : Nat) : State :=
  ⟨caller ++ [⟨signed64,n⟩,⟨signed64,m⟩,⟨signed64,a⟩,⟨signed64,b⟩,⟨unsigned64,ans⟩],
    [⟨caller.length,true⟩,⟨caller.length+1,true⟩,⟨caller.length+2,true⟩,
      ⟨caller.length+3,true⟩,⟨caller.length+4,true⟩],work,base,peak⟩

def temporaryState (n m a b ans remainder : Int) (caller : List Cell) (work base peak : Nat) : State :=
  {mainState n m a b ans caller work base peak with
    memory := (mainState n m a b ans caller work base peak).memory ++ [⟨signed64,remainder⟩],
    bindings := (mainState n m a b ans caller work base peak).bindings ++ [⟨caller.length+5,false⟩]}

theorem main_environment (n m a b ans : Int) (caller : List Cell) (work base peak : Nat)
    (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (hv : unsigned64.valid ans = true) :
    (mainState n m a b ans caller work base peak).environment = some [n,m,a,b,ans] := by
  have outside (i : Nat) : ¬ caller.length+i < caller.length := by omega
  simp [mainState,State.environment,List.getElem?_append,outside,hn,hm,ha,hb,hv]

def callArguments (slot : Nat) : List Expr := [.variable signed64 slot,.variable signed64 1]

theorem arguments_eval (env : List Int) (slot : Nat) (x m : Int)
    (hx : signed64.valid x = true) (hm : signed64.valid m = true)
    (sx : env[slot]? = some x) (sm : env[1]? = some m) :
    (callArguments slot).mapM (Expr.eval env) = some [⟨x,1⟩,⟨m,1⟩] := by
  simp [callArguments,Expr.eval,hx,hm,sx,sm]

-- Exact copied cells and caller bindings; only the peak returned by the
-- already-proved helper remains existential.
theorem invoke_at (n m a b ans x : Int) (caller : List Cell) (work base peak slot : Nat)
    (allocated : base ≤ caller.length) (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (hv : unsigned64.valid ans = true)
    (hx : signed64.valid x = true) (positive : 0 < m) (sx : ([n,m,a,b,ans] : List Int)[slot]? = some x) :
    ∃ nextPeak,
      runFuel 10 (.invoke Proofs.SafeModInvoke.valueParameters signed64 (callArguments slot)
        SafeModInstance.safe_mod.body) (mainState n m a b ans caller work base peak) =
      .finished ⟨temporaryState n m a b ans (x%m) caller
        (work+Proofs.SafeModFrame.bodyWork x m+6) base nextPeak,none,false⟩ ∧
      nextPeak ≤ max peak (caller.length+18-base) := by
  have env := main_environment n m a b ans caller work base peak hn hm ha hb hv
  have evaluated : (callArguments slot).mapM (mainState n m a b ans caller work base peak).evaluate =
      some [⟨x,1⟩,⟨m,1⟩] := by
    have evaluate : (mainState n m a b ans caller work base peak).evaluate = Expr.eval [n,m,a,b,ans] := by
      funext e
      simp [State.evaluate,env]
    rw [evaluate]
    exact arguments_eval [n,m,a,b,ans] slot x m hx hm sx rfl
  obtain ⟨nextPeak,done,bound,_,_,_⟩ := Proofs.SafeModInvoke.invoke_correct
    (mainState n m a b ans caller work base peak) (callArguments slot) x m 1 1 evaluated
    (by simp [mainState]; omega) hx hm positive
  refine ⟨nextPeak,?_,?_⟩
  · have total : 2+(Proofs.SafeModFrame.bodyWork x m+4) = Proofs.SafeModFrame.bodyWork x m+6 := by omega
    simpa [mainState,temporaryState,callArguments,Expr.nodes,List.append_assoc,Nat.add_assoc,total] using done
  · simp [mainState,callerPrefix,argumentPeak,callArguments,Expr.nodes,State.observe] at bound
    omega

def remainderDeclaration : Stmt := .declare unsigned64 true (.cast unsigned64 (.variable signed64 5))

theorem declare_remainder (n m a b ans x : Int) (caller : List Cell) (work base peak : Nat)
    (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (hv : unsigned64.valid ans = true)
    (hr : signed64.valid x = true) (hu : unsigned64.valid x = true) :
    remainderDeclaration.run (temporaryState n m a b ans x caller work base peak) =
      some ⟨correctionState n m a b ans x x caller (work+3) base
        (max peak (caller.length+7-base+9)),none,false⟩ := by
  have outside (i : Nat) : ¬ caller.length+i < caller.length := by omega
  have env : (temporaryState n m a b ans x caller work base peak).environment = some [n,m,a,b,ans,x] := by
    simp [temporaryState,mainState,State.environment,List.getElem?_append,List.append_assoc,outside,hn,hm,ha,hb,hv,hr]
  have converted := Ty.convert_of_valid unsigned64 x hu
  simp only [remainderDeclaration,Stmt.run,State.evaluate,env]
  simp [Expr.eval,hr,converted,Expr.nodes,temporaryState,mainState,correctionState,State.observe,
    List.append_assoc,Nat.add_assoc]

def initialization (slot : Nat) : Stmt :=
  .sequence (.invoke Proofs.SafeModInvoke.valueParameters signed64 (callArguments slot)
    SafeModInstance.safe_mod.body) (.sequence remainderDeclaration .skip)

def negativeBody (product : Expr) (slot : Nat) : Stmt :=
  .scope (.scope (.sequence (initialization slot) (correctionTail product slot)))


theorem sequence_done (fuel : Nat) (first rest : Stmt) (s middle : State) (final : Step)
    (hf : runFuel fuel first s = .finished ⟨middle,none,false⟩)
    (hr : runFuel fuel rest middle = .finished final) :
    runFuel (fuel+1) (.sequence first rest) s = .finished final := by
  rw [runFuel]
  simp only [hf,bind,Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false,hr]

theorem scope_done (fuel : Nat) (body : Stmt) (s : State) (step : Step)
    (done : runFuel fuel body s = .finished step) :
    runFuel (fuel+1) (.scope body) s = .finished {step with state := {step.state with
      memory := step.state.memory.take s.memory.length,bindings := step.state.bindings.take s.bindings.length}} := by
  rw [runFuel]
  simp only [done,bind,Outcome.bind,pure]

theorem initialization_at (n m : Nat) (a b ans x : Int) (caller : List Cell)
    (work base peak slot : Nat) (allocated : base ≤ caller.length)
    (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (hv : unsigned64.valid ans = true)
    (hx : signed64.valid x = true) (sx : ([(n:Int),(m:Int),a,b,ans] : List Int)[slot]? = some x) :
    ∃ nextPeak,
      runFuel 11 (initialization slot) (mainState n m a b ans caller work base peak) =
      .finished ⟨correctionState n m a b ans (x%(m:Int)) (x%(m:Int)) caller
        (work+Proofs.SafeModFrame.bodyWork x m+9) base nextPeak,none,false⟩ ∧
      nextPeak ≤ max peak (caller.length+18-base) := by
  obtain ⟨helperPeak,invoked,bound⟩ := invoke_at n m a b ans x caller work base peak slot allocated
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv hx (by omega) sx
  have declared := declare_remainder n m a b ans (x%(m:Int)) caller
    (work+Proofs.SafeModFrame.bodyWork x m+6) base helperPeak
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv
    (normalized_signed_valid x m hm positive) (normalized_unsigned_valid x m hm positive)
  refine ⟨max helperPeak (caller.length+7-base+9),?_,?_⟩
  · have declaredFuel := congrArg liftChecked declared
    change runFuel 9 remainderDeclaration _ = .finished _ at declaredFuel
    have remainder := sequence_done 9 remainderDeclaration .skip _ _ _ declaredFuel rfl
    have initialized := sequence_done 10 _ (.sequence remainderDeclaration .skip) _ _ _ invoked remainder
    simpa only [initialization,Nat.add_assoc] using initialized
  · omega

theorem restore_correction (n m a b ans temporary remainder : Int) (caller : List Cell)
    (work base peak : Nat) :
    {correctionState n m a b ans temporary remainder caller work base peak with
      memory := (correctionState n m a b ans temporary remainder caller work base peak).memory.take (caller.length+5),
      bindings := (correctionState n m a b ans temporary remainder caller work base peak).bindings.take 5} =
      mainState n m a b ans caller work base peak := by
  have take : caller.take (caller.length+5) = caller := List.take_of_length_le (by omega)
  simp [correctionState,mainState,List.take_append,take]

theorem restore_main (n m a b ans : Int) (caller : List Cell) (work base peak : Nat) :
    {mainState n m a b ans caller work base peak with
      memory := (mainState n m a b ans caller work base peak).memory.take (caller.length+5),
      bindings := (mainState n m a b ans caller work base peak).bindings.take 5} =
      mainState n m a b ans caller work base peak := by
  have take : caller.take (caller.length+5) = caller := List.take_of_length_le (by omega)
  simp [mainState,List.take_append,take]

theorem a_negative_body (n m : Nat) (a b ans : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (negative : a < 0)
    (hv : unsigned64.valid ans = true) :
    ∃ finalPeak,
      runFuel 14 (negativeBody aCorrectionExpression 2) (mainState n m a b ans caller work base peak) =
      .finished ⟨mainState n m (a%(m:Int)) b ((ans-(triangle n:Int)*(-(a/(m:Int))))%(wordLimit:Int)) caller
        (work+Proofs.SafeModFrame.bodyWork a m+34) base finalPeak,none,false⟩ ∧
      finalPeak ≤ max peak (caller.length+35-base) := by
  obtain ⟨preparedPeak,initialized,bound⟩ := initialization_at n m a b ans a caller work base peak 2
    allocated hn hm positive ha hb hv ha rfl
  have tail := a_correction_tail n m a b ans (a%(m:Int)) caller
    (work+Proofs.SafeModFrame.bodyWork a m+9) base preparedPeak hn hm positive ha hb negative hv
    (normalized_signed_valid a m hm positive)
  have padded := runFuel_success_mono 3 8 _ _ _ tail
  refine ⟨max preparedPeak (caller.length+7-base+28),?_,?_⟩
  · have body := sequence_done 11 _ _ _ _ _ initialized padded
    have scopeResult := scope_done 12 _ _ _ body
    have memoryLength : (mainState n m a b ans caller work base peak).memory.length = caller.length+5 := by simp [mainState]
    have bindingLength : (mainState n m a b ans caller work base peak).bindings.length = 5 := rfl
    simp only [memoryLength,bindingLength,restore_correction] at scopeResult
    have outer := scope_done 13 _ _ _ scopeResult
    simpa only [negativeBody,memoryLength,bindingLength,restore_main,Nat.add_assoc] using outer
  · omega

theorem b_negative_body (n m : Nat) (a b ans : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (negative : b < 0)
    (hv : unsigned64.valid ans = true) :
    ∃ finalPeak,
      runFuel 14 (negativeBody bCorrectionExpression 3) (mainState n m a b ans caller work base peak) =
      .finished ⟨mainState n m a (b%(m:Int)) ((ans-(n:Int)*(-(b/(m:Int))))%(wordLimit:Int)) caller
        (work+Proofs.SafeModFrame.bodyWork b m+25) base finalPeak,none,false⟩ ∧
      finalPeak ≤ max peak (caller.length+26-base) := by
  obtain ⟨preparedPeak,initialized,bound⟩ := initialization_at n m a b ans b caller work base peak 3
    allocated hn hm positive ha hb hv hb rfl
  have tail := b_correction_tail n m a b ans (b%(m:Int)) caller
    (work+Proofs.SafeModFrame.bodyWork b m+9) base preparedPeak hn hm positive ha hb negative hv
    (normalized_signed_valid b m hm positive)
  have padded := runFuel_success_mono 3 8 _ _ _ tail
  refine ⟨max preparedPeak (caller.length+7-base+19),?_,?_⟩
  · have body := sequence_done 11 _ _ _ _ _ initialized padded
    have scopeResult := scope_done 12 _ _ _ body
    have memoryLength : (mainState n m a b ans caller work base peak).memory.length = caller.length+5 := by simp [mainState]
    have bindingLength : (mainState n m a b ans caller work base peak).bindings.length = 5 := rfl
    simp only [memoryLength,bindingLength,restore_correction] at scopeResult
    have outer := scope_done 13 _ _ _ scopeResult
    simpa only [negativeBody,memoryLength,bindingLength,restore_main,Nat.add_assoc] using outer
  · omega


def guardExpression (slot : Nat) : Expr :=
  .binary boolType .lt (.variable signed64 slot) (.cast signed64 (.literal ⟨32,true,false⟩ 0))

theorem guard_eval (env : List Int) (slot : Nat) (x : Int)
    (value : env[slot]? = some x) (valid : signed64.valid x = true) :
    (guardExpression slot).eval env = some ⟨if x < 0 then 1 else 0,4⟩ := by
  have zero : signed64.convert 0 = some 0 := by decide
  have literal : (⟨32,true,false⟩ : Ty).valid 0 = true := by decide
  have boolean : boolType.valid (if x < 0 then 1 else 0) = true := by split <;> decide
  have converted := Ty.convert_of_valid boolType (if x < 0 then 1 else 0) boolean
  simp [guardExpression,Expr.eval,value,valid,zero,literal,binaryValue,converted]

theorem guard_at (n m a b ans x : Int) (caller : List Cell) (work base peak slot : Nat)
    (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (hv : unsigned64.valid ans = true)
    (hx : signed64.valid x = true) (sx : ([n,m,a,b,ans] : List Int)[slot]? = some x) :
    (mainState n m a b ans caller work base peak).evaluate (guardExpression slot) =
      some ⟨if x < 0 then 1 else 0,4⟩ := by
  have env := main_environment n m a b ans caller work base peak hn hm ha hb hv
  simpa [State.evaluate,env] using guard_eval [n,m,a,b,ans] slot x sx hx

theorem branch_step (fuel : Nat) (condition : Expr) (yes no : Stmt) (s : State) (result : Result)
    (evaluated : s.evaluate condition = some result) :
    runFuel (fuel+1) (.branch condition yes no) s =
      if result.value == 0 then runFuel fuel no (({s with work := s.work+result.work+1}).observe condition.nodes)
      else runFuel fuel yes (({s with work := s.work+result.work+1}).observe condition.nodes) := by
  rw [runFuel]
  simp only [evaluated,liftChecked,bind,Outcome.bind]

def normalizationBranch (product : Expr) (slot : Nat) : Stmt :=
  .branch (guardExpression slot) (negativeBody product slot) .skip

def normalizedCoefficient (x : Int) (m : Nat) : Int := if x < 0 then x%(m:Int) else x

def correctedAns (ans factor x : Int) (m : Nat) : Int :=
  if x < 0 then (ans-factor*(-(x/(m:Int))))%(wordLimit:Int) else ans

def normalizationWork (x : Int) (m : Nat) (overhead : Nat) : Nat :=
  if x < 0 then Proofs.SafeModFrame.bodyWork x m+overhead+5 else 5

theorem a_normalization_branch (n m : Nat) (a b ans : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (hv : unsigned64.valid ans = true) :
    ∃ finalPeak,
      runFuel 15 (normalizationBranch aCorrectionExpression 2) (mainState n m a b ans caller work base peak) =
      .finished ⟨mainState n m (normalizedCoefficient a m) b (correctedAns ans (triangle n:Int) a m) caller
        (work+normalizationWork a m 34) base finalPeak,none,false⟩ ∧
      finalPeak ≤ max peak (caller.length+35-base) := by
  have evaluated := guard_at n m a b ans a caller work base peak 2
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv ha rfl
  have advanced : ({mainState n m a b ans caller work base peak with work := (mainState n m a b ans caller work base peak).work+4+1}).observe 4 =
      mainState n m a b ans caller (work+5) base (max peak (caller.length+5-base+9)) := by
    simp [mainState,State.observe,Nat.add_assoc]
  have branch := branch_step 14 (guardExpression 2) (negativeBody aCorrectionExpression 2)
    .skip (mainState n m a b ans caller work base peak) _ evaluated
  have nodes : (guardExpression 2).nodes = 4 := rfl
  simp only [nodes,advanced] at branch
  by_cases negative : a < 0
  · obtain ⟨finalPeak,body,bound⟩ := a_negative_body n m a b ans caller (work+5) base
      (max peak (caller.length+5-base+9)) allocated hn hm positive ha hb negative hv
    refine ⟨finalPeak,?_,?_⟩
    · simpa [normalizationBranch,negative,normalizedCoefficient,correctedAns,normalizationWork,body,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using branch
    · omega
  · refine ⟨max peak (caller.length+5-base+9),?_,?_⟩
    · simpa [normalizationBranch,negative,normalizedCoefficient,correctedAns,normalizationWork,skip_succeeds] using branch
    · omega

theorem b_normalization_branch (n m : Nat) (a b ans : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (hv : unsigned64.valid ans = true) :
    ∃ finalPeak,
      runFuel 15 (normalizationBranch bCorrectionExpression 3) (mainState n m a b ans caller work base peak) =
      .finished ⟨mainState n m a (normalizedCoefficient b m) (correctedAns ans (n:Int) b m) caller
        (work+normalizationWork b m 25) base finalPeak,none,false⟩ ∧
      finalPeak ≤ max peak (caller.length+26-base) := by
  have evaluated := guard_at n m a b ans b caller work base peak 3
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv hb rfl
  have advanced : ({mainState n m a b ans caller work base peak with work := (mainState n m a b ans caller work base peak).work+4+1}).observe 4 =
      mainState n m a b ans caller (work+5) base (max peak (caller.length+5-base+9)) := by
    simp [mainState,State.observe,Nat.add_assoc]
  have branch := branch_step 14 (guardExpression 3) (negativeBody bCorrectionExpression 3)
    .skip (mainState n m a b ans caller work base peak) _ evaluated
  have nodes : (guardExpression 3).nodes = 4 := rfl
  simp only [nodes,advanced] at branch
  by_cases negative : b < 0
  · obtain ⟨finalPeak,body,bound⟩ := b_negative_body n m a b ans caller (work+5) base
      (max peak (caller.length+5-base+9)) allocated hn hm positive ha hb negative hv
    refine ⟨finalPeak,?_,?_⟩
    · simpa [normalizationBranch,negative,normalizedCoefficient,correctedAns,normalizationWork,body,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using branch
    · omega
  · refine ⟨max peak (caller.length+5-base+9),?_,?_⟩
    · simpa [normalizationBranch,negative,normalizedCoefficient,correctedAns,normalizationWork,skip_succeeds] using branch
    · omega

theorem normalizedCoefficient_nonnegative (x : Int) (m : Nat) (positive : 0 < m) :
    0 ≤ normalizedCoefficient x m := by
  simp only [normalizedCoefficient]
  split
  · exact Int.emod_nonneg x (by omega)
  · omega

theorem normalizationWork_bound (x : Int) (m : Nat) (overhead : Nat) :
    normalizationWork x m overhead ≤ overhead+20 := by
  have bounded := Proofs.SafeModFrame.bodyWork_bound x m
  simp only [normalizationWork]
  split <;> omega


theorem normalizedCoefficient_valid (x : Int) (m : Nat) (hx : signed64.valid x = true)
    (hm : m < inputLimit) (positive : 0 < m) : signed64.valid (normalizedCoefficient x m) = true := by
  simp only [normalizedCoefficient]
  split
  · exact normalized_signed_valid x m hm positive
  · exact hx

theorem correctedAns_valid (ans factor x : Int) (m : Nat) (hv : unsigned64.valid ans = true) :
    unsigned64.valid (correctedAns ans factor x m) = true := by
  simp only [correctedAns]
  split
  · exact unsigned_mod_valid _
  · exact hv

def normalizationSequence : Stmt := .sequence (normalizationBranch aCorrectionExpression 2)
  (.sequence (normalizationBranch bCorrectionExpression 3) .skip)

theorem both_normalizations (n m : Nat) (a b ans : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true) (hv : unsigned64.valid ans = true) :
    ∃ finalPeak,
      runFuel 17 normalizationSequence (mainState n m a b ans caller work base peak) =
      .finished ⟨mainState n m (normalizedCoefficient a m) (normalizedCoefficient b m)
        (correctedAns (correctedAns ans (triangle n:Int) a m) (n:Int) b m) caller
        (work+normalizationWork a m 34+normalizationWork b m 25) base finalPeak,none,false⟩ ∧
      finalPeak ≤ max peak (caller.length+35-base) ∧
      normalizationWork a m 34+normalizationWork b m 25 ≤ 99 ∧
      0 ≤ normalizedCoefficient a m ∧ 0 ≤ normalizedCoefficient b m := by
  obtain ⟨firstPeak,first,firstBound⟩ := a_normalization_branch n m a b ans caller work base peak
    allocated hn hm positive ha hb hv
  obtain ⟨lastPeak,last,lastBound⟩ := b_normalization_branch n m (normalizedCoefficient a m) b
    (correctedAns ans (triangle n:Int) a m) caller (work+normalizationWork a m 34) base firstPeak
    allocated hn hm positive (normalizedCoefficient_valid a m ha hm positive) hb (correctedAns_valid _ _ _ _ hv)
  have padded := runFuel_success_mono 15 1 _ _ _ first
  have rest := sequence_done 15 _ .skip _ _ _ last rfl
  have combined := sequence_done 16 _ _ _ _ _ padded rest
  refine ⟨lastPeak,?_,?_,?_,normalizedCoefficient_nonnegative a m positive,normalizedCoefficient_nonnegative b m positive⟩
  · exact combined
  · omega
  · have boundA := normalizationWork_bound a m 34
    have boundB := normalizationWork_bound b m 25
    omega

end Proofs.FloorSumSignedBranch
