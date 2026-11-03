import Proofs.FloorSumSignedPrefix
import Proofs.FloorSumInvoke

namespace Proofs.FloorSumSignedReturn
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppInvokePreparation
open Proofs.SafeModProofs Proofs.FloorSumArithmetic Proofs.FloorSumState
open Proofs.FloorSumSignedBranch Proofs.FloorSumSignedState Proofs.FloorSumSignedCorrection
open Proofs.FloorSumSignedArithmetic

def unsignedArguments : List Expr :=
  [.cast unsigned64 (.variable signed64 0),.cast unsigned64 (.variable signed64 1),
   .cast unsigned64 (.variable signed64 2),.cast unsigned64 (.variable signed64 3)]

def resultState (n m a b ans result : Int) (caller : List Cell) (work base peak : Nat) : State :=
  {mainState n m a b ans caller work base peak with
    memory := (mainState n m a b ans caller work base peak).memory ++ [⟨unsigned64,result⟩],
    bindings := (mainState n m a b ans caller work base peak).bindings ++ [⟨caller.length+5,false⟩]}

theorem signed_unsigned_bound (a : Int) (valid : signed64.valid a = true) : a < (wordLimit:Int) := by
  have bounds : -9223372036854775808 ≤ a ∧ a < 9223372036854775808 := of_decide_eq_true valid
  change a < 18446744073709551616
  omega

theorem natural_unsigned_bound (a : Nat) (valid : signed64.valid (a:Int) = true) : a < wordLimit := by
  have bound := signed_unsigned_bound a valid
  exact_mod_cast bound

theorem arguments_eval_checked (n m a b : Int) (env : List Int)
    (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true)
    (sn : env[0]? = some n) (sm : env[1]? = some m) (sa : env[2]? = some a) (sb : env[3]? = some b)
    (cn : unsigned64.convert n = some n) (cm : unsigned64.convert m = some m)
    (ca : unsigned64.convert a = some a) (cb : unsigned64.convert b = some b) :
    unsignedArguments.mapM (Expr.eval env) = some [⟨n,2⟩,⟨m,2⟩,⟨a,2⟩,⟨b,2⟩] := by
  simp [unsignedArguments,Expr.eval,hn,hm,ha,hb,sn,sm,sa,sb,cn,cm,ca,cb]

theorem unsigned_arguments_eval (n m a b : Nat) (env : List Int)
    (hn : signed64.valid (n:Int) = true) (hm : signed64.valid (m:Int) = true)
    (ha : signed64.valid (a:Int) = true) (hb : signed64.valid (b:Int) = true)
    (sn : env[0]? = some (n:Int)) (sm : env[1]? = some (m:Int))
    (sa : env[2]? = some (a:Int)) (sb : env[3]? = some (b:Int)) :
    unsignedArguments.mapM (Expr.eval env) = some [⟨n,2⟩,⟨m,2⟩,⟨a,2⟩,⟨b,2⟩] :=
  arguments_eval_checked n m a b env hn hm ha hb sn sm sa sb
    (Ty.convert_of_valid unsigned64 n (unsigned64_valid n (natural_unsigned_bound n hn)))
    (Ty.convert_of_valid unsigned64 m (unsigned64_valid m (natural_unsigned_bound m hm)))
    (Ty.convert_of_valid unsigned64 a (unsigned64_valid a (natural_unsigned_bound a ha)))
    (Ty.convert_of_valid unsigned64 b (unsigned64_valid b (natural_unsigned_bound b hb)))

def unsignedCall : Stmt := .invoke Proofs.FloorSumInvoke.valueParameters unsigned64 unsignedArguments
  FloorSumUnsignedInstance.floor_sum_unsigned.body

theorem invoke_unsigned (n m a b : Nat) (ans : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid (a:Int) = true) (hb : signed64.valid (b:Int) = true)
    (hv : unsigned64.valid ans = true) :
    ∃ bodyWork nextPeak,
      runFuel 837 unsignedCall (mainState n m a b ans caller work base peak) =
      .finished ⟨resultState n m a b ans (directSum m a b n%wordLimit : Nat) caller
        (work+bodyWork+14) base nextPeak,none,false⟩ ∧
      bodyWork ≤ 4229 ∧ nextPeak ≤ max peak (caller.length+35-base) ∧
      bodyWork ≤ 5+132*(m.log2+1) := by
  have env := main_environment n m a b ans caller work base peak
    (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv
  have evaluated : unsignedArguments.mapM (mainState n m a b ans caller work base peak).evaluate =
      some [⟨n,2⟩,⟨m,2⟩,⟨a,2⟩,⟨b,2⟩] := by
    have evaluation : (mainState n m a b ans caller work base peak).evaluate = Expr.eval [(n:Int),(m:Int),(a:Int),(b:Int),ans] := by
      funext e
      simp [State.evaluate,env]
    rw [evaluation]
    exact unsigned_arguments_eval n m a b _ (input_signed_valid n hn) (input_signed_valid m hm) ha hb rfl rfl rfl rfl
  obtain ⟨bodyWork,nextPeak,done,workBound,peakBound,logBound⟩ := Proofs.FloorSumInvoke.invoke_correct
    (mainState n m a b ans caller work base peak) unsignedArguments n m a b 2 2 2 2 evaluated
    (by simp [mainState]; omega) hn hm positive (natural_unsigned_bound a ha) (natural_unsigned_bound b hb)
  refine ⟨bodyWork,nextPeak,?_,workBound,?_,logBound⟩
  · have total : 8+(bodyWork+6) = bodyWork+14 := by omega
    simpa [unsignedCall,resultState,mainState,unsignedArguments,Expr.nodes,List.append_assoc,Nat.add_assoc,total] using done
  · simp [mainState,callerPrefix,argumentPeak,unsignedArguments,Expr.nodes,State.observe] at peakBound
    omega

def returnExpression : Expr := .targetCast signed64
  (.binary unsigned64 .add (.variable unsigned64 4) (.variable unsigned64 5))

theorem decode64_modulo (value : Int) :
    signedDecode64 (value%(wordLimit:Int)) = signedDecode64 value := by
  simp only [signedDecode64,Int.emod_emod]

theorem decode64_add_modulo (ans value : Int) :
    signedDecode64 (ans+value%(wordLimit:Int)) = signedDecode64 (ans+value) := by
  simp only [signedDecode64,Int.add_emod,Int.emod_emod]

theorem return_eval (env : List Int) (ans result : Int)
    (va : unsigned64.valid ans = true) (vr : unsigned64.valid result = true)
    (sa : env[4]? = some ans) (sr : env[5]? = some result) :
    returnExpression.eval env = some ⟨signedDecode64 (ans+result),4⟩ := by
  have add : unsigned64.convert (ans+result) = some ((ans+result)%(wordLimit:Int)) := rfl
  have cast := (Proofs.CppTargetCast.targetConvert_i64_valid ((ans+result)%(wordLimit:Int))).1
  rw [Proofs.CppTargetCast.decode64_spec] at cast
  change signed64.targetConvert ((ans+result)%(wordLimit:Int)) = _ at cast
  simp [returnExpression,Expr.eval,va,vr,sa,sr,binaryValue,add,cast,decode64_modulo]

theorem return_runs (n m a b ans result : Int) (caller : List Cell) (work base peak : Nat)
    (hn : signed64.valid n = true) (hm : signed64.valid m = true)
    (ha : signed64.valid a = true) (hb : signed64.valid b = true)
    (hv : unsigned64.valid ans = true) (hr : unsigned64.valid result = true) :
    (Stmt.ret returnExpression).run (resultState n m a b ans result caller work base peak) =
      some ⟨resultState n m a b ans result caller (work+5) base
        (max peak (caller.length+6-base+10)),some (signedDecode64 (ans+result)),false⟩ := by
  have outside (i : Nat) : ¬ caller.length+i < caller.length := by omega
  have env : (resultState n m a b ans result caller work base peak).environment = some [n,m,a,b,ans,result] := by
    simp [resultState,mainState,State.environment,List.getElem?_append,List.append_assoc,outside,hn,hm,ha,hb,hv,hr]
  have evaluated := return_eval [n,m,a,b,ans,result] ans result hv hr rfl rfl
  have success : (resultState n m a b ans result caller work base peak).evaluate returnExpression =
      some ⟨signedDecode64 (ans+result),4⟩ := by simpa [State.evaluate,env] using evaluated
  simp only [Stmt.run,success]
  simp [resultState,mainState,State.observe,returnExpression,Expr.nodes,Nat.add_assoc]

-- A returned value stops the enclosing sequence; the trailing skip has no cost.
theorem sequence_returns (fuel : Nat) (first rest : Stmt) (s : State) (step : Step)
    (done : runFuel fuel first s = .finished step) (returned : step.returned.isSome = true) :
    runFuel (fuel+1) (.sequence first rest) s = .finished step := by
  rw [runFuel]
  simp only [done,bind,Outcome.bind,returned,Bool.true_or,ite_true,pure]

def returnSuffix : Stmt := .scope (.sequence unsignedCall (.sequence (.ret returnExpression) .skip))

theorem restore_result (n m a b ans result : Int) (caller : List Cell) (work base peak : Nat) :
    {resultState n m a b ans result caller work base peak with
      memory := (resultState n m a b ans result caller work base peak).memory.take (caller.length+5),
      bindings := (resultState n m a b ans result caller work base peak).bindings.take 5} =
      mainState n m a b ans caller work base peak := by
  have take : caller.take (caller.length+5) = caller := List.take_of_length_le (by omega)
  simp [resultState,mainState,List.append_assoc,List.take_append,take]

theorem suffix_runs (n m a b : Nat) (ans : Int) (caller : List Cell) (work base peak : Nat)
    (allocated : base ≤ caller.length) (hn : n < inputLimit) (hm : m < inputLimit) (positive : 0 < m)
    (ha : signed64.valid (a:Int) = true) (hb : signed64.valid (b:Int) = true)
    (hv : unsigned64.valid ans = true) :
    ∃ bodyWork finalPeak,
      runFuel 839 returnSuffix (mainState n m a b ans caller work base peak) =
      .finished ⟨mainState n m a b ans caller (work+bodyWork+19) base finalPeak,
        some (signedDecode64 (ans+(directSum m a b n:Int))),false⟩ ∧
      bodyWork ≤ 4229 ∧ finalPeak ≤ max peak (caller.length+35-base) ∧
      bodyWork ≤ 5+132*(m.log2+1) := by
  obtain ⟨bodyWork,helperPeak,invoked,workBound,peakBound,logBound⟩ := invoke_unsigned n m a b ans caller work base peak
    allocated hn hm positive ha hb hv
  have returned := return_runs n m a b ans (directSum m a b n%wordLimit : Nat) caller
    (work+bodyWork+14) base helperPeak (input_signed_valid n hn) (input_signed_valid m hm) ha hb hv
    (unsigned64_valid _ (Nat.mod_lt _ (by decide : 0 < wordLimit)))
  have returnedFuel := congrArg liftChecked returned
  change runFuel 836 (.ret returnExpression) _ = .finished _ at returnedFuel
  have returnSequence := sequence_returns 836 _ .skip _ _ returnedFuel rfl
  have called := sequence_done 837 unsignedCall _ _ _ _ invoked returnSequence
  have restored := scope_done 838 _ _ _ called
  have memoryLength : (mainState n m a b ans caller work base peak).memory.length = caller.length+5 := by simp [mainState]
  have bindingLength : (mainState n m a b ans caller work base peak).bindings.length = 5 := rfl
  refine ⟨bodyWork,max helperPeak (caller.length+6-base+10),?_,workBound,?_,logBound⟩
  · simpa only [returnSuffix,memoryLength,bindingLength,restore_result,Nat.add_assoc,Int.natCast_emod,
      decode64_add_modulo] using restored
  · omega

end Proofs.FloorSumSignedReturn
