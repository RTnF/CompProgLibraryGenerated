import Proofs.Generated.BitWidthU64

namespace Proofs.BitWidthU64
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop

def u64 : Ty := ⟨64,false,false⟩
def i32 : Ty := ⟨32,true,false⟩
def width (n : Nat) : Nat := if n = 0 then 0 else n.log2+1

theorem width_zero : width 0 = 0 := rfl

theorem width_halve (n : Nat) (positive : 0 < n) :
    width n = width (n/2)+1 := by
  by_cases large : 2 ≤ n
  · have quotient : n/2 ≠ 0 := by omega
    have nonzero : n ≠ 0 := by omega
    simp only [width,nonzero,quotient,ite_false]
    rw [Nat.log2_def n,ite_eq_left large]
  · have one : n = 1 := by omega
    subst n
    rfl

theorem width_bound (n : Nat) (bound : n < 2^64) : width n ≤ 64 := by
  by_cases zero : n = 0
  · simp [width,zero]
  · have logBound := (Nat.log2_lt zero).2 bound
    simp only [width,zero,ite_false]
    omega

theorem width_characterization (n : Nat) :
    n < 2^(width n) ∧ (0 < n → 2^(width n-1) ≤ n) := by
  by_cases zero : n = 0
  · subst n
    simp [width_zero]
  · have upper := Nat.lt_log2_self (n := n)
    have lower := Nat.log2_self_le zero
    simp only [width,zero,ite_false,Nat.add_sub_cancel]
    exact ⟨upper,fun _ => lower⟩

def condition : Expr :=
  .binary ⟨1,false,true⟩ .ne (.variable u64 0) (.cast u64 (.literal i32 0))
def increment : Stmt :=
  .assign 1 (.binary i32 .add (.variable i32 1) (.literal i32 1))
def halve : Stmt :=
  .assign 0 (.divrem u64 false (.variable u64 0) (.cast u64 (.literal i32 2)))
def iteration : Stmt := .scope (.scope (.sequence increment (.sequence halve .skip)))
def loop : Stmt := .whileLoop condition iteration

theorem generated_shape : BitWidthU64Instance.bit_width_u64.body =
    .scope (.sequence (.sequence (.declare i32 true (.literal i32 0)) .skip)
      (.sequence loop (.sequence (.ret (.variable i32 1)) .skip))) := rfl

def frame (n count : Int) (caller : List Cell) (work peak : Nat) : State :=
  ⟨caller ++ [⟨u64,n⟩,⟨i32,count⟩], [⟨caller.length,true⟩,⟨caller.length+1,true⟩],
    work,caller.length,peak⟩

theorem u64_valid (n : Nat) (bound : n < 2^64) : u64.valid n = true := by
  simp [u64,Ty.valid] at *
  omega

theorem i32_valid (n : Nat) (bound : n ≤ 64) : i32.valid n = true := by
  simp [i32,Ty.valid] at *
  omega

theorem environment (n count : Int) (caller : List Cell) (work peak : Nat)
    (nv : u64.valid n = true) (cv : i32.valid count = true) :
    (frame n count caller work peak).environment = some [n,count] := by
  have offset : ¬caller.length+1 < caller.length := by omega
  simp [frame,State.environment,List.getElem?_append,nv,cv,offset]

theorem condition_evaluates (n count : Int) (caller : List Cell) (work peak : Nat)
    (hn : u64.valid n = true) (hc : i32.valid count = true) :
    (frame n count caller work peak).evaluate condition =
      some ⟨if n = 0 then 0 else 1,4⟩ := by
  have env := environment n count caller work peak hn hc
  have zeroLit : i32.valid 0 = true := by decide
  have zeroCast : u64.convert 0 = some 0 := by decide
  have validZero : u64.valid 0 = true := by decide
  have boolZero : (⟨1,false,true⟩:Ty).convert 0 = some 0 := rfl
  have boolOne : (⟨1,false,true⟩:Ty).convert 1 = some 1 := rfl
  rw [State.evaluate,env]
  by_cases zero : n = 0
  · simp [condition,Expr.eval,validZero,zeroLit,zeroCast,binaryValue,zero,boolZero]
  · simp [condition,Expr.eval,hn,zeroLit,zeroCast,binaryValue,zero,boolOne]

theorem increment_runs (n count : Int) (caller : List Cell) (work peak : Nat)
    (hn : u64.valid n = true) (hc : i32.valid count = true)
    (next : i32.valid (count+1) = true) :
    increment.run (frame n count caller work peak) =
      some ⟨frame n (count+1) caller (work+4) (max peak 7),none,false⟩ := by
  have env := environment n count caller work peak hn hc
  have conv := Ty.convert_of_valid i32 _ next
  have one : i32.valid 1 = true := by decide
  have eval : (frame n count caller work peak).evaluate
      (.binary i32 .add (.variable i32 1) (.literal i32 1)) = some ⟨count+1,3⟩ := by
    simp [State.evaluate,env,Expr.eval,hc,binaryValue,one,conv]
  have offset : ¬caller.length+1 < caller.length := by omega
  simp only [increment,Stmt.run]
  simp only [frame] at eval
  simp [eval,frame,conv,State.observe,Expr.nodes,List.getElem?_append,
    List.set_append_right,offset]

theorem halve_runs (n count : Int) (caller : List Cell) (work peak : Nat)
    (hn : u64.valid n = true) (hc : i32.valid count = true)
    (quotient : u64.valid (n.tdiv 2) = true) :
    halve.run (frame n count caller work peak) =
      some ⟨frame (n.tdiv 2) count caller (work+5) (max peak 8),none,false⟩ := by
  have env := environment n count caller work peak hn hc
  have div := checkedDivRem_division_exact u64 n 2 (by decide) quotient
  have conv := Ty.convert_of_valid u64 _ quotient
  have cast : u64.convert 2 = some 2 := by decide
  have lit : i32.valid 2 = true := by decide
  have eval : (frame n count caller work peak).evaluate
      (.divrem u64 false (.variable u64 0) (.cast u64 (.literal i32 2))) =
      some ⟨n.tdiv 2,4⟩ := by
    simp [State.evaluate,env,Expr.eval,hn,lit,cast,div]
  simp only [halve,Stmt.run]
  simp only [frame] at eval
  simp [eval,conv,frame,State.observe,Expr.nodes,List.getElem?_append,List.set_append_right]

theorem iteration_runs (fuel : Nat) (n count : Int) (caller : List Cell) (work peak : Nat)
    (hn : u64.valid n = true) (hc : i32.valid count = true)
    (next : i32.valid (count+1) = true) (quotient : u64.valid (n.tdiv 2) = true) :
    runFuel (fuel+5) iteration (frame n count caller work peak) =
      .finished ⟨frame (n.tdiv 2) (count+1) caller (work+9) (max peak 8),none,false⟩ := by
  have hi : runFuel (fuel+2) increment (frame n count caller work peak) =
      .finished ⟨frame n (count+1) caller (work+4) (max peak 7),none,false⟩ := by
    change liftChecked (increment.run _) = _
    rw [increment_runs n count caller work peak hn hc next]
    rfl
  have hh : runFuel (fuel+1) halve (frame n (count+1) caller (work+4) (max peak 7)) =
      .finished ⟨frame (n.tdiv 2) (count+1) caller (work+9) (max peak 8),none,false⟩ := by
    change liftChecked (halve.run _) = _
    rw [halve_runs n (count+1) caller (work+4) (max peak 7) hn next quotient]
    simp [liftChecked,Nat.add_assoc,Nat.max_assoc]
  rw [iteration,runFuel,runFuel,runFuel,hi]
  simp only [bind,Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false]
  rw [runFuel,hh]
  simp only [bind,Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false]
  have takeMemory : (caller ++ [Cell.mk u64 (n.tdiv 2),Cell.mk i32 (count+1)]).take (caller.length+2) =
      caller ++ [Cell.mk u64 (n.tdiv 2),Cell.mk i32 (count+1)] := List.take_of_length_le (by simp)
  simp [runFuel,Stmt.run,liftChecked,pure,frame,takeMemory]

theorem loop_correct (n count : Nat) (caller : List Cell) (work peak : Nat)
    (hn : n < 2^64) (hc : count+width n ≤ 64) :
    runFuel (width n+6) loop (frame n count caller work peak) =
      .finished ⟨frame 0 (count+width n) caller (work+14*width n+5) (max peak 8),none,false⟩ := by
  induction n using Nat.strongRecOn generalizing count work peak with
  | ind n ih =>
      have cv := i32_valid count (by omega)
      have nv := u64_valid n hn
      have evaluated := condition_evaluates n count caller work peak nv cv
      have observation : ({frame n count caller work peak with work := (frame n count caller work peak).work+4+1}).observe condition.nodes =
          frame n count caller (work+5) (max peak 8) := by
        simp [frame,State.observe,condition,Expr.nodes,Nat.add_assoc]
      by_cases zero : n = 0
      · subst n
        have evaluatedZero : (frame 0 count caller work peak).evaluate condition = some ⟨0,4⟩ := by
          simpa using evaluated
        simp only [Int.natCast_zero] at observation
        change runFuel 6 (.whileLoop condition iteration) (frame 0 count caller work peak) = _
        rw [runFuel,evaluatedZero]
        simp [observation,liftChecked,bind,pure,Outcome.bind,width_zero]
      · have positive : 0 < n := by omega
        have decrease : n/2 < n := Nat.div_lt_self positive (by decide)
        have quotientBound : n/2 < 2^64 := by omega
        have widths := width_halve n positive
        have nextBound : count+1+width (n/2) ≤ 64 := by omega
        have quotient : (n:Int).tdiv 2 = ((n/2:Nat):Int) := by simp
        have qv : u64.valid ((n:Int).tdiv 2) = true := by
          rw [quotient]
          exact u64_valid (n/2) quotientBound
        have next : i32.valid ((count:Int)+1) = true := by
          have valid := i32_valid (count+1) (by omega)
          simpa using valid
        have body := iteration_runs (width (n/2)+1) n count caller (work+5) (max peak 8) nv cv next qv
        have tail := ih (n/2) decrease (count+1) (work+14) (max peak 8) quotientBound nextBound
        have budget : width n+6 = (width (n/2)+6)+1 := by omega
        have nonzero : (n:Int) ≠ 0 := by omega
        rw [budget,loop,runFuel]
        simp only [evaluated,nonzero,ite_false,liftChecked,bind,Outcome.bind,
          beq_iff_eq,Int.one_ne_zero]
        rw [observation]
        have body' : runFuel (width (n/2)+6) iteration (frame n count caller (work+5) (max peak 8)) =
            .finished ⟨frame (n/2:Nat) (count+1) caller (work+14) (max peak 8),none,false⟩ := by
          simpa [quotient,Nat.add_assoc] using body
        rw [body']
        simp only [Option.isSome_none,Bool.false_eq_true,ite_false]
        change runFuel (width (n/2)+6) loop (frame (n/2:Nat) (count+1) caller (work+14) (max peak 8)) = _
        simp only [Int.natCast_add,Int.natCast_one] at tail
        rw [tail]
        have countEq : (count:Int)+1+(width (n/2):Int) = (count:Int)+(width n:Int) := by
          rw [widths]
          simp only [Int.natCast_add,Int.natCast_one]
          omega
        have workEq : work+14+14*width (n/2)+5 = work+14*width n+5 := by omega
        simp only [countEq,workEq,Nat.max_assoc,Nat.max_self]

def parameterFrame (n : Int) (caller : List Cell) (work peak : Nat) : State :=
  ⟨caller ++ [⟨u64,n⟩],[⟨caller.length,true⟩],work,caller.length,peak⟩

def initResult : Stmt := .sequence (.declare i32 true (.literal i32 0)) .skip
def returnResult : Stmt := .sequence (.ret (.variable i32 1)) .skip

theorem initResult_runs (fuel : Nat) (n : Int) (caller : List Cell)
    (hn : u64.valid n = true) :
    runFuel (fuel+2) initResult (parameterFrame n caller 0 2) =
      .finished ⟨frame n 0 caller 2 5,none,false⟩ := by
  have env : (parameterFrame n caller 0 2).environment = some [n] := by
    simp [parameterFrame,State.environment,List.getElem?_append,hn]
  have evaluated : (parameterFrame n caller 0 2).evaluate (.literal i32 0) = some ⟨0,1⟩ := by
    simp [State.evaluate,env,Expr.eval,i32,Ty.valid]
  simp only [initResult,runFuel]
  simp only [parameterFrame] at evaluated
  have convertZero : i32.convert 0 = some 0 := by decide
  simp [Stmt.run,evaluated,convertZero,liftChecked,bind,Outcome.bind,
    parameterFrame,frame,State.observe,Expr.nodes,List.append_assoc]

theorem return_runs (fuel : Nat) (n count : Int) (caller : List Cell) (work peak : Nat)
    (hn : u64.valid n = true) (hc : i32.valid count = true) :
    runFuel (fuel+2) returnResult (frame n count caller work peak) =
      .finished ⟨frame n count caller (work+2) (max peak 5),some count,false⟩ := by
  have env := environment n count caller work peak hn hc
  have evaluated : (frame n count caller work peak).evaluate (.variable i32 1) = some ⟨count,1⟩ := by
    simp [State.evaluate,env,Expr.eval,hc]
  rw [returnResult,runFuel]
  have ret : runFuel (fuel+1) (.ret (.variable i32 1)) (frame n count caller work peak) =
      .finished ⟨frame n count caller (work+2) (max peak 5),some count,false⟩ := by
    change liftChecked (Stmt.run _ _) = _
    rw [Stmt.run,evaluated]
    simp [frame,liftChecked,State.observe,Expr.nodes]
  rw [ret]
  rfl

theorem body_correct (n : Nat) (caller : List Cell) (hn : n < 2^64) :
    runFuel (width n+10) BitWidthU64Instance.bit_width_u64.body (parameterFrame n caller 0 2) =
      .finished ⟨parameterFrame 0 caller (9+14*width n) 8,some (width n),false⟩ := by
  have wb := width_bound n hn
  have nv := u64_valid n hn
  have cv := i32_valid (width n) wb
  have first := initResult_runs (width n+6) n caller nv
  have middle := loop_correct n 0 caller 2 5 hn (by omega)
  have larger := runFuel_success_mono (width n+6) 1 loop _ _ middle
  have middle' : runFuel (width n+7) loop (frame n 0 caller 2 5) =
      .finished ⟨frame 0 (width n) caller (7+14*width n) 8,none,false⟩ := by
    have costs : 2+14*width n+5 = 7+14*width n := by omega
    simpa [Nat.add_assoc,costs] using larger
  have last := return_runs (width n+5) 0 (width n) caller (7+14*width n) 8 (u64_valid 0 (by decide)) cv
  rw [generated_shape]
  change runFuel (width n+10) (.scope (.sequence initResult (.sequence loop returnResult))) _ = _
  rw [runFuel,runFuel,first]
  simp only [bind,Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false]
  rw [runFuel,middle']
  simp only [bind,Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false]
  rw [last]
  have cost : 7+14*width n+2 = 9+14*width n := by omega
  have takeMemory : (caller ++ [Cell.mk u64 0,Cell.mk i32 (width n)]).take (caller.length+1) =
      caller ++ [Cell.mk u64 0] := by simp [List.take_append,List.take_of_length_le]
  simp [pure,frame,parameterFrame,takeMemory,cost]

theorem call_correct (n : Nat) (caller : List Cell) (hn : n < 2^64) :
    BitWidthU64Instance.bit_width_u64.callFuel (width n+10) caller [.value n] =
      .finished ⟨width n,caller,9+14*width n,8⟩ := by
  have nv := u64_valid n hn
  have cv := i32_valid (width n) (width_bound n hn)
  have parameters : BitWidthU64Instance.bit_width_u64.parameters = [⟨u64,false,true⟩] := rfl
  have resultType : BitWidthU64Instance.bit_width_u64.resultType = i32 := rfl
  have bound : bindArguments {memory := caller,bindings := [],baseMemory := caller.length}
      [⟨u64,false,true⟩] [.value n] = some (parameterFrame n caller 0 2) := by
    simp [bindArguments,bindArgument,nv,parameterFrame,State.observe]
  have body := body_correct n caller hn
  simp only [LoopProgram.callFuel,parameters,List.all_cons,List.all_nil,Bool.and_true,
    Bool.not_true,Bool.false_eq_true,ite_false]
  rw [bound]
  simp only [liftChecked,bind,Outcome.bind]
  rw [body]
  simp [resultType,cv,pure,parameterFrame]

theorem call_uniform (n : Nat) (caller : List Cell) (hn : n < 2^64) :
    BitWidthU64Instance.bit_width_u64.callFuel 80 caller [.value n] =
      .finished ⟨width n,caller,9+14*width n,8⟩ := by
  have wb := width_bound n hn
  have budget : width n+10+(80-(width n+10)) = 80 := by omega
  have larger := LoopProgram.callFuel_success_mono _ (width n+10) (80-(width n+10))
    caller [.value n] _ (call_correct n caller hn)
  rw [budget] at larger
  exact larger

theorem call_bounds (n : Nat) (caller : List Cell) (hn : n < 2^64) :
    ∃ result, BitWidthU64Instance.bit_width_u64.callFuel 80 caller [.value n] = .finished result ∧
      result.value = (width n:Int) ∧ result.memory = caller ∧ result.work ≤ 905 ∧ result.peak = 8 := by
  refine ⟨_,call_uniform n caller hn,rfl,rfl,?_,rfl⟩
  have bound := width_bound n hn
  dsimp
  omega

end Proofs.BitWidthU64
