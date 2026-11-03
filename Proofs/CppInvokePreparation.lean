import Proofs.CppInvokeProofs

namespace Proofs.CppInvokePreparation
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop

def copiedCells (parameters : List (Ty × Bool)) (values : List Result) : List Cell :=
  (parameters.zip values).map fun (p,v) => ⟨p.1,v.value⟩

def copiedBindings (base : Nat) : List (Ty × Bool) → List Binding
  | [] => []
  | p :: ps => ⟨base,p.2⟩ :: copiedBindings (base+1) ps

theorem bind_results_shape (parameters : List (Ty × Bool)) (values : List Result)
    (s result : State) (success : bindValueResults s parameters values = some result) :
    parameters.length = values.length ∧
    result.memory = s.memory ++ copiedCells parameters values ∧
    result.bindings = s.bindings ++ copiedBindings s.memory.length parameters ∧
    result.baseMemory = s.baseMemory ∧
    result.work = s.work + (values.map (·.work)).sum + parameters.length ∧
    result.memory.length = s.memory.length + parameters.length ∧
    result.bindings.length = s.bindings.length + parameters.length ∧
    result.peak = if parameters.isEmpty then s.peak else
      max s.peak (result.memory.length-s.baseMemory+result.bindings.length) := by
  induction parameters generalizing values s result with
  | nil =>
    cases values with
    | nil =>
      simp [bindValueResults] at success
      cases success
      simp [copiedCells,copiedBindings]
    | cons v vs => simp [bindValueResults] at success
  | cons p ps ih =>
    cases values with
    | nil => simp [bindValueResults] at success
    | cons v vs =>
      by_cases valid : p.1.valid v.value = true
      · let next : State := ({s with
          memory := s.memory ++ [⟨p.1,v.value⟩],
          bindings := s.bindings ++ [⟨s.memory.length,p.2⟩],
          work := s.work+v.work+1} : State).observe 0
        have recurse : bindValueResults next ps vs = some result := by
          simpa [bindValueResults,valid,next] using success
        obtain ⟨count,mem,bindings,base,work,mlen,blen,peak⟩ := ih vs next result recurse
        refine ⟨by simp [count],?_,?_,?_,?_,?_,?_,?_⟩
        · simpa [next,State.observe,copiedCells,List.append_assoc] using mem
        · simpa [next,State.observe,copiedBindings,List.append_assoc,Nat.add_assoc] using bindings
        · simpa [next,State.observe] using base
        · simp only [List.map_cons,List.sum_cons,List.length_cons]
          simpa [next,State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using work
        · simpa [next,State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using mlen
        · simpa [next,State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using blen
        · simp only [List.isEmpty_cons, Bool.false_eq_true,ite_false]
          cases ps with
          | nil =>
            simp [next,State.observe] at peak mlen blen
            rw [peak]
            congr 1
            omega
          | cons q qs =>
            simp [next,State.observe] at peak mlen blen
            rw [peak]
            have monotone : s.memory.length+1-s.baseMemory+s.bindings.length+1 ≤
                result.memory.length-s.baseMemory+result.bindings.length := by omega
            omega
      · simp [bindValueResults,valid] at success



theorem bind_results_succeeds (parameters : List (Ty × Bool)) (values : List Result) (s : State)
    (count : parameters.length = values.length)
    (valid : (parameters.zip values).all (fun (p,v) => p.1.valid v.value) = true) :
    ∃ result, bindValueResults s parameters values = some result := by
  induction parameters generalizing values s with
  | nil =>
    cases values with
    | nil => exact ⟨s,rfl⟩
    | cons v vs => simp at count
  | cons p ps ih =>
    cases values with
    | nil => simp at count
    | cons v vs =>
      have tailCount : ps.length = vs.length := by simpa using count
      have accepted : p.1.valid v.value = true ∧
          (ps.zip vs).all (fun (p,v) => p.1.valid v.value) = true := by simpa using valid
      obtain ⟨result,done⟩ := ih vs _ tailCount accepted.2
      refine ⟨result,?_⟩
      simpa [bindValueResults,accepted.1] using done

theorem evaluate_work (s : State) (e : Expr) (value : Result)
    (success : s.evaluate e = some value) : value.work = e.nodes := by
  cases env : s.environment with
  | none => simp [State.evaluate,env] at success
  | some values =>
    simp only [State.evaluate,env] at success
    exact Expr.eval_work e values value success

theorem evaluated_arguments (s : State) (arguments : List Expr) (values : List Result)
    (success : arguments.mapM s.evaluate = some values) :
    values.length = arguments.length ∧
    (values.map (·.work)).sum = (arguments.map Expr.nodes).sum := by
  induction arguments generalizing values with
  | nil =>
    simp at success
    cases success
    simp
  | cons e es ih =>
    cases first : s.evaluate e with
    | none => simp [List.mapM_cons,first] at success
    | some v =>
      cases rest : es.mapM s.evaluate with
      | none => simp [List.mapM_cons,first,rest] at success
      | some vs =>
        simp [List.mapM_cons,first,rest] at success
        cases success
        obtain ⟨count,work⟩ := ih vs rest
        simp [count,work,evaluate_work s e v first]


def callerPrefix (s : State) : List Cell :=
  s.memory ++ List.replicate s.bindings.length ⟨⟨1,false,true⟩,0⟩

def argumentPeak (s : State) (arguments : List Expr) : Nat :=
  arguments.foldl (fun peak e => max peak ((s.observe (arguments.length+e.nodes)).peak)) s.peak

theorem prepare_shape (s : State) (parameters : List (Ty × Bool)) (arguments : List Expr)
    (result : State) (success : prepareInvoke s parameters arguments = some result) :
    ∃ values : List Result,
      arguments.mapM s.evaluate = some values ∧
      parameters.length = arguments.length ∧
      result.memory = callerPrefix s ++ copiedCells parameters values ∧
      result.bindings = copiedBindings (callerPrefix s).length parameters ∧
      result.baseMemory = s.baseMemory ∧
      result.work = s.work+1+(arguments.map Expr.nodes).sum+parameters.length ∧
      result.peak = max (argumentPeak s arguments)
        ((callerPrefix s).length+parameters.length-s.baseMemory+parameters.length) := by
  cases evaluated : arguments.mapM s.evaluate with
  | none => simp [prepareInvoke,evaluated] at success
  | some values =>
    let initial : State := ({s with
      memory := callerPrefix s,bindings := [],
      work := s.work+1,peak := argumentPeak s arguments} : State).observe 0
    have bound : bindValueResults initial parameters values = some result := by
      simpa [prepareInvoke,evaluated,initial,callerPrefix,argumentPeak] using success
    obtain ⟨counts,mem,bindings,base,work,mlen,blen,peak⟩ := bind_results_shape parameters values initial result bound
    obtain ⟨valueCount,valueWork⟩ := evaluated_arguments s arguments values evaluated
    refine ⟨values,rfl,by omega,?_,?_,?_,?_,?_⟩
    · simpa [initial,State.observe] using mem
    · simpa [initial,State.observe] using bindings
    · simpa [initial,State.observe] using base
    · simpa [initial,State.observe,valueWork,Nat.add_assoc] using work
    · cases parameters with
      | nil =>
        simp [initial,State.observe] at peak
        simpa using peak
      | cons p ps =>
        simp [initial,State.observe] at peak mlen blen
        rw [peak]
        have monotone : (callerPrefix s).length-s.baseMemory ≤
            result.memory.length-s.baseMemory+result.bindings.length := by omega
        have storage : result.memory.length-s.baseMemory+result.bindings.length =
            (callerPrefix s).length+(p::ps).length-s.baseMemory+(p::ps).length := by simp; omega
        rw [← storage]
        omega


theorem prepare_of_evaluated (s : State) (parameters : List (Ty × Bool))
    (arguments : List Expr) (values : List Result)
    (evaluated : arguments.mapM s.evaluate = some values)
    (count : parameters.length = values.length)
    (valid : (parameters.zip values).all (fun (p,v) => p.1.valid v.value) = true) :
    ∃ result, prepareInvoke s parameters arguments = some result := by
  obtain ⟨result,bound⟩ := bind_results_succeeds parameters values
    (({s with
      memory := callerPrefix s,bindings := [],work := s.work+1,
      peak := argumentPeak s arguments} : State).observe 0) count valid
  refine ⟨result,?_⟩
  simpa [prepareInvoke,evaluated,callerPrefix,argumentPeak] using bound


theorem invoke_composed (fuel : Nat) (s callee : State) (parameters : List (Ty × Bool))
    (ty : Ty) (arguments : List Expr) (body : Stmt) (step : Step) (value : Int) (bodyWork : Nat)
    (prepared : prepareInvoke s parameters arguments = some callee)
    (completed : runFuel fuel body callee = .finished step)
    (returned : step.returned = some value) (breaking : step.breaking = false)
    (valid : ty.valid value = true) (body_work : step.state.work = callee.work+bodyWork) :
    runFuel (fuel+1) (.invoke parameters ty arguments body) s = .finished
      ⟨({s with
        memory := s.memory ++ [⟨ty,value⟩],
        bindings := s.bindings ++ [⟨s.memory.length,false⟩],
        work := s.work+(arguments.map Expr.nodes).sum+parameters.length+bodyWork+2,
        peak := max s.peak step.state.peak} : State).observe 0,none,false⟩ := by
  obtain ⟨values,evaluated,count,mem,bindings,base,work,peak⟩ := prepare_shape s parameters arguments callee prepared
  have total : step.state.work+1 = s.work+(arguments.map Expr.nodes).sum+parameters.length+bodyWork+2 := by
    rw [body_work,work]
    omega
  have shape : step = ⟨step.state,some value,false⟩ := by
    cases step
    simp_all
  rw [CppInvokeProofs.invoke_fuel fuel s callee parameters ty arguments body step prepared completed]
  rw [shape,CppInvokeProofs.finish_result s ty _ value valid]
  simp only [liftChecked]
  simp only [total]

end Proofs.CppInvokePreparation
