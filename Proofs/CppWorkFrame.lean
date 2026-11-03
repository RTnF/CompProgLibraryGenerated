import Proofs.CppInvokePreparation

namespace Proofs.CppWorkFrame
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop

-- Existing caller work does not change values, guards, or live storage.
def addWork (s : State) (extra : Nat) : State := {s with work := s.work + extra}
def addStepWork (step : Step) (extra : Nat) : Step :=
  {step with state := addWork step.state extra}

theorem observe_addWork (s : State) (extra temporaries : Nat) :
    (addWork s extra).observe temporaries = addWork (s.observe temporaries) extra := rfl

theorem evaluate_addWork (s : State) (extra : Nat) (e : Expr) :
    (addWork s extra).evaluate e = s.evaluate e := rfl

theorem bindValueResults_addWork (s : State) (extra : Nat)
    (parameters : List (Ty × Bool)) (values : List Result) :
    bindValueResults (addWork s extra) parameters values =
      (bindValueResults s parameters values).map (fun result => addWork result extra) := by
  induction parameters generalizing s values with
  | nil => cases values <;> rfl
  | cons p ps ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [bindValueResults]
          split
          · rfl
          · simpa [addWork,State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
              ih (({s with
                memory := s.memory ++ [⟨p.1,value.value⟩],
                bindings := s.bindings ++ [⟨s.memory.length,p.2⟩],
                work := s.work + value.work + 1} : State).observe 0) values

theorem prepareInvoke_addWork (s : State) (extra : Nat)
    (parameters : List (Ty × Bool)) (arguments : List Expr) :
    prepareInvoke (addWork s extra) parameters arguments =
      (prepareInvoke s parameters arguments).map (fun result => addWork result extra) := by
  have evaluator : (addWork s extra).evaluate = s.evaluate := rfl
  cases evaluated : arguments.mapM s.evaluate with
  | none => simp [prepareInvoke,evaluator,evaluated]
  | some values =>
      simp only [prepareInvoke,evaluator,evaluated,bind,Option.bind]
      have initial :
          ({addWork s extra with
            memory := s.memory ++ List.replicate s.bindings.length ⟨⟨1,false,true⟩,0⟩,
            bindings := [], work := (addWork s extra).work+1,
            peak := arguments.foldl (fun peak e =>
              max peak (((addWork s extra).observe (arguments.length+e.nodes)).peak))
                (addWork s extra).peak} : State).observe 0 =
          addWork (({s with
            memory := s.memory ++ List.replicate s.bindings.length ⟨⟨1,false,true⟩,0⟩,
            bindings := [], work := s.work+1,
            peak := arguments.foldl (fun peak e =>
              max peak ((s.observe (arguments.length+e.nodes)).peak)) s.peak} : State).observe 0)
            extra := by
        simp [addWork,State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      have lifted := bindValueResults_addWork
        (({s with
          memory := s.memory ++ List.replicate s.bindings.length ⟨⟨1,false,true⟩,0⟩,
          bindings := [], work := s.work+1,
          peak := arguments.foldl (fun peak e =>
            max peak ((s.observe (arguments.length+e.nodes)).peak)) s.peak} : State).observe 0)
        extra parameters values
      rw [← initial] at lifted
      exact lifted

theorem finishInvoke_addWork (caller : State) (step : Step) (extra : Nat) (ty : Ty) :
    finishInvoke (addWork caller extra) ty (addStepWork step extra) =
      (finishInvoke caller ty step).map (fun result => addStepWork result extra) := by
  cases step with
  | mk state returned breaking =>
      cases breaking <;> cases returned <;>
        simp [finishInvoke,addStepWork,addWork,State.observe,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      split <;> rfl

theorem memory_addWork (s : State) (extra : Nat) :
    (addWork s extra).memory = s.memory := rfl

theorem bindings_addWork (s : State) (extra : Nat) :
    (addWork s extra).bindings = s.bindings := rfl

theorem run_addWork (stmt : Stmt) (s : State) (extra : Nat) :
    stmt.run (addWork s extra) = (stmt.run s).map (fun step => addStepWork step extra) := by
  induction stmt generalizing s with
  | skip => rfl
  | whileLoop _ _ _ => rfl
  | breakLoop => rfl
  | declare ty writable e =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,evaluate_addWork,he]
      | some result =>
          cases hc : ty.convert result.value <;>
            simp only [Stmt.run,evaluate_addWork,he,hc,bind,Option.bind] <;>
            simp [addWork,addStepWork,State.observe,
              Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | ret e =>
      cases he : s.evaluate e <;>
        simp only [Stmt.run,evaluate_addWork,he,bind,Option.bind] <;>
        simp [addWork,addStepWork,State.observe,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | check e =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,evaluate_addWork,he]
      | some result =>
          by_cases hz : result.value = 0 <;>
            simp only [Stmt.run,evaluate_addWork,he,bind,Option.bind] <;>
            simp [hz,addWork,addStepWork,State.observe,
              Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | assign slot e =>
      cases hb : s.bindings[slot]? with
      | none => simp [Stmt.run,addWork,hb]
      | some binding =>
          cases hc : s.memory[binding.address]? with
          | none => simp [Stmt.run,addWork,hb,hc]
          | some cell =>
              cases he : s.evaluate e with
              | none =>
                  simp only [Stmt.run,evaluate_addWork,memory_addWork,bindings_addWork,hb,hc,he,bind,Option.bind]
                  split <;> rfl
              | some result =>
                  cases hv : cell.type.convert result.value <;>
                    cases hw : binding.writable <;>
                    simp only [Stmt.run,evaluate_addWork,memory_addWork,bindings_addWork,hb,hc,he,hv,hw,bind,Option.bind] <;>
                    simp [addWork,addStepWork,
                      State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | swap left right =>
      cases hl : s.bindings[left]? with
      | none => simp [Stmt.run,addWork,hl]
      | some lhs =>
          cases hr : s.bindings[right]? with
          | none => simp [Stmt.run,addWork,hl,hr]
          | some rhs =>
              cases ha : s.memory[lhs.address]? with
              | none => simp [Stmt.run,addWork,hl,hr,ha]
              | some a =>
                  cases hb : s.memory[rhs.address]? with
                  | none => simp [Stmt.run,addWork,hl,hr,hb]
                  | some b =>
                      simp [Stmt.run,addWork,hl,hr,ha,hb,addStepWork,State.observe,
                        Nat.add_assoc,Nat.add_comm]
                      split <;> (try rfl)
                      split <;> rfl
  | branch e yes no yesIH noIH =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,evaluate_addWork,he]
      | some result =>
          have next : ({addWork s extra with work := (addWork s extra).work+result.work+1} : State).observe e.nodes =
              addWork (({s with work := s.work+result.work+1} : State).observe e.nodes) extra := by
            simp [addWork,State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          simp only [Stmt.run,evaluate_addWork,he,bind,Option.bind]
          rw [next]
          split <;> simp only [yesIH,noIH]
  | sequence first rest firstIH restIH =>
      simp only [Stmt.run,firstIH]
      cases hf : first.run s with
      | none => simp
      | some step =>
          simp only [Option.map_some,bind,Option.bind]
          change (if step.returned.isSome then some (addStepWork step extra)
            else rest.run (addWork step.state extra)) = _
          split <;> simp_all
  | scope body bodyIH =>
      simp only [Stmt.run,bodyIH]
      cases hb : body.run s <;> simp [addStepWork,addWork]
  | invoke parameters ty arguments body bodyIH =>
      simp only [Stmt.run,prepareInvoke_addWork]
      cases hp : prepareInvoke s parameters arguments with
      | none => simp
      | some callee =>
          simp only [Option.map_some,bind,Option.bind,bodyIH]
          cases hb : body.run callee <;> simp [finishInvoke_addWork]

def addOutcomeWork (outcome : Outcome Step) (extra : Nat) : Outcome Step :=
  match outcome with
  | .finished step => .finished (addStepWork step extra)
  | .fault => .fault
  | .exhausted => .exhausted

theorem liftChecked_addWork (value : Option Step) (extra : Nat) :
    liftChecked (value.map (fun step => addStepWork step extra)) =
      addOutcomeWork (liftChecked value) extra := by cases value <;> rfl

theorem runFuel_addWork (fuel : Nat) (stmt : Stmt) (s : State) (extra : Nat) :
    runFuel fuel stmt (addWork s extra) = addOutcomeWork (runFuel fuel stmt s) extra := by
  induction fuel generalizing stmt s with
  | zero => rfl
  | succ fuel ih =>
      cases stmt with
      | skip => rfl
      | declare ty writable e =>
          simpa only [runFuel,run_addWork] using liftChecked_addWork ((Stmt.declare ty writable e).run s) extra
      | assign slot e =>
          simpa only [runFuel,run_addWork] using liftChecked_addWork ((Stmt.assign slot e).run s) extra
      | swap left right =>
          simpa only [runFuel,run_addWork] using liftChecked_addWork ((Stmt.swap left right).run s) extra
      | ret e =>
          simpa only [runFuel,run_addWork] using liftChecked_addWork ((Stmt.ret e).run s) extra
      | check e =>
          simpa only [runFuel,run_addWork] using liftChecked_addWork ((Stmt.check e).run s) extra
      | breakLoop =>
          simp [runFuel,addOutcomeWork,addStepWork,addWork,pure,Nat.add_assoc,Nat.add_comm]
      | scope body =>
          simp only [runFuel,ih]
          cases hb : runFuel fuel body s <;>
            simp [addOutcomeWork,addStepWork,addWork,bind,pure,Outcome.bind]
      | sequence first rest =>
          simp only [runFuel,ih]
          cases hf : runFuel fuel first s with
          | fault => rfl
          | exhausted => rfl
          | finished step =>
              simp only [addOutcomeWork,bind,Outcome.bind]
              change (if step.returned.isSome || step.breaking then
                pure (addStepWork step extra) else runFuel fuel rest (addWork step.state extra)) = _
              split <;> simp_all [addOutcomeWork,pure]
      | invoke parameters ty arguments body =>
          simp only [runFuel,prepareInvoke_addWork]
          cases hp : prepareInvoke s parameters arguments with
          | none => rfl
          | some callee =>
              simp only [Option.map_some,liftChecked,bind,Outcome.bind,ih]
              cases hb : runFuel fuel body callee with
              | fault => rfl
              | exhausted => rfl
              | finished step =>
                  simp only [addOutcomeWork,finishInvoke_addWork]
                  exact liftChecked_addWork (finishInvoke s ty step) extra
      | branch e yes no =>
          cases he : s.evaluate e with
          | none => simp [runFuel,evaluate_addWork,he,liftChecked,bind,Outcome.bind,addOutcomeWork]
          | some result =>
              have next : ({addWork s extra with work := (addWork s extra).work+result.work+1} : State).observe e.nodes =
                  addWork (({s with work := s.work+result.work+1} : State).observe e.nodes) extra := by
                simp [addWork,State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
              simp only [runFuel,evaluate_addWork,he,liftChecked,bind,Outcome.bind]
              rw [next]
              split <;> simp only [ih]
      | whileLoop e body =>
          cases he : s.evaluate e with
          | none => simp [runFuel,evaluate_addWork,he,liftChecked,bind,Outcome.bind,addOutcomeWork]
          | some result =>
              let next := ({s with work := s.work+result.work+1} : State).observe e.nodes
              have shifted : ({addWork s extra with work := (addWork s extra).work+result.work+1} : State).observe e.nodes =
                  addWork next extra := by
                simp [next,addWork,State.observe,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
              simp only [runFuel,evaluate_addWork,he,liftChecked,bind,Outcome.bind]
              rw [shifted]
              by_cases zero : result.value = 0
              · simp [zero,next,addOutcomeWork,addStepWork,pure]
              · simp only [beq_iff_eq,zero,↓reduceIte,ih]
                cases hb : runFuel fuel body next with
                | fault => rfl
                | exhausted => rfl
                | finished step =>
                    simp only [addOutcomeWork]
                    change (if step.returned.isSome then pure (addStepWork step extra)
                      else if step.breaking then pure {addStepWork step extra with breaking := false}
                      else runFuel fuel (.whileLoop e body) (addWork step.state extra)) = _
                    by_cases returned : step.returned.isSome = true
                    · simp [returned,pure]
                    · by_cases breaking : step.breaking = true <;>
                        simp [returned,breaking,ih,addOutcomeWork,addStepWork,pure]

end Proofs.CppWorkFrame
