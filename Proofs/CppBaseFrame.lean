import Proofs.CppStorageFrame

namespace Proofs.CppBaseFrame
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppStorageFrame

def lowerStepBase (step : Step) (offset : Nat) : Step :=
  {step with state := lowerBase step.state offset}

theorem fold_max_add (xs : List α) (f : α → Nat) (initial offset : Nat) :
    xs.foldl (fun peak x => max peak (f x+offset)) (initial+offset) =
      xs.foldl (fun peak x => max peak (f x)) initial + offset := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have shifted : max (initial+offset) (f x+offset) = max initial (f x)+offset := by omega
      rw [shifted,ih]

theorem argumentPeak_lowerBase (s : State) (arguments : List Expr) (offset : Nat)
    (within : offset ≤ s.baseMemory) (allocated : s.baseMemory ≤ s.memory.length) :
    Proofs.CppInvokePreparation.argumentPeak (lowerBase s offset) arguments =
      Proofs.CppInvokePreparation.argumentPeak s arguments + offset := by
  have peaks (e : Expr) : ((lowerBase s offset).observe (arguments.length+e.nodes)).peak =
      (s.observe (arguments.length+e.nodes)).peak+offset := by
    rw [lowerBase_observe s offset _ within allocated]
    rfl
  simp only [Proofs.CppInvokePreparation.argumentPeak,peaks]
  exact fold_max_add arguments (fun e => (s.observe (arguments.length+e.nodes)).peak) s.peak offset

theorem prepareInvoke_lowerBase (s : State) (parameters : List (Ty × Bool))
    (arguments : List Expr) (offset : Nat)
    (within : offset ≤ s.baseMemory) (allocated : s.baseMemory ≤ s.memory.length) :
    prepareInvoke (lowerBase s offset) parameters arguments =
      (prepareInvoke s parameters arguments).map (fun result => lowerBase result offset) := by
  have evaluator : (lowerBase s offset).evaluate = s.evaluate := rfl
  cases evaluated : arguments.mapM s.evaluate with
  | none => simp [prepareInvoke,evaluator,evaluated]
  | some values =>
      let initial : State := {s with
        memory := Proofs.CppInvokePreparation.callerPrefix s,bindings := [],work := s.work+1,
        peak := Proofs.CppInvokePreparation.argumentPeak s arguments}
      have bound : initial.baseMemory ≤ initial.memory.length := by
        simp [initial,Proofs.CppInvokePreparation.callerPrefix]
        omega
      have shifted : ({lowerBase s offset with
          memory := Proofs.CppInvokePreparation.callerPrefix (lowerBase s offset),
          bindings := [],work := (lowerBase s offset).work+1,
          peak := Proofs.CppInvokePreparation.argumentPeak (lowerBase s offset) arguments} : State) =
          lowerBase initial offset := by
        rw [argumentPeak_lowerBase s arguments offset within allocated]
        rfl
      simp only [prepareInvoke,evaluator,evaluated,bind,Option.bind]
      change bindValueResults (({lowerBase s offset with
          memory := Proofs.CppInvokePreparation.callerPrefix (lowerBase s offset),
          bindings := [],work := (lowerBase s offset).work+1,
          peak := Proofs.CppInvokePreparation.argumentPeak (lowerBase s offset) arguments} : State).observe 0) parameters values =
        (bindValueResults (initial.observe 0) parameters values).map (fun result => lowerBase result offset)
      rw [shifted,lowerBase_observe initial offset 0 within bound]
      exact bindValueResults_lowerBase (initial.observe 0) offset parameters values within bound

theorem finishInvoke_lowerBase (caller : State) (ty : Ty) (step : Step) (offset : Nat)
    (within : offset ≤ caller.baseMemory) (allocated : caller.baseMemory ≤ caller.memory.length) :
    finishInvoke (lowerBase caller offset) ty (lowerStepBase step offset) =
      (finishInvoke caller ty step).map (fun result => lowerStepBase result offset) := by
  cases step with
  | mk callee value breaking =>
      cases breaking with
      | true => simp [finishInvoke,lowerStepBase]
      | false =>
          cases value with
          | none => simp [finishInvoke,lowerStepBase]
          | some value =>
              cases valid : ty.valid value with
              | false => simp [finishInvoke,lowerStepBase,valid]
              | true =>
                  simp [finishInvoke,lowerStepBase,lowerBase,valid,State.observe]
                  congr 2
                  omega

theorem memory_lowerBase (s : State) (offset : Nat) : (lowerBase s offset).memory = s.memory := rfl
theorem bindings_lowerBase (s : State) (offset : Nat) : (lowerBase s offset).bindings = s.bindings := rfl

theorem run_lowerBase (stmt : Stmt) (s : State) (offset : Nat)
    (within : offset ≤ s.baseMemory) (allocated : s.baseMemory ≤ s.memory.length) :
    stmt.run (lowerBase s offset) = (stmt.run s).map (fun step => lowerStepBase step offset) := by
  induction stmt generalizing s with
  | skip => rfl
  | whileLoop _ _ _ => rfl
  | breakLoop => rfl
  | declare ty writable e =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,lowerBase_evaluate,he]
      | some result =>
          cases hc : ty.convert result.value <;>
            simp only [Stmt.run,lowerBase_evaluate,he,hc,bind,Option.bind] <;>
            simp [lowerBase,lowerStepBase,State.observe] <;> congr 2 <;> omega
  | ret e =>
      cases he : s.evaluate e <;>
        simp only [Stmt.run,lowerBase_evaluate,he,bind,Option.bind] <;>
        simp [lowerBase,lowerStepBase,State.observe] <;> congr 2 <;> omega
  | check e =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,lowerBase_evaluate,he]
      | some result =>
          by_cases zero : result.value = 0 <;>
            simp only [Stmt.run,lowerBase_evaluate,he,bind,Option.bind] <;>
            simp [zero,lowerBase,lowerStepBase,State.observe] <;> congr 2 <;> omega
  | assign slot e =>
      cases hb : s.bindings[slot]? with
      | none => simp [Stmt.run,lowerBase,hb]
      | some binding =>
          cases hc : s.memory[binding.address]? with
          | none => simp [Stmt.run,lowerBase,hb,hc]
          | some cell =>
              cases he : s.evaluate e with
              | none =>
                  simp only [Stmt.run,lowerBase_evaluate,memory_lowerBase,bindings_lowerBase,hb,hc,he,bind,Option.bind]
                  split <;> rfl
              | some result =>
                  cases hv : cell.type.convert result.value <;> cases hw : binding.writable <;>
                    simp only [Stmt.run,lowerBase_evaluate,memory_lowerBase,bindings_lowerBase,hb,hc,he,hv,hw,bind,Option.bind] <;>
                    simp [lowerBase,lowerStepBase,State.observe] <;> congr 2 <;> omega
  | swap left right =>
      cases hl : s.bindings[left]? with
      | none => simp [Stmt.run,lowerBase,hl]
      | some lhs =>
          cases hr : s.bindings[right]? with
          | none => simp [Stmt.run,lowerBase,hl,hr]
          | some rhs =>
              cases ha : s.memory[lhs.address]? with
              | none => simp [Stmt.run,lowerBase,hl,hr,ha]
              | some a =>
                  cases hb : s.memory[rhs.address]? with
                  | none => simp [Stmt.run,lowerBase,hl,hr,hb]
                  | some b =>
                      simp only [Stmt.run,memory_lowerBase,bindings_lowerBase,hl,hr,ha,hb,bind,Option.bind]
                      split
                      · rfl
                      · split
                        · rfl
                        · simp [lowerBase,lowerStepBase,State.observe]
                          congr 2
                          omega
  | branch e yes no yesIH noIH =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,lowerBase_evaluate,he]
      | some result =>
          let next := ({s with work := s.work+result.work+1} : State).observe e.nodes
          have shifted : ({lowerBase s offset with work := (lowerBase s offset).work+result.work+1} : State).observe e.nodes =
              lowerBase next offset :=
            lowerBase_observe ({s with work := s.work+result.work+1} : State) offset e.nodes within allocated
          simp only [Stmt.run,lowerBase_evaluate,he,bind,Option.bind]
          change (if result.value == 0 then no.run _ else yes.run _) = _
          rw [shifted]
          split <;> simp only [yesIH next within allocated,noIH next within allocated] <;> rfl
  | sequence first rest firstIH restIH =>
      simp only [Stmt.run,firstIH s within allocated]
      cases hf : first.run s with
      | none => simp
      | some middle =>
          have frame := run_storage first s middle hf
          have mw : offset ≤ middle.state.baseMemory := by rw [frame.2]; exact within
          have ma : middle.state.baseMemory ≤ middle.state.memory.length := by
            rw [frame.2]
            exact Nat.le_trans allocated frame.1
          simp only [Option.map_some,bind,Option.bind]
          change (if middle.returned.isSome then some (lowerStepBase middle offset)
            else rest.run (lowerBase middle.state offset)) = _
          split <;> simp_all [restIH middle.state mw ma]
  | scope body bodyIH =>
      simp only [Stmt.run,bodyIH s within allocated]
      cases hb : body.run s <;> simp [lowerStepBase,lowerBase]
  | invoke parameters ty arguments body bodyIH =>
      simp only [Stmt.run,prepareInvoke_lowerBase s parameters arguments offset within allocated]
      cases hp : prepareInvoke s parameters arguments with
      | none => simp
      | some callee =>
          have frame := prepare_storage s parameters arguments callee hp
          have cw : offset ≤ callee.baseMemory := by rw [frame.2]; exact within
          have ca : callee.baseMemory ≤ callee.memory.length := by
            rw [frame.2]
            exact Nat.le_trans allocated frame.1
          simp only [Option.map_some,bind,Option.bind,bodyIH callee cw ca]
          cases hb : body.run callee <;>
            simp [finishInvoke_lowerBase s ty _ offset within allocated]

def lowerOutcomeBase (outcome : Outcome Step) (offset : Nat) : Outcome Step :=
  match outcome with
  | .finished step => .finished (lowerStepBase step offset)
  | .fault => .fault
  | .exhausted => .exhausted

theorem liftChecked_lowerBase (value : Option Step) (offset : Nat) :
    liftChecked (value.map (fun step => lowerStepBase step offset)) =
      lowerOutcomeBase (liftChecked value) offset := by cases value <;> rfl

theorem runFuel_lowerBase (fuel : Nat) (stmt : Stmt) (s : State) (offset : Nat)
    (within : offset ≤ s.baseMemory) (allocated : s.baseMemory ≤ s.memory.length) :
    runFuel fuel stmt (lowerBase s offset) = lowerOutcomeBase (runFuel fuel stmt s) offset := by
  induction fuel generalizing stmt s with
  | zero => rfl
  | succ fuel ih =>
      cases stmt with
      | skip => rfl
      | declare ty writable e =>
          simpa only [runFuel,run_lowerBase _ s offset within allocated] using
            liftChecked_lowerBase ((Stmt.declare ty writable e).run s) offset
      | assign slot e =>
          simpa only [runFuel,run_lowerBase _ s offset within allocated] using
            liftChecked_lowerBase ((Stmt.assign slot e).run s) offset
      | swap left right =>
          simpa only [runFuel,run_lowerBase _ s offset within allocated] using
            liftChecked_lowerBase ((Stmt.swap left right).run s) offset
      | ret e =>
          simpa only [runFuel,run_lowerBase _ s offset within allocated] using
            liftChecked_lowerBase ((Stmt.ret e).run s) offset
      | check e =>
          simpa only [runFuel,run_lowerBase _ s offset within allocated] using
            liftChecked_lowerBase ((Stmt.check e).run s) offset
      | breakLoop => rfl
      | scope body =>
          simp only [runFuel,ih body s within allocated]
          cases hb : runFuel fuel body s <;>
            simp [lowerOutcomeBase,lowerStepBase,lowerBase,bind,pure,Outcome.bind]
      | sequence first rest =>
          simp only [runFuel,ih first s within allocated]
          cases hf : runFuel fuel first s with
          | fault => rfl
          | exhausted => rfl
          | finished middle =>
              have frame := runFuel_storage fuel first s middle hf
              have mw : offset ≤ middle.state.baseMemory := by rw [frame.2]; exact within
              have ma : middle.state.baseMemory ≤ middle.state.memory.length := by
                rw [frame.2]
                exact Nat.le_trans allocated frame.1
              simp only [lowerOutcomeBase,bind,Outcome.bind]
              change (if middle.returned.isSome || middle.breaking then pure (lowerStepBase middle offset)
                else runFuel fuel rest (lowerBase middle.state offset)) = _
              split <;> simp_all [ih rest middle.state mw ma,lowerOutcomeBase,pure]
      | invoke parameters ty arguments body =>
          simp only [runFuel,prepareInvoke_lowerBase s parameters arguments offset within allocated]
          cases hp : prepareInvoke s parameters arguments with
          | none => rfl
          | some callee =>
              have frame := prepare_storage s parameters arguments callee hp
              have cw : offset ≤ callee.baseMemory := by rw [frame.2]; exact within
              have ca : callee.baseMemory ≤ callee.memory.length := by
                rw [frame.2]
                exact Nat.le_trans allocated frame.1
              simp only [Option.map_some,liftChecked,bind,Outcome.bind,ih body callee cw ca]
              cases hb : runFuel fuel body callee with
              | fault => rfl
              | exhausted => rfl
              | finished step =>
                  simp only [lowerOutcomeBase,finishInvoke_lowerBase s ty step offset within allocated]
                  exact liftChecked_lowerBase (finishInvoke s ty step) offset
      | branch e yes no =>
          cases he : s.evaluate e with
          | none => simp [runFuel,lowerBase_evaluate,he,liftChecked,bind,Outcome.bind,lowerOutcomeBase]
          | some result =>
              let next := ({s with work := s.work+result.work+1} : State).observe e.nodes
              have shifted : ({lowerBase s offset with work := (lowerBase s offset).work+result.work+1} : State).observe e.nodes =
                  lowerBase next offset :=
                lowerBase_observe ({s with work := s.work+result.work+1} : State) offset e.nodes within allocated
              simp only [runFuel,lowerBase_evaluate,he,liftChecked,bind,Outcome.bind]
              rw [shifted]
              split <;> simp only [ih yes next within allocated,ih no next within allocated] <;> rfl
      | whileLoop e body =>
          cases he : s.evaluate e with
          | none => simp [runFuel,lowerBase_evaluate,he,liftChecked,bind,Outcome.bind,lowerOutcomeBase]
          | some result =>
              let next := ({s with work := s.work+result.work+1} : State).observe e.nodes
              have shifted : ({lowerBase s offset with work := (lowerBase s offset).work+result.work+1} : State).observe e.nodes =
                  lowerBase next offset :=
                lowerBase_observe ({s with work := s.work+result.work+1} : State) offset e.nodes within allocated
              simp only [runFuel,lowerBase_evaluate,he,liftChecked,bind,Outcome.bind]
              rw [shifted]
              by_cases zero : result.value = 0
              · simp [zero,next,lowerOutcomeBase,lowerStepBase,pure]
              · simp only [beq_iff_eq,zero,↓reduceIte,ih body next within allocated]
                cases hb : runFuel fuel body next with
                | fault => rfl
                | exhausted => rfl
                | finished middle =>
                    have frame := runFuel_storage fuel body next middle hb
                    have mw : offset ≤ middle.state.baseMemory := by rw [frame.2]; exact within
                    have ma : middle.state.baseMemory ≤ middle.state.memory.length := by
                      rw [frame.2]
                      exact Nat.le_trans allocated frame.1
                    simp only [lowerOutcomeBase]
                    change (if middle.returned.isSome then pure (lowerStepBase middle offset)
                      else if middle.breaking then pure {lowerStepBase middle offset with breaking := false}
                      else runFuel fuel (.whileLoop e body) (lowerBase middle.state offset)) = _
                    by_cases returned : middle.returned.isSome = true
                    · simp [returned,pure]
                    · by_cases breaking : middle.breaking = true <;>
                        simp [returned,breaking,ih (.whileLoop e body) middle.state mw ma,
                          lowerOutcomeBase,lowerStepBase,pure]

end Proofs.CppBaseFrame
