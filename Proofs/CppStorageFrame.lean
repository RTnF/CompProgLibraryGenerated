import Proofs.CppInvokePreparation

namespace Proofs.CppStorageFrame
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop

def StorageFrame (before after : State) : Prop :=
  before.memory.length ≤ after.memory.length ∧ after.baseMemory = before.baseMemory

theorem storage_refl (s : State) : StorageFrame s s := ⟨Nat.le_refl _,rfl⟩

theorem storage_trans (a b c : State) (first : StorageFrame a b)
    (second : StorageFrame b c) : StorageFrame a c :=
  ⟨Nat.le_trans first.1 second.1,second.2.trans first.2⟩

theorem finish_storage (caller : State) (ty : Ty) (step result : Step)
    (success : finishInvoke caller ty step = some result) : StorageFrame caller result.state := by
  have preserved := Proofs.CppInvokeProofs.result_caller_memory caller ty step result success
  have base := Proofs.CppInvokeProofs.result_resources caller ty step result success
  have lengths := congrArg List.length preserved.1
  simp only [List.length_take] at lengths
  exact ⟨by omega,base.2.2⟩

theorem run_storage (stmt : Stmt) (s : State) (step : Step)
    (success : stmt.run s = some step) : StorageFrame s step.state := by
  induction stmt generalizing s step with
  | skip => simp [Stmt.run] at success; cases success; exact storage_refl s
  | whileLoop _ _ _ => simp [Stmt.run] at success
  | breakLoop => simp [Stmt.run] at success
  | declare ty writable e =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,he] at success
      | some value =>
          cases hv : ty.convert value.value with
          | none => simp [Stmt.run,he,hv] at success
          | some converted =>
              simp [Stmt.run,he,hv] at success
              cases success
              simp [StorageFrame,State.observe]
  | ret e =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,he] at success
      | some value =>
          simp [Stmt.run,he] at success
          cases success
          exact storage_refl s
  | check e =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,he] at success
      | some value =>
          by_cases zero : value.value = 0
          · simp [Stmt.run,he,zero] at success
          · simp [Stmt.run,he,zero] at success
            cases success
            exact storage_refl s
  | assign slot e =>
      cases hb : s.bindings[slot]? with
      | none => simp [Stmt.run,hb] at success
      | some binding =>
          by_cases writable : binding.writable = true
          · cases hc : s.memory[binding.address]? with
            | none => simp [Stmt.run,hb,writable,hc] at success
            | some cell =>
                cases he : s.evaluate e with
                | none => simp [Stmt.run,hb,he] at success
                | some value =>
                    cases hv : cell.type.convert value.value with
                    | none => simp [Stmt.run,hb,writable,hc,he,hv] at success
                    | some converted =>
                        simp [Stmt.run,hb,writable,hc,he,hv] at success
                        cases success
                        simp [StorageFrame,State.observe]
          · simp [Stmt.run,hb,writable] at success
  | swap left right =>
      cases hl : s.bindings[left]? with
      | none => simp [Stmt.run,hl] at success
      | some lhs =>
          cases hr : s.bindings[right]? with
          | none => simp [Stmt.run,hl,hr] at success
          | some rhs =>
              cases ha : s.memory[lhs.address]? with
              | none => simp [Stmt.run,hl,hr,ha] at success
              | some a =>
                  cases hb : s.memory[rhs.address]? with
                  | none => simp [Stmt.run,hl,hr,hb] at success
                  | some b =>
                      simp [Stmt.run,hl,hr,ha,hb] at success
                      rcases success with ⟨_,_,success⟩
                      cases success
                      simp [StorageFrame,State.observe]
  | branch e yes no yesIH noIH =>
      cases he : s.evaluate e with
      | none => simp [Stmt.run,he] at success
      | some value =>
          let next := ({s with work := s.work+value.work+1} : State).observe e.nodes
          have frame : StorageFrame s next := storage_refl s
          by_cases zero : value.value = 0
          · have body : no.run next = some step := by simpa [Stmt.run,he,zero,next] using success
            exact storage_trans s next step.state frame (noIH next step body)
          · have body : yes.run next = some step := by simpa [Stmt.run,he,zero,next] using success
            exact storage_trans s next step.state frame (yesIH next step body)
  | sequence first rest firstIH restIH =>
      cases hf : first.run s with
      | none => simp [Stmt.run,hf] at success
      | some middle =>
          have frame := firstIH s middle hf
          by_cases returned : middle.returned.isSome = true
          · simp [Stmt.run,hf,returned] at success
            cases success
            exact frame
          · have tail : rest.run middle.state = some step := by simpa [Stmt.run,hf,returned] using success
            exact storage_trans s middle.state step.state frame (restIH middle.state step tail)
  | scope body bodyIH =>
      cases hb : body.run s with
      | none => simp [Stmt.run,hb] at success
      | some middle =>
          have frame := bodyIH s middle hb
          simp [Stmt.run,hb] at success
          cases success
          simp [StorageFrame,List.length_take,Nat.min_eq_left frame.1,frame.2]
  | invoke parameters ty arguments body _ =>
      cases hp : prepareInvoke s parameters arguments with
      | none => simp [Stmt.run,hp] at success
      | some callee =>
          cases hb : body.run callee with
          | none => simp [Stmt.run,hp,hb] at success
          | some middle =>
              have finished : finishInvoke s ty middle = some step := by
                simpa [Stmt.run,hp,hb] using success
              exact finish_storage s ty middle step finished

theorem prepare_storage (s : State) (parameters : List (Ty × Bool)) (arguments : List Expr)
    (callee : State) (success : prepareInvoke s parameters arguments = some callee) :
    StorageFrame s callee := by
  obtain ⟨values,_,_,memory,_,base,_,_⟩ :=
    Proofs.CppInvokePreparation.prepare_shape s parameters arguments callee success
  refine ⟨?_,base⟩
  simp [memory,Proofs.CppInvokePreparation.callerPrefix]

theorem checked_storage (stmt : Stmt) (s : State) (step : Step)
    (success : liftChecked (stmt.run s) = .finished step) : StorageFrame s step.state := by
  cases result : stmt.run s with
  | none => simp [liftChecked,result] at success
  | some middle =>
      have frame := run_storage stmt s middle result
      simp [liftChecked,result] at success
      cases success
      exact frame

theorem runFuel_storage (fuel : Nat) (stmt : Stmt) (s : State) (step : Step)
    (success : runFuel fuel stmt s = .finished step) : StorageFrame s step.state := by
  induction fuel generalizing stmt s step with
  | zero => simp [runFuel] at success
  | succ fuel ih =>
      cases stmt with
      | skip => exact checked_storage .skip s step success
      | declare ty writable e => exact checked_storage _ s step success
      | assign slot e => exact checked_storage _ s step success
      | swap left right => exact checked_storage _ s step success
      | ret e => exact checked_storage _ s step success
      | check e => exact checked_storage _ s step success
      | breakLoop =>
          simp [runFuel,pure] at success
          cases success
          exact storage_refl s
      | scope body =>
          cases hb : runFuel fuel body s with
          | fault => simp [runFuel,hb,bind,Outcome.bind] at success
          | exhausted => simp [runFuel,hb,bind,Outcome.bind] at success
          | finished middle =>
              have frame := ih body s middle hb
              simp [runFuel,hb,bind,Outcome.bind,pure] at success
              cases success
              simp [StorageFrame,List.length_take,Nat.min_eq_left frame.1,frame.2]
      | sequence first rest =>
          cases hf : runFuel fuel first s with
          | fault => simp [runFuel,hf,bind,Outcome.bind] at success
          | exhausted => simp [runFuel,hf,bind,Outcome.bind] at success
          | finished middle =>
              have frame := ih first s middle hf
              by_cases stopped : (middle.returned.isSome || middle.breaking) = true
              · simp [runFuel,hf,stopped,bind,Outcome.bind,pure] at success
                cases success
                exact frame
              · have tail : runFuel fuel rest middle.state = .finished step := by
                  simpa [runFuel,hf,stopped,bind,Outcome.bind] using success
                exact storage_trans s middle.state step.state frame (ih rest middle.state step tail)
      | invoke parameters ty arguments body =>
          cases hp : prepareInvoke s parameters arguments with
          | none => simp [runFuel,hp,liftChecked,bind,Outcome.bind] at success
          | some callee =>
              cases hb : runFuel fuel body callee with
              | fault => simp [runFuel,hp,hb,liftChecked,bind,Outcome.bind] at success
              | exhausted => simp [runFuel,hp,hb,liftChecked,bind,Outcome.bind] at success
              | finished middle =>
                  cases hr : finishInvoke s ty middle with
                  | none => simp [runFuel,hp,hb,hr,liftChecked,bind,Outcome.bind] at success
                  | some result =>
                      have frame := finish_storage s ty middle result hr
                      simp [runFuel,hp,hb,hr,liftChecked,bind,Outcome.bind] at success
                      cases success
                      exact frame
      | branch e yes no =>
          cases he : s.evaluate e with
          | none => simp [runFuel,he,liftChecked,bind,Outcome.bind] at success
          | some value =>
              let next := ({s with work := s.work+value.work+1} : State).observe e.nodes
              have frame : StorageFrame s next := storage_refl s
              by_cases zero : value.value = 0
              · have body : runFuel fuel no next = .finished step := by
                  simpa [runFuel,he,zero,next,liftChecked,bind,Outcome.bind] using success
                exact storage_trans s next step.state frame (ih no next step body)
              · have body : runFuel fuel yes next = .finished step := by
                  simpa [runFuel,he,zero,next,liftChecked,bind,Outcome.bind] using success
                exact storage_trans s next step.state frame (ih yes next step body)
      | whileLoop e body =>
          cases he : s.evaluate e with
          | none => simp [runFuel,he,liftChecked,bind,Outcome.bind] at success
          | some value =>
              let next := ({s with work := s.work+value.work+1} : State).observe e.nodes
              have frame : StorageFrame s next := storage_refl s
              by_cases zero : value.value = 0
              · simp [runFuel,he,zero,liftChecked,bind,Outcome.bind,pure] at success
                cases success
                exact storage_refl s
              · cases hb : runFuel fuel body next with
                | fault => simp [runFuel,he,zero,hb,next,liftChecked,bind,Outcome.bind] at success
                | exhausted => simp [runFuel,he,zero,hb,next,liftChecked,bind,Outcome.bind] at success
                | finished middle =>
                    have bodyFrame := storage_trans s next middle.state frame (ih body next middle hb)
                    by_cases returned : middle.returned.isSome = true
                    · simp [runFuel,he,zero,hb,next,returned,liftChecked,bind,Outcome.bind,pure] at success
                      cases success
                      exact bodyFrame
                    · by_cases breaking : middle.breaking = true
                      · simp [runFuel,he,zero,hb,next,returned,breaking,liftChecked,bind,Outcome.bind,pure] at success
                        cases success
                        exact bodyFrame
                      · have tail : runFuel fuel (.whileLoop e body) middle.state = .finished step := by
                          simpa [runFuel,he,zero,hb,next,returned,breaking,liftChecked,bind,Outcome.bind] using success
                        exact storage_trans s middle.state step.state bodyFrame
                          (ih (.whileLoop e body) middle.state step tail)

theorem runFuel_base_bound (fuel : Nat) (stmt : Stmt) (s : State) (step : Step)
    (initial : s.baseMemory ≤ s.memory.length)
    (success : runFuel fuel stmt s = .finished step) :
    step.state.baseMemory ≤ step.state.memory.length := by
  obtain ⟨growth,base⟩ := runFuel_storage fuel stmt s step success
  rw [base]
  exact Nat.le_trans initial growth

-- Lowering the exclusion boundary counts existing caller cells as live storage.
-- The peak is translated by the same amount; values and work are unchanged.
def lowerBase (s : State) (offset : Nat) : State :=
  {s with baseMemory := s.baseMemory-offset,peak := s.peak+offset}

theorem lowerBase_evaluate (s : State) (offset : Nat) (e : Expr) :
    (lowerBase s offset).evaluate e = s.evaluate e := rfl

theorem lowerBase_observe (s : State) (offset temporaries : Nat)
    (within : offset ≤ s.baseMemory) (allocated : s.baseMemory ≤ s.memory.length) :
    (lowerBase s offset).observe temporaries = lowerBase (s.observe temporaries) offset := by
  simp [lowerBase,State.observe]
  congr 1
  omega

theorem lowerBase_live (s : State) (offset temporaries : Nat)
    (within : offset ≤ s.baseMemory) (allocated : s.baseMemory ≤ s.memory.length) :
    (lowerBase s offset).memory.length - (lowerBase s offset).baseMemory +
      (lowerBase s offset).bindings.length + temporaries =
    s.memory.length-s.baseMemory+s.bindings.length+temporaries+offset := by
  simp only [lowerBase]
  omega

theorem bindValueResults_lowerBase (s : State) (offset : Nat)
    (parameters : List (Ty × Bool)) (values : List Result)
    (within : offset ≤ s.baseMemory) (allocated : s.baseMemory ≤ s.memory.length) :
    bindValueResults (lowerBase s offset) parameters values =
      (bindValueResults s parameters values).map (fun result => lowerBase result offset) := by
  induction parameters generalizing s values with
  | nil => cases values <;> rfl
  | cons p ps ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [bindValueResults]
          split
          · rfl
          · let next : State := {s with
              memory := s.memory ++ [⟨p.1,value.value⟩],
              bindings := s.bindings ++ [⟨s.memory.length,p.2⟩],
              work := s.work+value.work+1}
            have nextWithin : offset ≤ next.baseMemory := within
            have nextAllocated : next.baseMemory ≤ next.memory.length := by
              simp [next]
              omega
            change bindValueResults ((lowerBase next offset).observe 0) ps values =
              (bindValueResults (next.observe 0) ps values).map (fun result => lowerBase result offset)
            rw [lowerBase_observe next offset 0 nextWithin nextAllocated]
            exact ih (next.observe 0) values nextWithin nextAllocated

end Proofs.CppStorageFrame
