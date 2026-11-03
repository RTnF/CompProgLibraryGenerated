import Proofs.CppNestedProgram

namespace Proofs.AppendRowStmt
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings

theorem appendRow_stmt (s next : NState) (container : Container) (slot : Nat) (ty : Ty) (frame : Frame)
    (eval : container.eval (s.charge 0 (container.nodes+2)) = some (next,slot))
    (run : next.frame.appendRow slot ty = some frame) :
    (NStmt.appendRow container ty).run s =
      some ⟨(({next with frame := frame} : NState).release s).charge 1 1,none,false⟩ := by
  simp [NStmt.run, eval, run]

theorem appendRow_valid (s : NState) (container : Container) (ty : Ty) (step : NStep)
    (ran : (NStmt.appendRow container ty).run s = some step) :
    step.state.frame.state.wellFormed = true := by
  unfold NStmt.run at ran
  cases eval : container.eval (s.charge 0 (container.nodes+2)) with
  | none => simp [eval] at ran
  | some pair =>
    obtain ⟨next,slot⟩ := pair
    simp only [eval, Bind.bind, Option.bind] at ran
    cases run : next.frame.appendRow slot ty with
    | none => simp [run] at ran
    | some frame =>
      simp only [run, Option.some.injEq] at ran
      cases ran
      exact Proofs.CppAppendRow.frame_appendRow_valid next.frame frame slot ty run

end Proofs.AppendRowStmt
