import Proofs.DynamicExprAuto
import Proofs.DynamicControlBridge

namespace Proofs.DynamicStmtAuto
open Proofs.CppNestedProgram Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicScalarSound

-- Keep the statement profile explicit: vector operations have allocation and
-- scope premises that pure scalar success alone does not supply.
def ScalarForm : NStmt → Prop
  | .skip | .declare _ _ _ | .assign _ _ _ | .ret _ | .check _ => True
  | _ => False

theorem scalar_ready (params : List Parameter) (st : DynamicStmt.State) (stmt : NStmt)
    (form : ScalarForm stmt) : ScalarReady params st stmt := by
  cases stmt with
  | skip => exact True.intro
  | declare _ _ e | assign _ _ e | ret e | check e => exact DynamicExprAuto.ready params st.locals st.contents e
  | _ => simp [ScalarForm] at form

theorem scalar_sound (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (stmt : NStmt) (form : ScalarForm stmt)
    (result : DynamicStmt.Step) (run : DynamicStmt.run params stmt st = some result) :
    ∃ actual, stmt.run s = some actual ∧ Matches params result actual ∧
      actual.state.work ≤ s.work+workBound stmt ∧ actual.state.peak ≤ max s.peak
        (max s.scalars.peak (Proofs.CppNestedEval.liveS s+tempBound stmt)+s.frame.state.storage.peak) :=
  DynamicScalarSound.sound params st s realizes stmt (scalar_ready params st stmt form) result run

theorem scalar_runs (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (stmt : NStmt) (form : ScalarForm stmt)
    (result : DynamicStmt.Step) (run : DynamicStmt.run params stmt st = some result) :
    DynamicControlBridge.Runs params (.primitive stmt) st s (fun final actual =>
      final = DynamicControl.ofStmt result ∧ actual.state.work ≤ s.work+workBound stmt ∧
      actual.state.peak ≤ max s.peak (max s.scalars.peak
        (Proofs.CppNestedEval.liveS s+tempBound stmt)+s.frame.state.storage.peak)) :=
  DynamicControlBridge.Runs.scalar realizes (scalar_ready params st stmt form) result run

end Proofs.DynamicStmtAuto
