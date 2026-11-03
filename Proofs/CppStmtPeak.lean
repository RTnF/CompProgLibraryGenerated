import Proofs.CppEvalPeak
import Proofs.CppNoResizeStmt
import Proofs.CppWritePeak

namespace Proofs.CppStmtPeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppPeakComponents Proofs.CppEvalPeak Proofs.DynamicResultValid

theorem scalar_peak (stmt : NStmt) (s : NState) (out : NStep)
    (form : Proofs.CppScalarFrame.Scalar stmt = true) (actual : stmt.run s = some out) : Grows s out.state := by
  cases stmt with
  | skip =>
    have eq := Option.some.inj actual
    rw [← eq]
    exact Grows.refl _
  | declare ty wr e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := Option.some.inj rest
    rw [← eq]
    let cells : Proofs.CppState.State := {t.scalars with
      memory := t.scalars.memory++[⟨ty,x⟩]
      bindings := t.scalars.bindings++[⟨t.scalars.memory.length,wr⟩]}
    let raw : NState := {(t.release s) with
      scalars := cells
      slots := t.slots++[.scalar t.scalars.bindings.length]}
    have updated : Grows (t.release s) raw := uncharged _ _ (Nat.le_refl _) (Nat.le_refl _) rfl
    exact (expression_peak e s t v ran).trans ((release t s).trans (updated.trans (charge raw 1 0)))
  | assign slot ty e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨binding,cell⟩,_,rest⟩ := bind_some _ _ _ rest
    dsimp only at rest
    split at rest
    · obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
      have eq := Option.some.inj rest
      rw [← eq]
      let raw : NState := {(t.release s) with scalars := {t.scalars with
        memory := t.scalars.memory.set binding.address ⟨cell.type,x⟩}}
      have updated : Grows (t.release s) raw := uncharged _ _ (Nat.le_refl _) (Nat.le_refl _) rfl
      exact (expression_peak e s t v ran).trans ((release t s).trans (updated.trans (charge raw 1 0)))
    · simp at rest
  | ret e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    rw [← eq]
    exact (expression_peak e s t v ran).trans ((release t s).trans (charge _ 1 0))
  | check e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    dsimp only at rest
    split at rest
    · simp at rest
    · have eq := Option.some.inj rest
      rw [← eq]
      exact (expression_peak e s t v ran).trans ((release t s).trans (charge _ 1 0))
  | _ => simp [Proofs.CppScalarFrame.Scalar] at form

theorem write_peak (s : NState) (out : NStep) (container : Container) (ty : Ty) (index expression : NExpr)
    (actual : (NStmt.write container ty index expression).run s = some out) : Grows s out.state := by
  unfold NStmt.run at actual
  obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
  obtain ⟨⟨b,owner⟩,rb,rest⟩ := bind_some _ _ _ rest
  obtain ⟨⟨c,pos⟩,rc,rest⟩ := bind_some _ _ _ rest
  obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
  obtain ⟨frame,written,rest⟩ := bind_some _ _ _ rest
  have peak := Proofs.CppWritePeak.frame_write_peak c.frame frame reference x written
  have storage : c.frame.state.storage.peak ≤ frame.state.storage.peak := by
    rw [peak]
    exact Nat.le_max_left _ _
  let raw : NState := {c with frame := frame}
  have framed : Grows c raw := reframe_raw c frame storage
  have before := (charge s 0 (container.nodes+index.nodes+expression.nodes+3)).trans
    ((expression_peak expression _ a x ra).trans ((container_peak container a b owner rb).trans (expression_peak index b c pos rc)))
  have eq := Option.some.inj rest
  subst out
  exact before.trans (framed.trans ((release raw s).trans (charge _ 1 0)))

theorem primitive (stmt : NStmt) (s : NState) (out : NStep)
    (allowed : Proofs.CppNoResizeStmt.Allowed stmt = true) (actual : stmt.run s = some out) : Grows s out.state := by
  cases stmt with
  | write container ty index expression => exact write_peak s out container ty index expression actual
  | _ =>
    apply scalar_peak _ s out ?_ actual
    exact allowed

end Proofs.CppStmtPeak
