import Proofs.CppScalarFrame
import Proofs.CppEvalScope

namespace Proofs.CppNoResizeStmt
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.DynamicResultValid
open Proofs.CppScalarFrame Proofs.CppBufferHeaders Proofs.CppEvalFrame

def ScalarResult : Option Ret → Prop
  | none | some (.scalar _) => True
  | _ => False

def Allowed : NStmt → Bool
  | .write _ _ _ _ => true
  | stmt => Scalar stmt

structure Effects (s : NState) (out : NStep) : Prop where
  headers : SameHeaders s.frame.state out.state.frame.state
  flags : out.state.frame.rootWritable = s.frame.rootWritable
  scopedState : out.state.scope = s.scope
  returned : ScalarResult out.returned

theorem scalar_facts (stmt : NStmt) (s : NState) (out : NStep)
    (form : Scalar stmt = true) (actual : stmt.run s = some out) : out.state.scope = s.scope ∧ ScalarResult out.returned := by
  cases stmt with
  | skip =>
    have eq := Option.some.inj actual
    rw [← eq]
    exact ⟨rfl,trivial⟩
  | declare ty wr e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := Option.some.inj rest
    rw [← eq]
    exact ⟨Proofs.CppEvalScope.expression_scope e s t v ran,trivial⟩
  | assign slot ty e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨binding,cell⟩,_,rest⟩ := bind_some _ _ _ rest
    dsimp only at rest
    split at rest
    · obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
      have eq := Option.some.inj rest
      rw [← eq]
      exact ⟨Proofs.CppEvalScope.expression_scope e s t v ran,trivial⟩
    · simp at rest
  | ret e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    rw [← eq]
    exact ⟨Proofs.CppEvalScope.expression_scope e s t v ran,trivial⟩
  | check e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    dsimp only at rest
    split at rest
    · simp at rest
    · have eq := Option.some.inj rest
      rw [← eq]
      exact ⟨Proofs.CppEvalScope.expression_scope e s t v ran,trivial⟩
  | _ => simp [Scalar] at form

theorem scalar_effect (stmt : NStmt) (s : NState) (out : NStep)
    (form : Scalar stmt = true) (actual : stmt.run s = some out) : Effects s out := by
  have frame := scalar_frame stmt s out form actual
  obtain ⟨scopeEq,returned⟩ := scalar_facts stmt s out form actual
  refine ⟨?_,frame.2,scopeEq,returned⟩
  rw [frame.1]
  exact SameHeaders.refl _

theorem write_effect (s : NState) (out : NStep) (container : Container) (ty : Ty) (index expression : NExpr)
    (actual : (NStmt.write container ty index expression).run s = some out) : Effects s out := by
  have original := actual
  unfold NStmt.run at actual
  obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
  obtain ⟨⟨b,owner⟩,rb,rest⟩ := bind_some _ _ _ rest
  obtain ⟨⟨c,pos⟩,rc,rest⟩ := bind_some _ _ _ rest
  obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
  obtain ⟨frame,written,rest⟩ := bind_some _ _ _ rest
  have eq := Option.some.inj rest
  subst out
  obtain ⟨headers,flags⟩ := Proofs.CppWriteHeaders.stmt_write s _ container ty index expression original
  refine ⟨headers,flags,?_,trivial⟩
  exact (Proofs.CppEvalScope.expression_scope index b c pos rc).trans
    ((Proofs.CppEvalScope.container_scope container a b owner rb).trans
      (Proofs.CppEvalScope.expression_scope expression
        (s.charge 0 (container.nodes+index.nodes+expression.nodes+3)) a x ra))

theorem primitive (stmt : NStmt) (s : NState) (out : NStep)
    (form : Allowed stmt = true) (actual : stmt.run s = some out) : Effects s out := by
  cases stmt with
  | write container ty index expression => exact write_effect s out container ty index expression actual
  | _ =>
    apply scalar_effect _ s out ?_ actual
    exact form

end Proofs.CppNoResizeStmt
