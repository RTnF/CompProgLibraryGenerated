import Proofs.DynamicOwnedConstruct
import Proofs.DynamicStmtAuto

namespace Proofs.DynamicOwnedScalar
open Proofs.CppNestedProgram Proofs.CppNestedStmt Proofs.DynamicExpr Proofs.DynamicOwnedState

-- Scalar writes never change the vector frame, including its reference table.
-- Expression temporaries are released before the scalar operation completes.
theorem released {s t : NState} {e : NExpr} {v : Int} {extra : List Proofs.CppNestedVectorBindings.Binding}
    {w p : Nat} (ev : Ev s e t v extra w p) : (t.release s).frame = s.frame := by
  have bindings := DynamicConstructCore.release_bindings s t extra ev.2.2
  have state := ev.2.1.1
  have flags := ev.2.1.2.1
  change t.frame.bindings.take s.frame.bindings.length = s.frame.bindings at bindings
  change (⟨t.frame.state,t.frame.rootWritable,t.frame.bindings.take s.frame.bindings.length⟩ : Proofs.CppNestedVectorBindings.Frame) = s.frame
  rw [state,flags,bindings]

-- Layout is derived from the actual checked operation and certified evaluation;
-- the ordinary scalar simulation supplies the new logical contents separately.
theorem layout (st : State) (s : NState) (real : Realizes st s) (stmt : NStmt)
    (form : DynamicStmtAuto.ScalarForm stmt) (result : DynamicStmt.Step)
    (pureRun : DynamicStmt.run st.params stmt st.core = some result)
    (out : NStep) (actual : stmt.run s = some out) : out.state.frame = s.frame ∧ out.state.scope = s.scope := by
  have eval (e : NExpr) (v : Int) (value : denote st.params st.core.locals st.core.contents e = some v) :=
    DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) v value) s real.data
  cases stmt with
  | skip =>
    have same : (⟨s,none,false⟩ : NStep) = out := Option.some.inj actual
    subst out; exact ⟨rfl,rfl⟩
  | declare ty wr e =>
    obtain ⟨v,value,_⟩ := DynamicResultValid.bind_some _ _ _ pureRun
    obtain ⟨_,t,extra,ev⟩ := eval e v value
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind] at actual
    obtain ⟨x,_,same⟩ := DynamicResultValid.bind_some _ _ _ actual
    have equal := Option.some.inj same
    subst out
    exact ⟨released ev,ev.2.1.2.2.2.1⟩
  | assign slot ty e =>
    obtain ⟨v,value,_⟩ := DynamicResultValid.bind_some _ _ _ pureRun
    obtain ⟨_,t,extra,ev⟩ := eval e v value
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind] at actual
    obtain ⟨pair,_,rest⟩ := DynamicResultValid.bind_some _ _ _ actual
    obtain ⟨binding,cell⟩ := pair
    cases wr : binding.writable with
    | false => simp [wr] at rest
    | true =>
      simp only [wr,ite_true] at rest
      obtain ⟨x,_,same⟩ := DynamicResultValid.bind_some _ _ _ rest
      have equal := Option.some.inj same
      subst out
      exact ⟨released ev,ev.2.1.2.2.2.1⟩
  | ret e =>
    obtain ⟨v,value,_⟩ := DynamicResultValid.bind_some _ _ _ pureRun
    obtain ⟨_,t,extra,ev⟩ := eval e v value
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind] at actual
    have equal := Option.some.inj actual
    subst out
    exact ⟨released ev,ev.2.1.2.2.2.1⟩
  | check e =>
    obtain ⟨v,value,_⟩ := DynamicResultValid.bind_some _ _ _ pureRun
    obtain ⟨_,t,extra,ev⟩ := eval e v value
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind] at actual
    split at actual
    · contradiction
    · have equal := Option.some.inj actual
      subst out
      exact ⟨released ev,ev.2.1.2.2.2.1⟩
  | _ => simp [DynamicStmtAuto.ScalarForm] at form

theorem sound (st : State) (s : NState) (real : Realizes st s) (stmt : NStmt)
    (form : DynamicStmtAuto.ScalarForm stmt) (result : DynamicStmt.Step)
    (pureRun : DynamicStmt.run st.params stmt st.core = some result) :
    ∃ out, stmt.run s = some out ∧ Realizes {st with core := result.state} out.state ∧
      out.returned = result.returned.map Ret.scalar ∧ out.breaking = false ∧
      out.state.work ≤ s.work+DynamicScalarSound.workBound stmt ∧
      out.state.peak ≤ max s.peak (max s.scalars.peak
        (Proofs.CppNestedEval.liveS s+DynamicScalarSound.tempBound stmt)+s.frame.state.storage.peak) := by
  obtain ⟨out,ran,matched,work,peak⟩ := DynamicStmtAuto.scalar_sound st.params st.core s real.data stmt form result pureRun
  obtain ⟨frame,scope⟩ := layout st s real stmt form result pureRun out ran
  exact ⟨out,ran,⟨matched.state,by rw [frame]; exact real.owner,by rw [frame]; exact real.binding,scope.trans real.scopedState⟩,
    matched.returned,matched.breaking,work,peak⟩

end Proofs.DynamicOwnedScalar
