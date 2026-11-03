import Proofs.CppWriteHeaders

namespace Proofs.CppScalarFrame
open Proofs.CppNestedProgram Proofs.DynamicResultValid Proofs.CppEvalFrame

def Scalar : NStmt → Bool
  | .skip | .declare _ _ _ | .assign _ _ _ | .ret _ | .check _ => true
  | _ => false

theorem scalar_frame (stmt : NStmt) (s : NState) (out : NStep)
    (form : Scalar stmt = true) (actual : stmt.run s = some out) : FrameSame s.frame out.state.frame := by
  cases stmt with
  | skip =>
    have eq := Option.some.inj actual
    rw [← eq]
    exact ⟨rfl,rfl⟩
  | declare ty wr e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := Option.some.inj rest
    rw [← eq]
    exact expression_frame e s t v ran
  | assign slot ty e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨binding,cell⟩,_,rest⟩ := bind_some _ _ _ rest
    dsimp only at rest
    split at rest
    · obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
      have eq := Option.some.inj rest
      rw [← eq]
      exact expression_frame e s t v ran
    · simp at rest
  | ret e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    rw [← eq]
    exact expression_frame e s t v ran
  | check e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    dsimp only at rest
    split at rest
    · simp at rest
    · have eq := Option.some.inj rest
      rw [← eq]
      exact expression_frame e s t v ran
  | _ => simp [Scalar] at form

end Proofs.CppScalarFrame
