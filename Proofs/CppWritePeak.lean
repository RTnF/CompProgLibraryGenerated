import Proofs.CppWriteHeaders
import Proofs.CppScalarFrame
import Proofs.CppNoResizeScope

namespace Proofs.CppWritePeak
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.DynamicResultValid
open Proofs.CppEvalFrame

theorem frame_write_peak (f g : Frame) (reference : Reference) (value : Int)
    (actual : f.write reference value = some g) :
    g.state.storage.peak = max f.state.storage.peak (f.state.liveSpace+1-f.state.storage.baseSpace) := by
  unfold Frame.write at actual
  obtain ⟨writable,_,rest⟩ := bind_some _ _ _ actual
  split at rest
  · obtain ⟨⟨buffer,tag⟩,object,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,written,rest⟩ := bind_some _ _ _ rest
    have peak : result.peak = buffer.capacity+2 := by
      unfold writeRef at written
      split at written
      · have same := Option.some.inj written
        rw [← same]
      · simp at written
    unfold Frame.commit at rest
    rw [object] at rest
    dsimp only at rest
    split at rest
    · split at rest
      · have eq := Option.some.inj rest
        subst g
        change max f.state.storage.peak
          (f.state.liveSpace+(result.peak-(buffer.capacity+1))-f.state.storage.baseSpace) = _
        rw [peak]
        have temp : buffer.capacity+2-(buffer.capacity+1) = 1 := by omega
        rw [temp]
      · simp at rest
    · simp at rest
  · simp at rest

theorem stmt_write_peak (s : NState) (out : NStep) (container : Container) (ty : Ty) (index expression : NExpr)
    (actual : (NStmt.write container ty index expression).run s = some out) :
    out.state.frame.state.storage.peak = max s.frame.state.storage.peak
      (s.frame.state.liveSpace+1-s.frame.state.storage.baseSpace) := by
  unfold NStmt.run at actual
  obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
  obtain ⟨⟨b,owner⟩,rb,rest⟩ := bind_some _ _ _ rest
  obtain ⟨⟨c,pos⟩,rc,rest⟩ := bind_some _ _ _ rest
  obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
  obtain ⟨frame,written,rest⟩ := bind_some _ _ _ rest
  have before := (expression_frame expression (s.charge 0 (container.nodes+index.nodes+expression.nodes+3)) a x ra).trans
    ((container_frame container a b owner rb).trans (expression_frame index b c pos rc))
  have stateEq : c.frame.state = s.frame.state := before.1
  have peak := frame_write_peak c.frame frame reference x written
  have eq := Option.some.inj rest
  subst out
  change frame.state.storage.peak = _
  rw [peak,stateEq]


theorem retire_peak (f g : Frame) (scope : Nat)
    (fresh : ∀ owner, f.state.forest.context owner ≠ some scope)
    (actual : f.retireScope scope = some g) :
    g.state.storage.peak = max f.state.storage.peak (f.state.liveSpace-f.state.storage.baseSpace) := by
  unfold Frame.retireScope at actual
  obtain ⟨state,retired,rest⟩ := bind_some _ _ _ actual
  unfold State.retireScope at retired
  split at retired
  · dsimp only at retired
    split at retired
    · have eq := Option.some.inj retired
      subst state
      have eq := Option.some.inj rest
      subst g
      rw [Proofs.CppNestedScope.retired_fresh f.state scope fresh]
    · simp at retired
  · simp at retired

end Proofs.CppWritePeak
