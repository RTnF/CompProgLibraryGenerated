import Proofs.CppEvalFrame

namespace Proofs.CppWriteHeaders
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.DynamicResultValid
open Proofs.CppBufferHeaders Proofs.CppEvalFrame

theorem object_lookup (f : Frame) (owner : Nat) (ty : Proofs.CppVectorOwnership.Element)
    (buffer : Buffer Value) (tag : Proofs.CppVectorOwnership.Tag)
    (actual : f.object owner ty = some (buffer,tag)) : f.state.storage.lookup owner = some buffer := by
  unfold Frame.object at actual
  split at actual
  · obtain ⟨found,lookup,rest⟩ := bind_some _ _ _ actual
    obtain ⟨foundTag,_,rest⟩ := bind_some _ _ _ rest
    split at rest
    · have eq := congrArg Prod.fst (Option.some.inj rest)
      change found = buffer at eq
      rwa [eq] at lookup
    · simp at rest
  · simp at actual

theorem frame_write (f g : Frame) (reference : Reference) (value : Int)
    (actual : f.write reference value = some g) :
    SameHeaders f.state g.state ∧ g.rootWritable = f.rootWritable ∧ g.bindings = f.bindings := by
  unfold Frame.write at actual
  obtain ⟨writable,_,rest⟩ := bind_some _ _ _ actual
  split at rest
  · obtain ⟨⟨buffer,tag⟩,object,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,written,rest⟩ := bind_some _ _ _ rest
    have header : signature result.buffer = signature buffer := by
      unfold writeRef at written
      split at written
      · have same := Option.some.inj written
        rw [← same]
        simp [signature]
      · simp at written
    have found := object_lookup f reference.address.owner (.integer reference.element) buffer tag object
    have bound := lookup_bound f.state.storage reference.address.owner buffer found
    unfold Frame.commit at rest
    rw [object] at rest
    dsimp only at rest
    split at rest
    · split at rest
      · have eq := Option.some.inj rest
        subst g
        exact ⟨updated_headers f reference.address.owner buffer result bound found header,rfl,rfl⟩
      · simp at rest
    · simp at rest
  · simp at rest

theorem stmt_write (s out : NState) (container : Container) (ty : Ty) (index expression : NExpr)
    (actual : (NStmt.write container ty index expression).run s = some ⟨out,none,false⟩) :
    SameHeaders s.frame.state out.frame.state ∧ out.frame.rootWritable = s.frame.rootWritable := by
  unfold NStmt.run at actual
  obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
  obtain ⟨⟨b,owner⟩,rb,rest⟩ := bind_some _ _ _ rest
  obtain ⟨⟨c,pos⟩,rc,rest⟩ := bind_some _ _ _ rest
  obtain ⟨reference,_,rest⟩ := bind_some _ _ _ rest
  obtain ⟨frame,written,rest⟩ := bind_some _ _ _ rest
  have before := (expression_frame expression (s.charge 0 (container.nodes+index.nodes+expression.nodes+3)) a x ra).trans
    ((container_frame container a b owner rb).trans (expression_frame index b c pos rc))
  have stateEq : c.frame.state = s.frame.state := before.1
  obtain ⟨headers,rw,_⟩ := frame_write c.frame frame reference x written
  have eq := congrArg NStep.state (Option.some.inj rest)
  change _ = out at eq
  subst out
  constructor
  · change SameHeaders s.frame.state frame.state
    rw [← stateEq]
    exact headers
  · exact rw.trans before.2

end Proofs.CppWriteHeaders
