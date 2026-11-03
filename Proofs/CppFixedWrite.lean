import Proofs.CppExprPrefix
import Proofs.CppWriteHeaders
import Proofs.CppReferenceHeaders

namespace Proofs.CppFixedWrite
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppExprPrefix Proofs.CppEvalFrame Proofs.DynamicResultValid

def Target (s : NState) (root : Nat) : Prop :=
  ∃ index binding, s.vectorSlot 0 = some index ∧ s.frame.bindings[index]? = some binding ∧ binding.owner = root

theorem target_prefix (s t : NState) (root : Nat) (target : Target s root) (prefixEq : Prefix s t) : Target t root := by
  obtain ⟨index,binding,slot,found,owner⟩ := target
  obtain ⟨extra,bindings⟩ := prefixEq.2
  have bound := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨index,binding,?_,?_,owner⟩
  · simpa only [NState.vectorSlot,prefixEq.1] using slot
  · rw [bindings]
    simpa only [List.getElem?_append_left bound] using found

theorem target_slots (s t : NState) (root : Nat) (target : Target s root)
    (bindings : t.frame.bindings = s.frame.bindings)
    (slots : ∃ extra, t.slots = s.slots++extra) : Target t root := by
  obtain ⟨index,binding,slot,found,owner⟩ := target
  obtain ⟨extra,slotsEq⟩ := slots
  have inside : 0 < s.slots.length := by
    by_cases inside : 0 < s.slots.length
    · exact inside
    have missing : s.slots[0]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp [NState.vectorSlot,missing] at slot
  have first : t.slots[0]? = s.slots[0]? := by rw [slotsEq]; exact List.getElem?_append_left inside
  refine ⟨index,binding,?_,?_,owner⟩
  · simpa only [NState.vectorSlot,first] using slot
  · rw [bindings]; exact found


theorem resolve_facts (f : Frame) (slot : Nat) (element : Element) (binding : Binding) (buffer : Buffer Value)
    (actual : f.resolve slot element = some (binding,buffer)) :
    f.bindings[slot]? = some binding ∧ buffer.owner = binding.owner := by
  unfold Frame.resolve at actual
  obtain ⟨b,found,rest⟩ := bind_some _ _ _ actual
  obtain ⟨owner,_,rest⟩ := bind_some _ _ _ rest
  obtain ⟨⟨buf,tag⟩,object,rest⟩ := bind_some _ _ _ rest
  obtain ⟨maximum,_,rest⟩ := bind_some _ _ _ rest
  try dsimp only at rest
  split at rest
  · rename_i checked
    obtain ⟨bindingEq,bufferEq⟩ := Prod.mk.inj (Option.some.inj rest)
    subst b
    subst buf
    have lookup := Proofs.CppWriteHeaders.object_lookup f owner element buffer tag object
    have valid : f.state.wellFormed = true := by
      unfold Frame.object at object
      split at object
      · assumption
      · simp at object
    obtain ⟨_,_,ownerEq,_⟩ := wellFormed_buffer f.state owner buffer valid lookup
    exact ⟨found,ownerEq.trans checked.1.symm⟩
  · simp at rest

theorem element_ref_owner (f : Frame) (slot : Nat) (ty : Ty) (index : Int) (reference : Reference) (binding : Binding)
    (found : f.bindings[slot]? = some binding) (actual : f.elementRef slot ty index = some reference) :
    reference.address.owner = binding.owner := by
  unfold Frame.elementRef at actual
  obtain ⟨⟨origin,buffer⟩,resolved,rest⟩ := bind_some _ _ _ actual
  obtain ⟨address,captured,rest⟩ := bind_some _ _ _ rest
  obtain ⟨originFound,owner⟩ := resolve_facts f slot (.integer ty) origin buffer resolved
  have same : origin = binding := Option.some.inj (originFound.symm.trans found)
  subst origin
  have eq := Option.some.inj rest
  subst reference
  unfold CppVector.elementRef at captured
  split at captured
  · have eq := Option.some.inj captured
    subst address
    exact owner
  · simp at captured

theorem frame_write_other (f g : Frame) (reference : Reference) (value : Int)
    (actual : f.write reference value = some g) (other : Nat) (different : other ≠ reference.address.owner) :
    g.state.storage.lookup other = f.state.storage.lookup other := by
  unfold Frame.write at actual
  obtain ⟨writable,_,rest⟩ := bind_some _ _ _ actual
  split at rest
  · obtain ⟨⟨buffer,tag⟩,object,rest⟩ := bind_some _ _ _ rest
    obtain ⟨result,_,rest⟩ := bind_some _ _ _ rest
    unfold Frame.commit at rest
    rw [object] at rest
    dsimp only at rest
    split at rest
    · split at rest
      · have eq := Option.some.inj rest
        subst g
        exact Proofs.CppNestedOps.updated_lookup_other f reference.address.owner other buffer result (Ne.symm different)
      · simp at rest
    · simp at rest
  · simp at rest

theorem write_local (s : NState) (out : NStep) (root : Nat) (ty : Ty) (index expression : NExpr)
    (target : Target s root)
    (actual : (NStmt.write (.local 0) ty index expression).run s = some out) :
    Target out.state root ∧ out.state.frame.bindings = s.frame.bindings ∧ out.state.slots = s.slots ∧
      ∀ other, other ≠ root → out.state.frame.state.storage.lookup other = s.frame.state.storage.lookup other := by
  unfold NStmt.run at actual
  obtain ⟨⟨a,x⟩,ra,rest⟩ := bind_some _ _ _ actual
  obtain ⟨⟨b,slot⟩,rb,rest⟩ := bind_some _ _ _ rest
  unfold Container.eval at rb
  obtain ⟨bindingIndex,slotA,rb⟩ := bind_some _ _ _ rb
  obtain ⟨bEq,slotEq⟩ := Prod.mk.inj (Option.some.inj rb)
  change a.charge 1 1 = b at bEq
  subst b
  subst slot
  obtain ⟨⟨c,pos⟩,rc,rest⟩ := bind_some _ _ _ rest
  obtain ⟨reference,captured,rest⟩ := bind_some _ _ _ rest
  obtain ⟨frame,written,rest⟩ := bind_some _ _ _ rest
  have pa := expression_prefix expression (s.charge 0 ((Container.local 0).nodes+index.nodes+expression.nodes+3)) a x ra
  have pc := expression_prefix index (a.charge 1 1) c pos rc
  have combined : Prefix s c := pa.trans pc
  obtain ⟨rootIndex,binding,rootSlot,rootFound,rootOwner⟩ := target_prefix s a root target pa
  have indexEq : rootIndex = bindingIndex := Option.some.inj (rootSlot.symm.trans slotA)
  subst rootIndex
  obtain ⟨extra,prefixC⟩ := pc.2
  change c.frame.bindings = a.frame.bindings++extra at prefixC
  have bound := (List.getElem?_eq_some_iff.mp rootFound).1
  have foundC : c.frame.bindings[bindingIndex]? = some binding := by
    rw [prefixC]
    simpa only [List.getElem?_append_left bound] using rootFound
  have addressOwner : reference.address.owner = root :=
    (element_ref_owner c.frame bindingIndex ty pos reference binding foundC captured).trans rootOwner
  have before := (expression_frame expression
    (s.charge 0 ((Container.local 0).nodes+index.nodes+expression.nodes+3)) a x ra).trans
      (expression_frame index (a.charge 1 1) c pos rc)
  have stateEq : c.frame.state = s.frame.state := before.1
  obtain ⟨_,_,bindings⟩ := Proofs.CppWriteHeaders.frame_write c.frame frame reference x written
  have eq := Option.some.inj rest
  subst out
  have restored : frame.bindings.take s.frame.bindings.length = s.frame.bindings := by
    rw [bindings]
    exact release_bindings s c combined
  have slots : c.slots = s.slots := combined.1
  refine ⟨?_,restored,slots,?_⟩
  · obtain ⟨i,b,slot,found,owner⟩ := target
    refine ⟨i,b,?_,?_,owner⟩
    · simpa only [NState.vectorSlot,NState.charge,NState.observe,NState.release,slots] using slot
    · exact (by change (frame.bindings.take s.frame.bindings.length)[i]? = some b; rw [restored]; exact found)
  · intro other different
    change frame.state.storage.lookup other = s.frame.state.storage.lookup other
    have untouched := frame_write_other c.frame frame reference x written other (by rwa [addressOwner])
    rw [stateEq] at untouched
    exact untouched


theorem scalar_full_frame (stmt : NStmt) (s : NState) (out : NStep)
    (form : Proofs.CppScalarFrame.Scalar stmt = true) (actual : stmt.run s = some out) : out.state.frame = s.frame ∧ ∃ extra, out.state.slots = s.slots++extra := by
  cases stmt with
  | skip =>
    have eq := Option.some.inj actual
    rw [← eq]
    exact ⟨rfl,[],by simp⟩
  | declare ty wr e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
    have eq := Option.some.inj rest
    rw [← eq]
    have frame := release_frame e s t v ran
    have slots := (expression_prefix e s t v ran).1
    refine ⟨frame,[.scalar t.scalars.bindings.length],?_⟩
    change t.slots++[.scalar t.scalars.bindings.length] = s.slots++[.scalar t.scalars.bindings.length]
    rw [slots]
  | assign slot ty e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    obtain ⟨⟨binding,cell⟩,_,rest⟩ := bind_some _ _ _ rest
    dsimp only at rest
    split at rest
    · obtain ⟨x,_,rest⟩ := bind_some _ _ _ rest
      have eq := Option.some.inj rest
      rw [← eq]
      exact ⟨release_frame e s t v ran,[],by
        have slots := (expression_prefix e s t v ran).1
        simpa only [NState.charge,NState.observe,NState.release,List.append_nil] using slots⟩
    · simp at rest
  | ret e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    have eq := Option.some.inj rest
    rw [← eq]
    exact ⟨release_frame e s t v ran,[],by
        have slots := (expression_prefix e s t v ran).1
        simpa only [NState.charge,NState.observe,NState.release,List.append_nil] using slots⟩
  | check e =>
    unfold NStmt.run at actual
    obtain ⟨⟨t,v⟩,ran,rest⟩ := bind_some _ _ _ actual
    dsimp only at rest
    split at rest
    · simp at rest
    · have eq := Option.some.inj rest
      rw [← eq]
      exact ⟨release_frame e s t v ran,[],by
        have slots := (expression_prefix e s t v ran).1
        simpa only [NState.charge,NState.observe,NState.release,List.append_nil] using slots⟩
  | _ => simp [Proofs.CppScalarFrame.Scalar] at form


theorem scalar_target (stmt : NStmt) (s : NState) (out : NStep) (root : Nat)
    (form : Proofs.CppScalarFrame.Scalar stmt = true) (target : Target s root)
    (actual : stmt.run s = some out) : Target out.state root ∧
      ∀ other, out.state.frame.state.storage.lookup other = s.frame.state.storage.lookup other := by
  obtain ⟨frame,slots⟩ := scalar_full_frame stmt s out form actual
  refine ⟨target_slots s out.state root target (congrArg Frame.bindings frame) slots,?_⟩
  intro other
  rw [frame]

end Proofs.CppFixedWrite
