import Proofs.UfCopyReceiver
import Proofs.UfReceiverValues
import Proofs.UfScalarTrace

namespace Proofs.UfCopyPreserve
open Proofs.CppScalar Proofs.CppVector Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppCallFrame Proofs.UfReceiverState Proofs.UfFindCall
open Proofs.DoublingNested (i32)
open Proofs.DynamicResultValid

-- Reuse an old receiver's exact buffer and cells after a call on another
-- object. The scalar non-alias conditions still have to be proved per call.
theorem Inv.after_other (s out : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank : Nat → Nat) (buf : Buffer Value) (cb nb : Proofs.CppState.Binding)
    (inv : Inv s layout ps count rank buf cb nb) (effects : CallEffects s out)
    (valid : out.frame.state.wellFormed = true)
    (buffer : out.frame.state.storage.lookup layout.owner = some buf)
    (countCell : out.scalarCell layout.countSlot i32 = some (cb,⟨i32,count⟩))
    (nCell : out.scalarCell layout.nSlot i32 = some (nb,⟨i32,ps.length⟩)) :
    Inv out layout ps count rank buf cb nb := by
  refine ⟨?_,inv.items,inv.bufferValid,inv.limit,inv.owner,inv.math,countCell,inv.writable,nCell,inv.different⟩
  refine ⟨valid,?_,?_,?_,buffer,?_,?_,?_,?_⟩
  · simpa only [NState.vectorSlot,effects.slots] using inv.ok.slot
  · rw [effects.vectorBindings]
    exact inv.ok.binding
  · rw [effects.headers.forest]
    exact inv.ok.vtag
  · rw [effects.flags,effects.headers.forest]
    exact inv.ok.lengths
  · rw [effects.flags]
    exact inv.ok.flag
  · intro owner scope found
    rw [effects.headers.forest] at found
    rw [effects.scopedState]
    exact inv.ok.strict owner scope found
  · rw [effects.base,effects.memoryLength]
    exact inv.ok.base

theorem other_buffer (fuels : List Nat) (ops : List Proofs.UfReceiverTrace.Operation)
    (s out : NState) (target : Layout) (answers : List Int) (owner : Nat) (buf : Buffer Value)
    (selected : Proofs.UfReceiverValues.Selected s target)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : Proofs.UfReceiverTrace.runCalls fuels ops s target = .finished (out,answers))
    (different : owner ≠ target.owner) (found : s.frame.state.storage.lookup owner = some buf) :
    out.frame.state.storage.lookup owner = some buf := by
  rw [Proofs.UfReceiverValues.actual_calls fuels ops s target out answers selected contexts actual owner different]
  exact found

open Proofs.UfBalancedReceiver Proofs.UfCopyFields Proofs.UfCopyReceiver

theorem calls_keep_inv (ops : List Proofs.UfReceiverTrace.Operation) (s : NState) (target old : Layout)
    (ps oldPs : List Int) (count oldCount : Int) (rank oldRank : Nat → Nat)
    (buf : Buffer Value) (cb nb targetCb : Proofs.CppState.Binding)
    (inv : Inv s old oldPs oldCount oldRank buf cb nb)
    (strong : Strong s target ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length)
    (counter : s.scalarCell target.countSlot i32 = some (targetCb,⟨i32,count⟩))
    (owners : old.owner ≠ target.owner) (counts : cb.address ≠ targetCb.address)
    (ns : nb.address ≠ targetCb.address) :
    ∃ fuels out vec nextCount nextRank answers,
      Proofs.UfReceiverTrace.runCalls fuels ops s target = .finished (out,answers) ∧
      Strong out target vec nextCount nextRank ∧ Inv out old oldPs oldCount oldRank buf cb nb ∧
      vec.length = ps.length ∧ fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧
      (∀ slot ty binding cell, s.scalarCell slot ty = some (binding,cell) → binding.address ≠ targetCb.address →
        out.scalarCell slot ty = some (binding,cell)) ∧
      ∀ reference : Reference, reference.address.owner ≠ target.owner → out.frame.read reference = s.frame.read reference := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,post,len,fl,al,work,effects,cells⟩ :=
    Proofs.UfScalarTrace.calls_work_other ops s target ps count rank targetCb strong allowed counter
  obtain ⟨targetBuf,targetCount,targetN,targetInv⟩ := strong.1
  obtain ⟨nextBuf,nextCb,nextNb,nextInv⟩ := post.1
  have buffer := other_buffer fuels ops s out target answers old.owner buf
    (Proofs.UfReceiverValues.represents_selected s target ps count rank strong.1) targetInv.ok.strict ran owners inv.ok.vfound
  have kept := Inv.after_other s out old oldPs oldCount oldRank buf cb nb inv effects nextInv.ok.valid buffer
    (cells _ _ cb _ inv.countCell counts) (cells _ _ nb _ inv.nCell ns)
  have reads := Proofs.UfReceiverValues.actual_calls_reads fuels ops s target out answers
    (Proofs.UfReceiverValues.represents_selected s target ps count rank strong.1)
    targetInv.ok.valid nextInv.ok.valid targetInv.ok.strict ran
  exact ⟨fuels,out,vec,nextCount,nextRank,answers,ran,post,kept,len,fl,al,work,cells,reads⟩

theorem read_bound (f : Frame) (reference : Reference) (value : Int) (actual : f.read reference = some value) :
    reference.address.owner < f.state.storage.objects.length := by
  unfold Frame.read at actual
  obtain ⟨_,_,rest⟩ := bind_some _ _ _ actual
  obtain ⟨⟨buffer,tag⟩,object,_⟩ := bind_some _ _ _ rest
  have found := Proofs.CppWriteHeaders.object_lookup f reference.address.owner (.integer reference.element) buffer tag object
  exact Proofs.CppVectorStore.lookup_bound f.state.storage reference.address.owner buffer found

theorem copy_calls_both (ops : List Proofs.UfReceiverTrace.Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat) (strong : Strong s layout ps count rank)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ initial fuels out vec nextCount nextRank answers,
      copyReceiver s layout = some (initial,layoutOf s) ∧
      Proofs.UfReceiverTrace.runCalls fuels ops initial (layoutOf s) = .finished (out,answers) ∧
      Strong out layout ps count rank ∧ Strong out (layoutOf s) vec nextCount nextRank ∧
      vec.length = ps.length ∧ fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ps.length+4+ops.length*Proofs.UfTraceWork.budget ps.length ∧
      (∀ slot ty binding cell, s.scalarCell slot ty = some (binding,cell) → out.scalarCell slot ty = some (binding,cell)) ∧
      ∀ reference value, s.frame.read reference = some value → out.frame.read reference = some value := by
  obtain ⟨buf,cb,nb,inv⟩ := strong.1
  let initial := state s buf count ps.length
  have oldInv : Inv initial layout ps count rank buf cb nb :=
    ⟨old_ok s layout ps count rank buf cb nb inv,inv.items,inv.bufferValid,inv.limit,inv.owner,
      inv.math,fields_old_scalar s _ count ps.length _ _ cb _ inv.countCell,inv.writable,
      fields_old_scalar s _ count ps.length _ _ nb _ inv.nCell,inv.different⟩
  have newStrong : Strong initial (layoutOf s) ps count rank :=
    ⟨new_represents s layout ps count rank buf cb nb inv,strong.2⟩
  have counter := fields_count s (Proofs.CppFrameCopy.copiedFrame s.frame buf i32 s.scope true) count ps.length
    (scalar_valid s layout.countSlot i32 cb ⟨i32,count⟩ inv.countCell)
  have ownerBound := Proofs.CppVectorStore.lookup_bound s.frame.state.storage layout.owner buf inv.ok.vfound
  obtain ⟨_,_,_,countFound,_⟩ := Proofs.ExtremaCall.scalarCell_facts inv.countCell
  obtain ⟨_,_,_,nFound,_⟩ := Proofs.ExtremaCall.scalarCell_facts inv.nCell
  have countBound := (List.getElem?_eq_some_iff.mp countFound).1
  have nBound := (List.getElem?_eq_some_iff.mp nFound).1
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,post,kept,len,fl,al,work,cells,reads⟩ :=
    calls_keep_inv ops initial (layoutOf s) layout ps ps count count rank rank buf cb nb
      ⟨s.scalars.memory.length,true⟩ oldInv newStrong allowed counter
      (by simp only [layoutOf]; omega) (by dsimp; omega) (by dsimp; omega)
  obtain ⟨resolved,_,_⟩ := Proofs.CppNestedRows.resolve_vroot s.frame layout.vectorBinding layout.owner layout.scope
    i32 true true buf inv.ok.binding inv.ok.valid inv.ok.vtag inv.ok.vfound inv.ok.lengths inv.ok.flag (fun _ => rfl)
  have cost := (state_cost s buf count ps.length (wellFormed_parts s.frame.state inv.ok.valid).1).1
  have size : buf.items.length = ps.length := by rw [inv.items,List.length_map]
  rw [size] at cost
  refine ⟨initial,fuels,out,vec,nextCount,nextRank,answers,
    copy_receiver_runs s layout count ps.length cb nb _ buf inv.ok.slot inv.ok.lengths resolved inv.countCell inv.nCell,
    ran,⟨⟨buf,cb,nb,kept⟩,strong.2⟩,post,len,fl,al,?_,?_,?_⟩
  · change out.work ≤ (state s buf count ps.length).work+_ at work
    rw [cost] at work
    exact work
  · intro slot ty binding cell found
    obtain ⟨_,_,_,memory,_⟩ := Proofs.ExtremaCall.scalarCell_facts found
    have bound := (List.getElem?_eq_some_iff.mp memory).1
    exact cells slot ty binding cell (fields_old_scalar s _ count ps.length slot ty binding cell found) (by dsimp; omega)
  · intro reference value found
    have bound := read_bound s.frame reference value found
    have different : reference.address.owner ≠ (layoutOf s).owner := by simp only [layoutOf]; omega
    rw [reads reference different]
    exact Proofs.CppFrameExtension.read_kept s.frame initial.frame
      (Proofs.CppFrameCopy.copied_frame_extends s.frame buf i32 s.scope true inv.ok.valid inv.ok.lengths
        (by decide +kernel) inv.bufferValid) reference value found

end Proofs.UfCopyPreserve
