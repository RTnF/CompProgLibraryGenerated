import Proofs.UfCopyPreserve
import Proofs.UfConstructedPeak

namespace Proofs.UfCopyPeak
open Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.UfCopyFields Proofs.UfCopyReceiver
open Proofs.CppVector Proofs.CppNestedVectorStore

-- The same resident increments as the ordinary UF constructor permit reuse
-- of its caller-to-receiver envelope lemma, with no argument-expression nodes.
theorem initial_components (s : NState) (buf : Buffer Value) (count n : Int)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length) :
    liveS (state s buf count n) = liveS s+4 ∧
    (state s buf count n).frame.bindings.length = s.frame.bindings.length+1 ∧
    (state s buf count n).scalars.peak = max s.scalars.peak (liveS s+4) ∧
    (state s buf count n).peak = max s.peak
      ((state s buf count n).scalars.peak+(state s buf count n).frame.state.storage.peak) := by
  refine ⟨?_,?_,?_,rfl⟩
  · simp only [state,fields,NState.observe,Proofs.CppState.State.observe,liveS,List.length_append,
      List.length_cons,List.length_nil]
    omega
  · simp [state,fields,NState.observe,Proofs.CppFrameCopy.copiedFrame]
  · simp only [state,fields,NState.observe,Proofs.CppState.State.observe,liveS,List.length_append,
      List.length_cons,List.length_nil,Nat.add_zero]
    congr 1
    omega

open Proofs.UfReceiverState Proofs.UfBalancedReceiver Proofs.UfReceiverTrace
open Proofs.UfConstructedPeak Proofs.CppNestedCall
open Proofs.DoublingNested (i32)

theorem copy_envelopes (s receiver : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank : Nat → Nat) (strong : Strong s layout ps count rank)
    (actual : copyReceiver s layout = some (receiver,layoutOf s)) :
    max receiver.scalars.peak (Proofs.UfUniformScalarPeak.budget receiver) ≤ scalarEnvelope s 0 ∧
    Proofs.CppStoragePeak.bound receiver ≤ storageEnvelope s ps.length ∧
    receiver.peak ≤ envelope s ps.length 0 ∧
    liveS receiver = liveS s+4 ∧ receiver.frame.state.liveSpace = s.frame.state.liveSpace+ps.length+1 := by
  obtain ⟨buf,cb,nb,inv⟩ := strong.1
  obtain ⟨resolved,_,_⟩ := Proofs.CppNestedRows.resolve_vroot s.frame layout.vectorBinding layout.owner layout.scope
    i32 true true buf inv.ok.binding inv.ok.valid inv.ok.vtag inv.ok.vfound inv.ok.lengths inv.ok.flag (fun _ => rfl)
  have expected := copy_receiver_runs s layout count ps.length cb nb _ buf inv.ok.slot inv.ok.lengths resolved inv.countCell inv.nCell
  have same : receiver = state s buf count ps.length := congrArg Prod.fst (Option.some.inj (actual.symm.trans expected))
  subst receiver
  have parts := initial_components s buf count ps.length inv.ok.base
  have cost := state_cost s buf count ps.length (wellFormed_parts s.frame.state inv.ok.valid).1
  have size : buf.items.length = ps.length := by rw [inv.items,List.length_map]
  have resident : (state s buf count ps.length).frame.state.liveSpace = s.frame.state.liveSpace+ps.length+1 := by
    simpa only [size] using cost.2.1
  have scalar : (state s buf count ps.length).scalars.peak ≤
      max s.scalars.peak (liveS s+s.frame.bindings.length+0+12) := by
    rw [parts.2.2.1]
    exact max_le_max (Nat.le_refl _) (by omega)
  have storage : (state s buf count ps.length).frame.state.storage.peak ≤ storageEnvelope s ps.length := by
    simpa only [storageEnvelope,size] using Nat.le_of_eq cost.2.2.2.2.2
  have envs := receiver_envelopes s (state s buf count ps.length) ps.length 0 scalar storage parts.1 resident rfl parts.2.1
  refine ⟨envs.1,envs.2,?_,parts.1,resident⟩
  rw [parts.2.2.2]
  unfold envelope
  apply max_le_max (Nat.le_refl _)
  exact Nat.add_le_add (Nat.le_trans (Nat.le_max_left _ _) envs.1) storage

theorem actual_history_peak (s receiver out : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank : Nat → Nat) (fuels : List Nat) (ops : List Operation) (answers : List Int)
    (strong : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length)
    (copied : copyReceiver s layout = some (receiver,layoutOf s))
    (actual : runCalls fuels ops receiver (layoutOf s) = .finished (out,answers)) :
    out.scalars.peak ≤ scalarEnvelope s 0 ∧ out.frame.state.storage.peak ≤ storageEnvelope s ps.length ∧
    out.peak ≤ envelope s ps.length 0 := by
  have both := actual_copy_strong s receiver layout (layoutOf s) ps count rank strong copied
  have bounds := copy_envelopes s receiver layout ps count rank strong copied
  obtain ⟨buf,cb,nb,inv⟩ := both.2.2.1
  have scalar := Proofs.UfUniformScalarPeak.actual_calls_peak fuels ops receiver (layoutOf s) out answers ps count rank both.2.2 allowed actual
  have storage := Proofs.UfUniformStoragePeak.actual_calls fuels ops receiver (layoutOf s) out answers inv.ok.strict actual
  have outer := Proofs.UfUniformPeak.actual_calls_peak fuels ops receiver (layoutOf s) out answers ps count rank both.2.2 allowed actual
  refine ⟨Nat.le_trans scalar bounds.1,Nat.le_trans storage bounds.2.1,?_⟩
  have components : Proofs.UfUniformPeak.components receiver ≤ scalarEnvelope s 0+storageEnvelope s ps.length :=
    Nat.add_le_add bounds.1 bounds.2.1
  exact Nat.le_trans outer (max_le bounds.2.2.1 (Nat.le_trans components (Nat.le_max_right _ _)))

theorem copy_history (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (ops : List Operation) (strong : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ receiver fuels out vec nextCount nextRank answers,
      copyReceiver s layout = some (receiver,layoutOf s) ∧
      runCalls fuels ops receiver (layoutOf s) = .finished (out,answers) ∧
      Strong out layout ps count rank ∧ Strong out (layoutOf s) vec nextCount nextRank ∧
      vec.length = ps.length ∧ fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ps.length+4+ops.length*Proofs.UfTraceWork.budget ps.length ∧
      liveS out = liveS s+4 ∧ out.frame.state.liveSpace = s.frame.state.liveSpace+ps.length+1 ∧
      Proofs.CppCallFrame.CallEffects receiver out ∧
      (∀ slot ty binding cell, s.scalarCell slot ty = some (binding,cell) → out.scalarCell slot ty = some (binding,cell)) ∧
      (∀ reference value, s.frame.read reference = some value → out.frame.read reference = some value) ∧
      out.scalars.peak ≤ scalarEnvelope s 0 ∧ out.frame.state.storage.peak ≤ storageEnvelope s ps.length ∧
      out.peak ≤ envelope s ps.length 0 := by
  obtain ⟨receiver,fuels,out,vec,nextCount,nextRank,answers,copied,ran,old,new,len,fl,al,work,cells,reads⟩ :=
    Proofs.UfCopyPreserve.copy_calls_both ops s layout ps count rank strong allowed
  have both := actual_copy_strong s receiver layout (layoutOf s) ps count rank strong copied
  obtain ⟨buf,cb,nb,inv⟩ := both.2.2.1
  have effects := Proofs.UfReceiverMetadata.actual_calls fuels ops receiver (layoutOf s) out answers inv.ok.strict ran
  have bounds := copy_envelopes s receiver layout ps count rank strong copied
  have peaks := actual_history_peak s receiver out layout ps count rank fuels ops answers strong allowed copied ran
  exact ⟨receiver,fuels,out,vec,nextCount,nextRank,answers,copied,ran,old,new,len,fl,al,work,
    effects.scalarLive.trans bounds.2.2.2.1,effects.headers.live.trans bounds.2.2.2.2,
    effects,cells,reads,peaks.1,peaks.2.1,peaks.2.2⟩

end Proofs.UfCopyPeak
