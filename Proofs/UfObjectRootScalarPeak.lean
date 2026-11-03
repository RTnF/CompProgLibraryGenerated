import Proofs.CppCompactScalarPeak
import Proofs.UfObjectHeapPeak

namespace Proofs.UfObjectRootScalarPeak
open Proofs.CppNestedProgram Proofs.VecExpr Proofs.VecWrite Proofs.StraightLine Proofs.QuotientFrame
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.DoublingNested Proofs.CppState
open Proofs.UfRootCall Proofs.CppCompactScalarPeak

def budget (s : NState) (prefixLength : Nat) : Nat := max s.scalars.peak (prefixLength+80-s.scalars.baseMemory)

theorem root_body_peak (s : NState) (vc : VCtx) (vec : List Int) (rank : Nat → Nat)
    (forest : Forest vec rank) (length : vec.length < 2147483648) (a : Nat) (inside : a < vec.length)
    (P : List Cell) (counter : Binding) (buffer : Buffer Value) (ty : vc.ty = i32)
    (permission : vc.wV = true ∧ vc.flag = true)
    (qs : QS s [] s.scalars.baseMemory s.scope
      (Proofs.UfFieldsRoot.fields P counter vec.length a).mem
      (Proofs.UfFieldsRoot.fields P counter vec.length a).bs
      (sl1 (Proofs.UfFieldsRoot.fields P counter vec.length a).bs.length))
    (frame : FW vc vec buffer 0 s.frame) (base : s.scalars.baseMemory ≤ P.length) (scope : vc.sc ≤ s.scope)
    (fuel : Nat) (step : NStep)
    (actual : Proofs.CppNestedProgram.runFuel fuel Proofs.UnionFindCandidateInstance.UnionFind_root.body s = .finished step) :
    step.state.scalars.peak ≤ budget s P.length := by
  obtain ⟨res,r,executed,returned,compressed,newForest,recursive,saved,cost,need,writes⟩ :=
    Proofs.UfFieldsRoot.body_correct P counter vec rank forest length a inside (rank a+2) (by omega)
  have run : pexecW vc.ty (rank a+2) Proofs.UnionFindCandidateInstance.UnionFind_root.body
      (Proofs.UfFieldsRoot.fields P counter vec.length a) vec = some res := by rw [ty]; exact executed
  have room : P.length+80 ≤ budget s P.length+s.scalars.baseMemory := by
    have bound := Nat.le_max_right s.scalars.peak (P.length+80-s.scalars.baseMemory)
    change P.length+80-s.scalars.baseMemory ≤ budget s P.length at bound
    omega
  apply actual_body_peak s vc true (fun _ => permission) _ (by decide) (rank a+2) _ vec res run buffer (budget s P.length)
    qs frame (Nat.le_max_left _ _) _ _ (by omega) scope fuel step actual
  · simpa [Proofs.UfFieldsRoot.fields,Proofs.VecShift.pad,Proofs.PrefixSumsCall.stI] using (show s.scalars.baseMemory ≤ P.length+2 by omega)
  · simp only [Proofs.UfFieldsRoot.fields,Proofs.VecShift.pad,Proofs.PrefixSumsCall.stI,List.length_append,List.length_cons,List.length_nil]
    omega

open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppMoveReceiverResolve
open Proofs.UfObjectTrace Proofs.CppMoveCallBindings Proofs.UfReceiverLayout Proofs.CppMoveReceiverLayout

-- The actual compact call result inherits the sharp body scalar bound.
theorem root_call_peak (s out : Context) (object : ObjectRef) (state : Proofs.UfObjectState.State s object)
    (a : Nat) (inside : a < state.data.items.length) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object (.root a) = .finished (out,result)) :
    ∃ prepared, prepareArguments s i32 Proofs.UnionFindCandidateInstance.UnionFind_root.parameters
      (Proofs.UfObjectCall.arguments s object state.receiver [(.literal i32 (a : Int),(a : Int))]) = some prepared ∧
      out.scalars.peak ≤ max (max s.scalars.peak
        (max prepared.scalars.peak ((receiverPrefix s).length+80-s.scalars.baseMemory)))
        (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length) := by
  have av := literal_valid s object state a inside
  have ready : Ready s i32 [(.literal i32 (a : Int),(a : Int))] := by
    intro expression value member
    rcases Prod.mk.inj (List.mem_singleton.mp member) with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,by simp [NExpr.denote,av]⟩
  obtain ⟨prepared,initial,vc,buffer,prep,compacted,qs,frame,ty,writable,flag,sc,current,base,scope⟩ :=
    Proofs.UfObjectCall.prepare s object state.receiver Proofs.UnionFindCandidateInstance.UnionFind_root
      [(.literal i32 (a : Int),(a : Int))] ready rfl state.readable state.unique state.covered state.allocations
      state.limit state.contexts
  have sameBuffer := Option.some.inj (current.symm.trans state.current)
  subst buffer
  have fields := qs_two initial (receiverPrefix s) state.receiver.counter.address state.receiver.size.value (a : Int) qs
  rw [state.size] at fields
  rw [invoke_state fuel s object state (.root a)] at actual
  obtain ⟨prepared2,initial2,step,after,prep2,compact2,body,breaking,finished,restored⟩ :=
    call_parts Proofs.UnionFindCandidateInstance.UnionFind_root fuel s out i32 _ result actual
  have samePrepared := Option.some.inj (prep.symm.trans prep2)
  subst prepared2
  have sameInitial := Option.some.inj (compacted.symm.trans compact2)
  subst initial2
  have scalar := root_body_peak initial vc state.data.items state.rank state.math.forest state.math.length a inside
    (receiverPrefix s) ⟨state.receiver.counter.address,true⟩ (Proofs.CppMoveFrame.box state.data) ty ⟨writable,flag⟩ fields
    frame (by rw [base]; exact state.baseline) (Nat.le_of_eq sc) fuel step body
  have counters := Proofs.CppMovePreparedCall.restored_finish_counters s out i32 i32 step.state after
    step.returned result finished restored state.covered
  have metadata := (compact_metadata (project prepared i32) initial compacted).2.2.1
  unfold budget at scalar
  rw [base,metadata] at scalar
  change step.state.scalars.peak ≤ max prepared.scalars.peak ((receiverPrefix s).length+80-s.scalars.baseMemory) at scalar
  refine ⟨prepared,prep,?_⟩
  rw [counters.1]
  clear * - scalar
  omega

end Proofs.UfObjectRootScalarPeak
