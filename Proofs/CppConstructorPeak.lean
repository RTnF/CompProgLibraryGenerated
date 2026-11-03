import Proofs.CppConstructorWork
import Proofs.CppConstructionFootprint

namespace Proofs.CppConstructorPeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.CppVectorOwnership
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState Proofs.DynamicResultValid
open Proofs.CppConstructorFinish

-- These are bounds in the checked abstract cell model, not measured bytes.
theorem scalar_peak (st next : Proofs.DynamicOwnedState.State) (s t : NState) (real : Realizes st s) (stmt : NStmt)
    (form : Proofs.DynamicStmtAuto.ScalarForm stmt)
    (pureRun : Proofs.DynamicOwnedControl.primitive stmt st = some ⟨next,none,false⟩)
    (actual : stmt.run s = some ⟨t,none,false⟩) :
    t.peak ≤ max s.peak (max s.scalars.peak
      (Proofs.CppNestedEval.liveS s+Proofs.DynamicScalarSound.tempBound stmt)+s.frame.state.storage.peak) := by
  cases stmt <;> try {simp [Proofs.DynamicStmtAuto.ScalarForm] at form}
  all_goals
    simp only [Proofs.DynamicOwnedControl.primitive] at pureRun
    obtain ⟨result,scalar,_⟩ := bind_some _ _ _ pureRun
    obtain ⟨out,ran,matched,ret,br,work,peak⟩ := Proofs.DynamicOwnedScalar.sound st s real _ form result scalar
    have same := Option.some.inj (ran.symm.trans actual)
    rw [same] at peak
    exact peak

theorem fill_peak (st : Proofs.DynamicOwnedState.State) (s t : NState) (real : Realizes st s)
    (ty : Ty) (wr : Bool) (count value : NExpr) (n x : Int)
    (countPure : denote st.params st.core.locals st.core.contents count = some n)
    (valuePure : denote st.params st.core.locals st.core.contents value = some x)
    (nonnegative : 0 ≤ n) (supported : Proofs.CppVectorBindings.supported ty)
    (limit : n.toNat ≤ Proofs.CppVectorBindings.sizeLimit ty) (accepted : ty.valid x = true)
    (actual : (NStmt.fillVector ty wr count value).run s = some ⟨t,none,false⟩) :
    t.peak ≤ max s.peak (max s.scalars.peak
      (Proofs.CppNestedEval.liveS s+2*count.nodes+2*value.nodes)+
      max s.frame.state.storage.peak (s.frame.state.liveSpace+(n.toNat+2)-s.frame.state.storage.baseSpace)) := by
  obtain ⟨h,m,family,erased⟩ := real.data.heap
  have before : Proofs.DynamicRealizes.Realizes st.params st.core.locals (eraseHeap h) s := by rw [erased]; exact real.data
  obtain ⟨out,ran,_,_,_,_,peak,_⟩ := Proofs.DynamicConstructFill.sound_full st.params h m st.core.locals s family before
    ty wr count value n x (by rw [erased]; exact countPure) (by rw [erased]; exact valuePure)
    nonnegative supported limit accepted
  have same := congrArg NStep.state (Option.some.inj (ran.symm.trans actual))
  change out = t at same
  rwa [same] at peak

theorem scalarBindings_length (start : Nat) (values : List ScalarValue) :
    (scalarBindings start values).length = values.length := by
  induction values generalizing start with
  | nil => rfl
  | cons value values ih => simp [scalarBindings,ih]

theorem empty_peak (s t : NState) (ty : Ty) (wr : Bool)
    (actual : (NStmt.declareVector ty wr).run s = some ⟨t,none,false⟩) :
    t.peak = max s.peak (max s.scalars.peak (Proofs.CppNestedEval.liveS s)+
      max s.frame.state.storage.peak (s.frame.state.liveSpace+1-s.frame.state.storage.baseSpace)) := by
  unfold NStmt.run at actual
  obtain ⟨next,allocated,rest⟩ := bind_some _ _ _ actual
  obtain ⟨pair,bound,same⟩ := bind_some _ _ _ rest
  obtain ⟨frame,index⟩ := pair
  have equal := congrArg NStep.state (Option.some.inj same)
  change _ = t at equal
  subst t
  obtain ⟨_,_,nextEq⟩ := Proofs.CppNestedConstruct.declareVector_inv s.frame.state ty s.scope next allocated
  obtain ⟨frameEq,_⟩ := Proofs.CppConstructionFootprint.bind_exact _ frame s.frame.state.storage.objects.length
    (.integer ty) s.scope wr index bound
  simp only [NState.charge,NState.observe,Proofs.CppState.State.observe,Proofs.CppNestedEval.liveS,
    frameEq,nextEq,Nat.add_zero]

-- Restoring k fields installs k cells and k scalar bindings; previous caller
-- cells are retained. The constructor's argument/local cells are discarded.
theorem restored_live (caller callee : NState) (frame : Frame) (binding : Binding)
    (values : List ScalarValue)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    Proofs.CppNestedEval.liveS (restored caller callee frame binding values) =
      Proofs.CppNestedEval.liveS caller+2*values.length := by
  simp only [restored,NState.observe,Proofs.CppState.State.observe,Proofs.CppNestedEval.liveS,
    List.length_append,List.length_take,List.length_map,scalarBindings_length,Nat.min_eq_left fits]
  omega

theorem restored_peak (caller callee : NState) (frame : Frame) (binding : Binding)
    (values : List ScalarValue)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    (restored caller callee frame binding values).peak =
      max (max caller.peak callee.peak)
        (max (max caller.scalars.peak callee.scalars.peak)
          (Proofs.CppNestedEval.liveS caller+2*values.length)+frame.state.storage.peak) := by
  have live := restored_live caller callee frame binding values fits baseline
  change (restored caller callee frame binding values).peak = _
  simp only [restored,NState.observe,Proofs.CppState.State.observe,Proofs.CppNestedEval.liveS,
    List.length_append,List.length_take,List.length_map,scalarBindings_length,Nat.min_eq_left fits] at live ⊢
  omega

theorem finish_peak (caller callee out : NState) (vslot : Nat) (element : Element)
    (fields : List ScalarField) (values : List ScalarValue) (object : ObjectRef)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (captured : captureAll callee fields = some values)
    (actual : Proofs.CppConstructorFinish.finish caller callee vslot element fields = some (out,object)) :
    out.peak = max (max caller.peak callee.peak)
      (max (max caller.scalars.peak callee.scalars.peak)
        (Proofs.CppNestedEval.liveS caller+2*values.length)+out.frame.state.storage.peak) := by
  unfold Proofs.CppConstructorFinish.finish at actual
  split at actual
  · rename_i guarded
    obtain ⟨index,_,rest⟩ := bind_some _ _ _ actual
    obtain ⟨binding,_,rest⟩ := bind_some _ _ _ rest
    split at rest
    · obtain ⟨actualValues,found,rest⟩ := bind_some _ _ _ rest
      have valuesEq : actualValues = values := Option.some.inj (found.symm.trans captured)
      subst actualValues
      obtain ⟨moved,_,rest⟩ := bind_some _ _ _ rest
      obtain ⟨retired,_,same⟩ := bind_some _ _ _ rest
      have eq := (Prod.mk.inj (Option.some.inj same)).1
      subst out
      exact restored_peak caller callee retired binding values guarded.2.1 baseline
    · simp at rest
  · simp at actual

end Proofs.CppConstructorPeak
