import Proofs.DynamicFlatFamily

namespace Proofs.DynamicFlatAppend
open Proofs.CppScalar Proofs.CppVector Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedStmt Proofs.CppNestedEval Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicContents
open Proofs.CppNestedVectorStore (Value)

-- The logical contents omit capacity. Available keeps the actual max-size
-- condition separate from successful lookup and value evaluation.
def run (slot : Nat) (ty : Ty) (value : NExpr) (st : DynamicOwnedState.State) : Option DynamicOwnedState.State := do
  let p ← DynamicStmt.mutableRoot st.params st.core slot (.integer ty)
  let x ← denote st.params st.core.locals st.core.contents value
  let .flat t sc values ← st.core.contents p.owner | none
  if t = ty ∧ ty.valid x = true then
    some {st with core := {st.core with contents := putContents st.core.contents p.owner (.flat t sc (values ++ [x]))}}
  else none

def Available (st : DynamicOwnedState.State) (s : NState) (slot : Nat) (ty : Ty) : Prop :=
  ∀ p, DynamicStmt.mutableRoot st.params st.core slot (.integer ty) = some p → DynamicAppendAuto.RootRoom s p.owner

theorem execute (st : DynamicOwnedState.State) (s : NState) (real : DynamicOwnedState.Realizes st s)
    (slot : Nat) (ty : Ty) (p : Parameter)
    (mutable : DynamicStmt.mutableRoot st.params st.core slot (.integer ty) = some p)
    (sc : Nat) (values : List Int) (lookup : st.core.contents p.owner = some (.flat ty sc values))
    (value : NExpr) (x : Int) (valuePure : denote st.params st.core.locals st.core.contents value = some x)
    (accepted : ty.valid x = true) (old : Buffer Value)
    (found : s.frame.state.storage.lookup p.owner = some old) (room : old.items.length < old.limit) :
    ∃ (r : Result Value Unit) (out : NState),
      (NStmt.append (.local slot) ty value).run s = some ⟨out,none,false⟩ ∧
      DynamicOwnedState.Realizes {st with core := {st.core with contents := putContents st.core.contents p.owner (.flat ty sc (values ++ [x]))}} out ∧
      out.work+CppVectorGrowth.potential r.buffer ≤ s.work+2*value.nodes+7+CppVectorGrowth.potential old ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveS s+2*value.nodes+4)+out.frame.state.storage.peak) ∧
      out.frame.state.storage.lookup p.owner = some r.buffer ∧
      r.buffer.limit = old.limit ∧ r.buffer.items = old.items ++ [.integer x] := by
  obtain ⟨location,selected,writable,maximum,_,_⟩ := DynamicAppendSound.mutable_found st.params st.core slot _ p mutable
  obtain ⟨heap,m,family,he⟩ := real.data.heap
  have hv := DynamicFlatSound.flat_lift heap p.owner ty sc values (by rw [he]; exact lookup)
  let start := s.charge 0 ((Container.local slot).nodes+value.nodes+2)
  let t1 := start.charge 1 1
  have containerRun : (Container.local slot).eval start = some (t1,p.slot) :=
    eval_local start slot p.slot (by simpa [NState.vectorSlot,start] using DynamicSizeSound.vector_slot st.params st.core.locals st.core.contents s real.data slot p.slot location)
  have firstGood := (GoodF.charge s 0 ((Container.local slot).nodes+value.nodes+2)).trans (GoodF.charge start 1 1)
  have real1 := DynamicExprCompose.in_extension st.params st.core.locals st.core.contents s t1 real.data
    (Ext.of_goodF (extra := []) firstGood (by simp [t1,start]))
  obtain ⟨_,t2,extra,ev⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) x valuePure) t1 real1
  have good := firstGood.trans ev.2.1
  have allBindings : t2.frame.bindings = s.frame.bindings ++ extra := by simpa [t1,start] using ev.2.2
  have family2 := family.transport t2.frame good.1 good.2.1 (by
    intro q hq
    rw [allBindings,List.getElem?_append_left (List.getElem?_eq_some_iff.mp (family.bindings q hq)).1]
    exact family.bindings q hq)
  obtain ⟨r,appended,post,amort,_,limit,items⟩ := DynamicFlatFamily.append family2 p (List.mem_of_find?_eq_some selected) ty sc values hv writable maximum old (by rw [good.1]; exact found) x accepted room
  let frame := t2.frame.updated p.owner old r
  let out := (({t2 with frame := frame} : NState).release s).charge 1 1
  have after : Family st.params (put heap p.owner (.flat ty sc (values ++ [x]))) out.frame (resources frame) :=
    post.rebind _ (by
      intro q hq
      change (t2.frame.bindings.take s.frame.bindings.length)[q.slot]? = _
      rw [allBindings,List.take_left]
      exact family.bindings q hq)
  obtain ⟨state,rights,slots,scope,memory,bindings,base,lower,upper,pl,pu,ql,qu⟩ := good
  have snapshotOut : snapshot out = st.core.locals := by
    have same : snapshot out = snapshot s := by simp [out,snapshot,NState.release,memory,bindings,slots]
    exact same.trans real.data.locals
  have erased : eraseHeap (put heap p.owner (.flat ty sc (values ++ [x])) ) = putContents st.core.contents p.owner (.flat ty sc (values ++ [x])) := by rw [erase_put,he]; rfl
  have data : DynamicRealizes.Realizes st.params st.core.locals (putContents st.core.contents p.owner (.flat ty sc (values ++ [x]))) out := ⟨snapshotOut,_,_,after,erased⟩
  have count : out.frame.state.storage.objects.length = st.nextOwner := by
    change (t2.frame.state.storage.objects.set p.owner (some r.buffer)).length = _
    rw [List.length_set,state,real.owner]
  have bindCount : out.frame.bindings.length = st.nextBinding := by
    change (t2.frame.bindings.take s.frame.bindings.length).length = _
    rw [allBindings,List.take_left,real.binding]
  have stored : out.frame.state.storage.lookup p.owner = some r.buffer := by
    exact Proofs.CppNestedOps.updated_lookup_self t2.frame p.owner old r
      (Proofs.CppVectorStore.lookup_bound t2.frame.state.storage p.owner old (by rw [state]; exact found))
  have oldPeak : s.frame.state.storage.peak ≤ frame.state.storage.peak := by
    change s.frame.state.storage.peak ≤ max t2.frame.state.storage.peak _
    rw [state]; exact Nat.le_max_left _ _
  have scalarPeak : out.scalars.peak ≤ max s.scalars.peak (liveS s+2*value.nodes+4) := by
    simp only [out,charge_scalar_peak,release_scalars]
    change max t2.scalars.peak (liveS t2+1) ≤ _
    have live := liveS_of_memory memory bindings base
    rw [live]
    simp only [Container.nodes] at pu
    omega
  have peak : out.peak = max t2.peak (out.scalars.peak+frame.state.storage.peak) := by
    simpa [out] using charge_release_peak ({t2 with frame := frame} : NState) s 1 1
  have scalarWork : out.scalars.work = t2.scalars.work+1 := by
    simp [out,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]
  have storageWork : out.frame.state.storage.work = s.frame.state.storage.work+r.work := by
    change t2.frame.state.storage.work+r.work = _
    rw [state]
  refine ⟨r,out,?_,⟨data,count,bindCount,scope.trans real.scopedState⟩,?_,?_,stored,limit,items⟩
  · simp [NStmt.run,containerRun,ev.1,appended,out,frame,start]
  · unfold NState.work
    rw [scalarWork,storageWork]
    omega
  · rw [peak]
    rw [state] at qu
    simp only [Container.nodes] at pu
    change _ ≤ max s.peak (max s.scalars.peak (liveS s+2*value.nodes+4)+frame.state.storage.peak)
    omega

theorem sound (st : DynamicOwnedState.State) (s : NState) (real : DynamicOwnedState.Realizes st s)
    (slot : Nat) (ty : Ty) (value : NExpr) (final : DynamicOwnedState.State)
    (pureRun : run slot ty value st = some final) (available : Available st s slot ty) :
    ∃ out, (NStmt.append (.local slot) ty value).run s = some ⟨out,none,false⟩ ∧ DynamicOwnedState.Realizes final out := by
  obtain ⟨p,mutable,valueRest⟩ := DynamicResultValid.bind_some _ _ _ pureRun
  obtain ⟨x,valuePure,viewRest⟩ := DynamicResultValid.bind_some _ _ _ valueRest
  cases lookup : st.core.contents p.owner with
  | none => simp [lookup] at viewRest
  | some view =>
    cases view with
    | rows _ _ _ => simp [lookup] at viewRest
    | flat t sc values =>
      simp only [lookup,Bind.bind,Option.bind] at viewRest
      split at viewRest
      · rename_i good
        have typeEq := good.1
        subst t
        have same := Option.some.inj viewRest
        subst final
        obtain ⟨old,found,room⟩ := available p mutable
        obtain ⟨r,out,ran,after,_⟩ := execute st s real slot ty p mutable sc values lookup value x valuePure good.2 old found room
        exact ⟨out,ran,after⟩
      · contradiction

end Proofs.DynamicFlatAppend
