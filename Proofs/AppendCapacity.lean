import Proofs.MultiVecDynamicSteps

/-!
Appending to a row of a nested vector with the capacity of the grown buffer exposed.

`MultiVecDynamicSteps.appendChild_stmt` proves the amortised work of one growing append but does not say
which buffer the row holds afterwards or how large its capacity is. Space bounds for a vector built by
repeated `emplace_back` need both: the row's buffer is the appended result, and its capacity is at most
`max old.capacity (2 * old.items.length + 1)` (libstdc++ doubling, `CppVectorGrowth.nextCapacity`).
-/

namespace Proofs.AppendCapacity
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedFacts
open Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt
open Proofs.CppRowsGraph Proofs.CppRowsContents Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic

theorem append_capacity {α : Type} (b : Buffer α) (accept : α → Bool) (writable : Bool) (value : α)
    (r : Result α Unit) (run : CppVectorGrowth.append b accept writable value = some r) :
    r.buffer.capacity ≤ max b.capacity (2 * b.items.length + 1) := by
  unfold CppVectorGrowth.append at run
  split at run
  · split at run
    · have := Option.some.inj run; subst this; exact Nat.le_max_left _ _
    · have := Option.some.inj run; subst this
      simp only [CppVectorGrowth.nextCapacity]
      omega
  · simp at run

theorem append_ok (f : Frame) (slot : Nat) (ty : Ty) (value : Int)
    (binding : Binding) (buffer : Buffer Value) (tag : Tag)
    (resolved : f.resolve slot (.integer ty) = some (binding,buffer))
    (writable : binding.writable = true) (valid : f.state.wellFormed = true)
    (object : f.object binding.owner (.integer ty) = some (buffer,tag))
    (tagFound : f.state.forest.lookup binding.owner = some tag)
    (found : f.state.storage.lookup binding.owner = some buffer)
    (type : tag.element = .integer ty) (owns : buffer.owner = binding.owner)
    (bv : buffer.Valid (accepts (.integer ty)))
    (accepted : ty.valid value = true) (room : buffer.items.length < buffer.limit) :
    ∃ r, f.appendGrowing slot ty value = some (f.updated binding.owner buffer r) ∧
      (f.updated binding.owner buffer r).state.wellFormed = true ∧
      r.buffer.items = buffer.items ++ [.integer value] ∧
      r.work + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential buffer + 5 ∧
      r.peak ≤ 3 * buffer.capacity + 3 ∧
      r.buffer.capacity ≤ max buffer.capacity (2 * buffer.items.length + 1) ∧ r.buffer.limit = buffer.limit := by
  obtain ⟨r, run, rv, ri, ro, rl, amort, peak, epoch⟩ :=
    CppVectorGrowth.append_spec buffer (accepts (.integer ty)) (.integer value) bv accepted room
  have same : r.buffer.owner = binding.owner := ro.trans owns
  have payload : CppNestedVectorStore.payloadOK tag r.buffer := by
    simp [CppNestedVectorStore.payloadOK, type, rv]
  have peaks := CppVectorStoreGrowth.append_peak buffer (accepts (.integer ty)) (.integer value) r run
  have commit := commit_runs f binding.owner (.integer ty) buffer tag r valid object tagFound found
    same payload peaks.1 peaks.2
  refine ⟨r, ?_, commit_success_valid f _ _ _ _ commit, ri, amort, peak,
    append_capacity buffer _ true _ r run, rl⟩
  simp [Frame.appendGrowing, resolved, writable, run, commit]

theorem Family.appendBound {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (p : Parameter) (member : p ∈ params)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : h p.owner = some (.rows ty sc ids epoch values))
    (writable : p.writable = true) (maximum : p.maximum = true)
    (cb k owner : Nat) (rowLookup : ids[k]? = some owner)
    (binding : f.bindings[cb]? = some (CppRowsGraph.binding p.owner ty epoch k owner true))
    (old : Buffer Value) (found : f.state.storage.lookup owner = some old) (x : Int)
    (accepted : ty.valid x = true) (room : old.items.length < old.limit) :
    ∃ r, f.append cb ty x = some (f.updated owner old r) ∧
      Family params (put h p.owner (.rows ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x]))))
        (f.updated owner old r) (afterRow m old r) ∧
      r.work + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old + 5 ∧
      r.peak ≤ 3*old.capacity+3 ∧
      r.buffer.capacity ≤ max old.capacity (2 * old.items.length + 1) ∧
      r.buffer.items = old.items ++ [.integer x] ∧ r.buffer.limit = old.limit := by
  have fw := family.row_frame p member ty sc ids epoch values lookup
  rw [writable,maximum] at fw
  obtain ⟨buffer,resolved,bfound⟩ := resolve_row f cb p.owner ty sc ids epoch k owner
    fw.data.rows rowLookup true true binding fw.lengths fw.flag (fun h => h)
  have equal : buffer = old := Option.some.inj (bfound.symm.trans found)
  subst buffer
  obtain ⟨ob,obj,ofound,_⟩ := row_object f p.owner ty sc ids epoch k owner fw.data.rows rowLookup
  have same : ob = old := Option.some.inj (ofound.symm.trans found)
  subst ob
  obtain ⟨valid,owns,bvalid,tagFound,element⟩ := Proofs.CppNestedRows.buffer_facts f owner ty old _ obj
  obtain ⟨r,run,validNext,items,amort,peak,capacity,limit⟩ := append_ok f cb ty x
    (CppRowsGraph.binding p.owner ty epoch k owner true) old _ resolved rfl valid obj tagFound found rfl owns bvalid accepted room
  obtain ⟨prev,pfound,pitems⟩ := fw.data.contents k owner rowLookup
  have equalPrev : prev = old := Option.some.inj (pfound.symm.trans found)
  subst prev
  have contents : r.buffer.items = (values[k]?.getD [] ++ [x]).map Value.integer := by
    simpa [pitems,List.map_append] using items
  exact ⟨r,by simpa [Frame.append,CppRowsGraph.binding] using run,
    family.updateChild p member ty sc ids epoch values lookup k owner rowLookup old found r _ contents validNext,
    amort,peak,capacity,items,limit⟩

/-- `MultiVecDynamicSteps.appendChild_stmt` with the row's new buffer, its capacity bound and the
unchanged other objects. -/
theorem appendChild_stmt (s : NState) (params : List Parameter) (h : Heap) (m : Resources)
    (family : Family params h s.frame m) (p : Parameter) (member : p ∈ params)
    (localSlot : Nat) (hslot : s.vectorSlot localSlot = some p.slot)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : h p.owner = some (.rows ty sc ids epoch values))
    (writable : p.writable = true) (maximum : p.maximum = true)
    (idx value : NExpr) (k owner : Nat) (x : Int)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (vScalar : value.scalarOnly = true) (vValue : value.denote (envOf s) = some x)
    (rowLookup : ids[k]? = some owner) (old : Buffer Value)
    (found : s.frame.state.storage.lookup owner = some old)
    (accepted : ty.valid x = true) (room : old.items.length < old.limit) :
    ∃ r t, (NStmt.append (.row (.local localSlot) (.integer ty) idx) ty value).run s = some ⟨t,none,false⟩ ∧
      Family params (put h p.owner (.rows ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x]))))
        t.frame (afterRow m old r) ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+idx.nodes+value.nodes+3 ∧
      r.work + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old + 5 ∧
      r.peak ≤ 3*old.capacity+3 ∧
      r.buffer.capacity ≤ max old.capacity (2 * old.items.length + 1) ∧
      r.buffer.items = old.items ++ [.integer x] ∧ r.buffer.limit = old.limit ∧
      t.frame.state.storage.lookup owner = some r.buffer ∧
      (∀ o, o ≠ owner → t.frame.state.storage.lookup o = s.frame.state.storage.lookup o) ∧
      t.frame.state.storage.objects.length = s.frame.state.storage.objects.length ∧
      t.frame.state.forest = s.frame.state.forest ∧
      t.frame.bindings = s.frame.bindings ∧ t.frame.rootWritable = s.frame.rootWritable ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.baseMemory = s.scalars.baseMemory ∧
      s.scalars.peak ≤ t.scalars.peak ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+idx.nodes+value.nodes+4) ∧
      s.peak ≤ t.peak ∧ t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak) := by
  have fw := family.row_frame p member ty sc ids epoch values lookup
  rw [writable,maximum] at fw
  let start := s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)
  obtain ⟨t1,hrow,good1,bindings1⟩ := CppRowsStmt.eval_row start localSlot p.slot idx k p.owner sc epoch owner ids ty
    idxScalar (by rw [envOf_core (core_charge _ _ _)]; exact idxValue)
    (by simpa [NState.vectorSlot,start] using hslot) fw.binding fw.data.rows fw.lengths fw.flag rowLookup
  have goodStart := GoodF.charge s 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)
  have goodRow := goodStart.trans good1
  obtain ⟨t2,hvalue,good2⟩ := scalar_eval value t1 x vScalar
    (by rw [envOf_goodF goodRow]; exact vValue)
  have good := goodRow.trans good2.toF
  have bindings2 : t2.frame.bindings = s.frame.bindings ++ [CppRowsGraph.binding p.owner ty epoch k owner true] := by
    rw [good2.1.1,bindings1]; rfl
  have family2 : Family params h t2.frame m := family.transport t2.frame good.1 good.2.1 (by
    intro q hq
    rw [bindings2,List.getElem?_append_left (List.getElem?_eq_some_iff.mp (family.bindings q hq)).1]
    exact family.bindings q hq)
  obtain ⟨r,run,post,amort,peak,capacity,items,limit⟩ := Family.appendBound family2 p member ty sc ids epoch values lookup
    writable maximum s.frame.bindings.length k owner rowLookup (by simp [bindings2]) old (by rw [good.1]; exact found)
    x accepted room
  let frame := t2.frame.updated owner old r
  let t := (({t2 with frame := frame} : NState).release s).charge 1 1
  have stateT : t.frame.state = frame.state := rfl
  have bound : owner < t2.frame.state.storage.objects.length := by
    rw [good.1]; exact CppVectorStore.lookup_bound _ owner old found
  have selfLookup : t.frame.state.storage.lookup owner = some r.buffer := by
    rw [stateT]; exact CppNestedOps.updated_lookup_self t2.frame owner old r bound
  have otherLookup : ∀ o, o ≠ owner → t.frame.state.storage.lookup o = s.frame.state.storage.lookup o := by
    intro o different
    rw [stateT,CppNestedOps.updated_lookup_other t2.frame owner o old r (Ne.symm different),good.1]
  have work : t.scalars.work = t2.scalars.work+1 := by
    simp [t,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]
  have g1 := good.1
  have g2 := good.2.1
  obtain ⟨_,_,sl,sc',me,bi,ba,wl,wu,pl,pu,ql,qu⟩ := good
  have bindingsT : t.frame.bindings = s.frame.bindings := by
    change (frame.bindings.take s.frame.bindings.length) = _
    simp [frame,Frame.updated,bindings2]
  refine ⟨r,t,?_,post.rebind _ ?_,by omega,by omega,amort,peak,capacity,items,limit,selfLookup,otherLookup,?_,?_,
    bindingsT,?_,sl,sc',me,bi,ba,?_,?_,?_,?_⟩
  · have evalRow : (Container.row (.local localSlot) (.integer ty) idx).eval
        (s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)) =
          some (t1,s.frame.bindings.length) := hrow
    simp [NStmt.run,evalRow,hvalue,run,t,frame]
  · intro q hq
    have inside := (List.getElem?_eq_some_iff.mp (family.bindings q hq)).1
    rw [List.getElem?_take_of_lt inside]
    exact post.bindings q hq
  · rw [stateT]; simp [frame,Frame.updated,g1]
  · rw [stateT]; simp [frame,Frame.updated,g1]
  · show frame.rootWritable = _
    simp [frame,Frame.updated]; exact g2
  · simp only [t,charge_scalar_peak,release_scalars]
    omega
  · simp only [t,charge_scalar_peak,release_scalars]
    simp [Container.nodes,NExpr.nodes] at pu
    simp only [liveS] at pu ⊢
    rw [me,bi,ba]
    omega
  · simp only [t,charge_peak,release_peak]
    omega
  · have hp := charge_release_peak ({t2 with frame := frame} : NState) s 1 1
    have st2 : t2.frame.state.storage.peak ≤ frame.state.storage.peak := by
      show t2.frame.state.storage.peak ≤ max t2.frame.state.storage.peak _
      exact Nat.le_max_left _ _
    have sp : t2.scalars.peak ≤ t.scalars.peak := by
      simp only [t,charge_scalar_peak,release_scalars]; omega
    change t.peak = max t2.peak (t.scalars.peak+frame.state.storage.peak) at hp
    rw [hp,stateT]
    have qu' : t2.peak ≤ max s.peak (t2.scalars.peak+s.frame.state.storage.peak) := by rw [← g1]; exact qu
    rw [g1] at st2
    omega

end Proofs.AppendCapacity
