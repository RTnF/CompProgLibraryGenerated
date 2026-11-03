import Proofs.DynamicAppendSound

namespace Proofs.DynamicAppendValue
open Proofs.CppScalar Proofs.CppVector Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt
open Proofs.CppRowsGraph Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicExprCertified Proofs.DynamicExprDerive Proofs.DynamicExprCompose

-- The value may read any supported vector expression. Its temporary row
-- bindings remain valid while the target binding is held across evaluation.
theorem appendChild_stmt (s : NState) (params : List Parameter) (heap : Heap) (m : Resources)
    (family : Family params heap s.frame m) (l : Locals) (contents : ContentsHeap)
    (realizes : Realizes params l contents s) (p : Parameter) (member : p ∈ params)
    (localSlot : Nat) (hslot : s.vectorSlot localSlot = some p.slot)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : heap p.owner = some (.rows ty sc ids epoch values))
    (writable : p.writable = true) (maximum : p.maximum = true)
    (idx value : NExpr) (k owner : Nat) (x : Int)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (ready : Ready params l contents value) (valuePure : denote params l contents value = some x)
    (rowLookup : ids[k]? = some owner) (old : Buffer Value)
    (found : s.frame.state.storage.lookup owner = some old)
    (accepted : ty.valid x = true) (room : old.items.length < old.limit) :
    ∃ (r : Result Value Unit) (out : NState),
      (NStmt.append (.row (.local localSlot) (.integer ty) idx) ty value).run s = some ⟨out,none,false⟩ ∧
      Family params (put heap p.owner (.rows ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x]))))
        out.frame (afterRow m old r) ∧ snapshot out = l ∧
      out.work ≤ s.work+idx.nodes+2*value.nodes+3+r.work ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveS s+idx.nodes+2*value.nodes+4)+(afterRow m old r).peak) ∧
      r.work+CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old+5 := by
  have fw := family.row_frame p member ty sc ids epoch values lookup
  rw [writable,maximum] at fw
  let start := s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)
  obtain ⟨t1,hrow,good1,bindings1⟩ := CppRowsStmt.eval_row start localSlot p.slot idx k p.owner sc epoch owner ids ty
    idxScalar (by rw [envOf_core (core_charge _ _ _)]; exact idxValue)
    (by simpa [NState.vectorSlot,start] using hslot) fw.binding fw.data.rows fw.lengths fw.flag rowLookup
  have firstGood := (GoodF.charge s 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)).trans good1
  have binds1 : t1.frame.bindings = s.frame.bindings ++ [CppRowsGraph.binding p.owner ty epoch k owner true] := bindings1
  have real1 := in_extension params l contents s t1 realizes (Ext.of_goodF firstGood binds1)
  obtain ⟨_,t2,extra,ev⟩ := DynamicExprCertified.sound (derive ready x valuePure) t1 real1
  have good := firstGood.trans ev.2.1
  have bindings2 : t2.frame.bindings = s.frame.bindings ++ ([CppRowsGraph.binding p.owner ty epoch k owner true] ++ extra) := by
    rw [ev.2.2,binds1,List.append_assoc]
  have family2 : Family params heap t2.frame m := family.transport t2.frame good.1 good.2.1 (by
    intro q hq
    rw [bindings2,List.getElem?_append_left (List.getElem?_eq_some_iff.mp (family.bindings q hq)).1]
    exact family.bindings q hq)
  obtain ⟨r,frame,run,post,amort,_⟩ := family2.appendBound p member ty sc ids epoch values lookup writable maximum
    s.frame.bindings.length k owner rowLookup (by simp [bindings2]) old (by rw [good.1]; exact found) x accepted room
  let out := (({t2 with frame := frame} : NState).release s).charge 1 1
  have after : Family params (put heap p.owner (.rows ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x]))))
      out.frame (afterRow m old r) := post.rebind _ (by
    intro q hq
    rw [List.getElem?_take_of_lt (List.getElem?_eq_some_iff.mp (family.bindings q hq)).1]
    exact post.bindings q hq)
  obtain ⟨state,rights,slots,scope,memory,bindings,base,lower,upper,pl,pu,ql,qu⟩ := good
  have snap : snapshot out = l := by
    have unchanged : snapshot out = snapshot s := by simp [out,snapshot,NState.release,memory,bindings,slots]
    exact unchanged.trans realizes.locals
  have work : out.scalars.work = t2.scalars.work+1 := by
    simp [out,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]
  have storage := after.measured.work
  have before := family.measured.work
  have oldPeak := family.measured.peak
  have newPeak := after.measured.peak
  have grows : s.frame.state.storage.peak ≤ (afterRow m old r).peak := by
    rw [oldPeak]; exact Nat.le_max_left _ _
  have scalarPeak : out.scalars.peak ≤ max s.scalars.peak (liveS s+idx.nodes+2*value.nodes+4) := by
    simp only [out,charge_scalar_peak,release_scalars]
    change max t2.scalars.peak (liveS t2+1) ≤ _
    have live := liveS_of_memory memory bindings base
    rw [live]
    simp only [Container.nodes] at pu
    omega
  have framePeak : frame.state.storage.peak = (afterRow m old r).peak := by simpa [out,NState.release] using newPeak
  have peak : out.peak = max t2.peak (out.scalars.peak+(afterRow m old r).peak) := by
    simpa [out,framePeak] using charge_release_peak ({t2 with frame := frame} : NState) s 1 1
  rw [state] at qu
  refine ⟨r,out,?_,after,snap,?_,?_,amort⟩
  · have evalRow : (Container.row (.local localSlot) (.integer ty) idx).eval
        (s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)) =
          some (t1,s.frame.bindings.length) := hrow
    simp [NStmt.run,evalRow,ev.1,run,out]
  · unfold NState.work
    simp only [afterRow] at storage
    omega
  · simp only [Container.nodes] at pu
    omega

-- Availability concerns only the row being mutated, not unrelated buffers.
def RoomAt (s : NState) (root k : Nat) : Prop :=
  ∃ parent owner old, s.frame.state.storage.lookup root = some parent ∧
    parent.items[k]? = some (.child owner) ∧ s.frame.state.storage.lookup owner = some old ∧
    old.items.length < old.limit

theorem appendChild (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (slot : Nat) (ty : Ty) (p : Parameter)
    (mutable : DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p)
    (sc k : Nat) (values : List (List Int)) (row : List Int)
    (lookup : st.contents p.owner = some (.rows ty sc values)) (rowFound : values[k]? = some row)
    (idx value : NExpr) (idxScalar : idx.scalarOnly = true)
    (idxValue : idx.denote (environment st.locals) = some (k : Int))
    (x : Int) (ready : Ready params st.locals st.contents value) (valuePure : denote params st.locals st.contents value = some x) (accepted : ty.valid x = true) (available : RoomAt s p.owner k) :
    let pure : DynamicStmt.Step := ⟨⟨st.locals,putContents st.contents p.owner (.rows ty sc (values.set k (row ++ [x])))⟩,none⟩
    DynamicStmt.run params (.append (.row (.local slot) (.integer ty) idx) ty value) st = some pure ∧
      ∃ (old : Buffer Value) (r : Result Value Unit) (out : NState),
        (NStmt.append (.row (.local slot) (.integer ty) idx) ty value).run s = some ⟨out,none,false⟩ ∧
        DynamicScalarSound.Matches params pure ⟨out,none,false⟩ ∧
        out.work+CppVectorGrowth.potential r.buffer ≤ s.work+idx.nodes+2*value.nodes+8+CppVectorGrowth.potential old ∧
        out.peak ≤ max s.peak (max s.scalars.peak (liveS s+idx.nodes+2*value.nodes+4)+out.frame.state.storage.peak) := by
  obtain ⟨location,selected,writable,maximum,_,_⟩ := DynamicAppendSound.mutable_found params st slot _ p mutable
  obtain ⟨heap,m,family,he⟩ := realizes.heap
  obtain ⟨ids,epoch,hv⟩ := DynamicSizeSound.rows_lift heap p.owner ty sc values (by rw [he]; exact lookup)
  have fw := family.row_frame p (List.mem_of_find?_eq_some selected) ty sc ids epoch values hv
  have bound : k < ids.length := by rw [← fw.data.length]; exact (List.getElem?_eq_some_iff.mp rowFound).1
  obtain ⟨owner,rowLookup⟩ : ∃ owner, ids[k]? = some owner := ⟨ids[k],by simp⟩
  obtain ⟨parent,other,old,parentFound,child,oldFound,room⟩ := available
  obtain ⟨pb,pbFound,_,items⟩ := fw.data.rows.buffer
  have same : pb = parent := Option.some.inj (pbFound.symm.trans parentFound)
  subst pb
  have child' : parent.items[k]? = some (.child owner) := by simp [items,List.getElem?_map,rowLookup]
  have owners : other = owner := by simpa using Option.some.inj (child.symm.trans child')
  subst other
  have indexPure : denote params st.locals st.contents idx = some (k : Int) := by
    rw [denote_scalar _ _ _ _ idxScalar]; exact idxValue
  have actualIndex : idx.denote (envOf s) = some (k : Int) := by
    rw [← snapshot_env,realizes.locals]; exact idxValue
  obtain ⟨r,out,ran,post,snap,work,peak,amort⟩ := appendChild_stmt s params heap m family st.locals st.contents realizes
    p (List.mem_of_find?_eq_some selected) slot (DynamicSizeSound.vector_slot params st.locals st.contents s realizes slot p.slot location)
    ty sc ids epoch values hv writable maximum idx value k owner x idxScalar actualIndex ready valuePure rowLookup old oldFound accepted room
  have projected : eraseHeap (put heap p.owner (.rows ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x])))) =
      putContents st.contents p.owner (.rows ty sc (values.set k (row ++ [x]))) := by
    rw [erase_put,he]; simp [erase,rowFound]
  have after : Realizes params st.locals (putContents st.contents p.owner (.rows ty sc (values.set k (row ++ [x])))) out :=
    ⟨snap,_,_,post,projected⟩
  refine ⟨?_,old,r,out,ran,⟨after,rfl,rfl⟩,?_,?_⟩
  · simp [DynamicStmt.run,mutable,indexPure,valuePure,DynamicContents.appendChild,lookup,rowFound,accepted]
  · omega
  · rw [post.measured.peak]; exact peak

end Proofs.DynamicAppendValue
