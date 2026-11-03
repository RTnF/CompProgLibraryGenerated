import Proofs.DynamicAppendValue
import Proofs.DynamicIndexAtoms

namespace Proofs.DynamicAppendIndex
open Proofs.CppScalar Proofs.CppVector Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt
open Proofs.CppRowsGraph Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicExprCertified Proofs.DynamicExprDerive Proofs.DynamicExprCompose

theorem append_bound {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (p : Parameter) (member : p ∈ params)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : h p.owner = some (.rows ty sc ids epoch values))
    (writable : p.writable = true) (maximum : p.maximum = true)
    (cb k owner : Nat) (rowLookup : ids[k]? = some owner)
    (binding : f.bindings[cb]? = some (CppRowsGraph.binding p.owner ty epoch k owner true))
    (old : Buffer Value) (found : f.state.storage.lookup owner = some old) (x : Int)
    (accepted : ty.valid x = true) (room : old.items.length < old.limit) :
    ∃ r next, f.append cb ty x = some next ∧
      Family params (put h p.owner (.rows ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x]))))
        next (afterRow m old r) ∧
      r.work + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old + 5 ∧
      r.peak ≤ 3*old.capacity+3 ∧ next = f.updated owner old r ∧ r.buffer.limit = old.limit ∧ r.buffer.items = old.items ++ [.integer x] := by
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
  obtain ⟨r,run,validNext,items,_,limit,amort,peak,_⟩ := CppNestedGrowth.append_ok f cb ty x
    (CppRowsGraph.binding p.owner ty epoch k owner true) old _ resolved rfl valid obj tagFound found rfl owns bvalid accepted room
  obtain ⟨prev,pfound,pitems⟩ := fw.data.contents k owner rowLookup
  have equalPrev : prev = old := Option.some.inj (pfound.symm.trans found)
  subst prev
  have contents : r.buffer.items = (values[k]?.getD [] ++ [x]).map Value.integer := by
    simpa [pitems,List.map_append] using items
  exact ⟨r,f.updated owner old r,by simpa [Frame.append,CppRowsGraph.binding] using run,
    family.updateChild p member ty sc ids epoch values lookup k owner rowLookup old found r _ contents validNext,amort,peak,rfl,limit,items⟩


theorem appendChild_stmt (s : NState) (params : List Parameter) (heap : Heap) (m : Resources)
    (family : Family params heap s.frame m) (l : Locals) (contents : ContentsHeap)
    (realizes : Realizes params l contents s) (p : Parameter) (member : p ∈ params)
    (localSlot : Nat) (hslot : s.vectorSlot localSlot = some p.slot)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : heap p.owner = some (.rows ty sc ids epoch values))
    (writable : p.writable = true) (maximum : p.maximum = true)
    (idx value : NExpr) (k owner : Nat) (x : Int)
    (idxReady : Ready params l contents idx) (idxValue : denote params l contents idx = some (k : Int))
    (ready : Ready params l contents value) (valuePure : denote params l contents value = some x)
    (rowLookup : ids[k]? = some owner) (old : Buffer Value)
    (found : s.frame.state.storage.lookup owner = some old)
    (accepted : ty.valid x = true) (room : old.items.length < old.limit) :
    ∃ (r : Result Value Unit) (out : NState),
      (NStmt.append (.row (.local localSlot) (.integer ty) idx) ty value).run s = some ⟨out,none,false⟩ ∧
      Family params (put heap p.owner (.rows ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x]))))
        out.frame (afterRow m old r) ∧ snapshot out = l ∧
      out.work ≤ s.work+2*idx.nodes+2*value.nodes+3+r.work ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveS s+2*idx.nodes+2*value.nodes+4)+(afterRow m old r).peak) ∧
      r.work+CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old+5 ∧
      out.frame.state.storage.lookup owner = some r.buffer ∧
      (∀ other, owner ≠ other → out.frame.state.storage.lookup other = s.frame.state.storage.lookup other) ∧
      r.buffer.limit = old.limit ∧ r.buffer.items = old.items ++ [.integer x] := by
  have fw := family.row_frame p member ty sc ids epoch values lookup
  rw [writable,maximum] at fw
  let start := s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)
  obtain ⟨t1,idxExtra,hrow,good1,bindings1⟩ := DynamicIndexEval.eval_row start localSlot p.slot idx k p.owner sc epoch owner ids ty true true
    (2*idx.nodes) (2*idx.nodes)
    (fun u ext => DynamicIndexAtoms.index_ev idxReady idxValue s realizes u ((Ext.charge s 0 _).trans ext))
    (by simpa [NState.vectorSlot,start] using hslot) fw.binding fw.data.rows fw.lengths fw.flag (fun h => h) rowLookup
  have firstGood := (GoodF.charge s 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)).trans good1
  have binds1 : t1.frame.bindings = s.frame.bindings ++ (idxExtra ++ [CppRowsGraph.binding p.owner ty epoch k owner true]) := bindings1
  have real1 := in_extension params l contents s t1 realizes (Ext.of_goodF firstGood binds1)
  obtain ⟨_,t2,extra,ev⟩ := DynamicExprCertified.sound (derive ready x valuePure) t1 real1
  have good := firstGood.trans ev.2.1
  have bindings2 : t2.frame.bindings = s.frame.bindings ++ (idxExtra ++ [CppRowsGraph.binding p.owner ty epoch k owner true] ++ extra) := by
    rw [ev.2.2,binds1]; simp [List.append_assoc]
  have family2 : Family params heap t2.frame m := family.transport t2.frame good.1 good.2.1 (by
    intro q hq
    rw [bindings2,List.getElem?_append_left (List.getElem?_eq_some_iff.mp (family.bindings q hq)).1]
    exact family.bindings q hq)
  obtain ⟨r,frame,run,post,amort,_,frameEq,limit,items⟩ := append_bound family2 p member ty sc ids epoch values lookup writable maximum
    (s.frame.bindings.length+idxExtra.length) k owner rowLookup (by simp [bindings2]) old (by rw [good.1]; exact found) x accepted room
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
  have scalarPeak : out.scalars.peak ≤ max s.scalars.peak (liveS s+2*idx.nodes+2*value.nodes+4) := by
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
  have updated : out.frame.state.storage.lookup owner = some r.buffer := by
    simpa [out,frameEq,NState.release] using CppNestedOps.updated_lookup_self t2.frame owner old r
      (CppVectorStore.lookup_bound t2.frame.state.storage owner old (by rw [state]; exact found))
  have others : ∀ other, owner ≠ other → out.frame.state.storage.lookup other = s.frame.state.storage.lookup other := by
    intro other different
    simpa [out,frameEq,NState.release,state] using CppNestedOps.updated_lookup_other t2.frame owner other old r different
  refine ⟨r,out,?_,after,snap,?_,?_,amort,updated,others,limit,items⟩
  · have evalRow : (Container.row (.local localSlot) (.integer ty) idx).eval
        (s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)) =
          some (t1,s.frame.bindings.length+idxExtra.length) := hrow
    simp [NStmt.run,evalRow,ev.1,run,out]
  · unfold NState.work
    simp only [afterRow] at storage
    omega
  · simp only [Container.nodes] at pu
    omega


-- The amortised witnesses are tied to the actual before/after buffers.
def RowUpdate (before after : NState) (root k : Nat) (x : Int) (old next : Buffer Value) : Prop :=
  ∃ parent owner, before.frame.state.storage.lookup root = some parent ∧
    parent.items[k]? = some (.child owner) ∧ before.frame.state.storage.lookup owner = some old ∧
    after.frame.state.storage.lookup root = some parent ∧ after.frame.state.storage.lookup owner = some next ∧
    next.limit = old.limit ∧ next.items = old.items ++ [.integer x]

theorem RowUpdate.room {before after : NState} {root k : Nat} {x : Int} {old next : Buffer Value}
    (updated : RowUpdate before after root k x old next) (room : next.items.length < next.limit) :
    DynamicAppendValue.RoomAt after root k := by
  obtain ⟨parent,owner,_,child,_,parentAfter,rowAfter,_,_⟩ := updated
  exact ⟨parent,owner,next,parentAfter,child,rowAfter,room⟩

def RoomFor (s : NState) (root k count : Nat) : Prop :=
  ∃ parent owner old, s.frame.state.storage.lookup root = some parent ∧
    parent.items[k]? = some (.child owner) ∧ s.frame.state.storage.lookup owner = some old ∧
    old.items.length+count ≤ old.limit

theorem RoomFor.one {s : NState} {root k count : Nat} (available : RoomFor s root k count) (positive : 0 < count) :
    DynamicAppendValue.RoomAt s root k := by
  obtain ⟨parent,owner,old,p,c,r,space⟩ := available
  exact ⟨parent,owner,old,p,c,r,by omega⟩

theorem RowUpdate.remaining {before after : NState} {root k count : Nat} {x : Int} {old next : Buffer Value}
    (updated : RowUpdate before after root k x old next) (available : RoomFor before root k (count+1)) :
    RoomFor after root k count := by
  obtain ⟨parent,owner,parentBefore,child,rowBefore,parentAfter,rowAfter,limit,items⟩ := updated
  obtain ⟨p2,o2,b2,pFound,cFound,bFound,space⟩ := available
  have parents : p2 = parent := Option.some.inj (pFound.symm.trans parentBefore)
  subst p2
  have owners : o2 = owner := by simpa using Option.some.inj (cFound.symm.trans child)
  subst o2
  have buffers : b2 = old := Option.some.inj (bFound.symm.trans rowBefore)
  subst b2
  refine ⟨parent,owner,next,parentAfter,child,rowAfter,?_⟩
  simp only [items,List.length_append,List.length_singleton,limit]
  omega

theorem RowUpdate.link {before middle after : NState} {root k : Nat} {x y : Int} {old next old2 final : Buffer Value}
    (first : RowUpdate before middle root k x old next) (second : RowUpdate middle after root k y old2 final) : old2 = next := by
  obtain ⟨parent,owner,_,child,_,parentAfter,rowAfter,_,_⟩ := first
  obtain ⟨parent2,owner2,parentBefore,child2,rowBefore,_⟩ := second
  have equal : parent2 = parent := Option.some.inj (parentBefore.symm.trans parentAfter)
  subst parent2
  have same : owner2 = owner := by simpa using Option.some.inj (child2.symm.trans child)
  subst owner2
  exact Option.some.inj (rowBefore.symm.trans rowAfter)

theorem RowUpdate.two_work {before middle after : NState} {root k : Nat} {x y : Int} {old next old2 final : Buffer Value}
    (first : RowUpdate before middle root k x old next) (second : RowUpdate middle after root k y old2 final)
    (c1 c2 : Nat)
    (one : middle.work+CppVectorGrowth.potential next ≤ before.work+c1+CppVectorGrowth.potential old)
    (two : after.work+CppVectorGrowth.potential final ≤ middle.work+c2+CppVectorGrowth.potential old2) :
    after.work+CppVectorGrowth.potential final ≤ before.work+c1+c2+CppVectorGrowth.potential old := by
  have same := first.link second
  rw [same] at two
  omega

theorem appendChild (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (slot : Nat) (ty : Ty) (p : Parameter)
    (mutable : DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p)
    (sc k : Nat) (values : List (List Int)) (row : List Int)
    (lookup : st.contents p.owner = some (.rows ty sc values)) (rowFound : values[k]? = some row)
    (idx value : NExpr) (idxReady : Ready params st.locals st.contents idx)
    (idxValue : denote params st.locals st.contents idx = some (k : Int))
    (x : Int) (ready : Ready params st.locals st.contents value) (valuePure : denote params st.locals st.contents value = some x) (accepted : ty.valid x = true) (available : DynamicAppendValue.RoomAt s p.owner k) :
    let pure : DynamicStmt.Step := ⟨⟨st.locals,putContents st.contents p.owner (.rows ty sc (values.set k (row ++ [x])))⟩,none⟩
    DynamicStmt.run params (.append (.row (.local slot) (.integer ty) idx) ty value) st = some pure ∧
      ∃ (old : Buffer Value) (r : Result Value Unit) (out : NState),
        (NStmt.append (.row (.local slot) (.integer ty) idx) ty value).run s = some ⟨out,none,false⟩ ∧
        DynamicScalarSound.Matches params pure ⟨out,none,false⟩ ∧
        RowUpdate s out p.owner k x old r.buffer ∧
        out.work+CppVectorGrowth.potential r.buffer ≤ s.work+2*idx.nodes+2*value.nodes+8+CppVectorGrowth.potential old ∧
        out.peak ≤ max s.peak (max s.scalars.peak (liveS s+2*idx.nodes+2*value.nodes+4)+out.frame.state.storage.peak) := by
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
  obtain ⟨r,out,ran,post,snap,work,peak,amort,updated,others,limit,newItems⟩ := appendChild_stmt s params heap m family st.locals st.contents realizes
    p (List.mem_of_find?_eq_some selected) slot (DynamicSizeSound.vector_slot params st.locals st.contents s realizes slot p.slot location)
    ty sc ids epoch values hv writable maximum idx value k owner x idxReady idxValue ready valuePure rowLookup old oldFound accepted room
  have projected : eraseHeap (put heap p.owner (.rows ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x])))) =
      putContents st.contents p.owner (.rows ty sc (values.set k (row ++ [x]))) := by
    rw [erase_put,he]; simp [erase,rowFound]
  have after : Realizes params st.locals (putContents st.contents p.owner (.rows ty sc (values.set k (row ++ [x])))) out :=
    ⟨snap,_,_,post,projected⟩
  obtain ⟨_,_,_,earlier⟩ := CppRowsGraph.row_object s.frame p.owner ty sc ids epoch k owner fw.data.rows rowLookup
  have linked : RowUpdate s out p.owner k x old r.buffer :=
    ⟨parent,owner,parentFound,child,oldFound,(others p.owner (by omega)).trans parentFound,updated,limit,newItems⟩
  refine ⟨?_,old,r,out,ran,⟨after,rfl,rfl⟩,linked,?_,?_⟩
  · simp [DynamicStmt.run,mutable,idxValue,valuePure,DynamicContents.appendChild,lookup,rowFound,accepted]
  · omega
  · rw [post.measured.peak]; exact peak

end Proofs.DynamicAppendIndex
