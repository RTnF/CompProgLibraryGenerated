import Proofs.CppRootModel

namespace Proofs.MultiVecDynamic
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedFacts
open Proofs.CppRowsGraph Proofs.CppRowsContents Proofs.CppRowsFrame Proofs.CppRootModel

structure Parameter where
  slot : Nat
  owner : Nat
  element : Element
  scope : Nat
  writable : Bool
  maximum : Bool
  deriving DecidableEq, Repr

def Parameter.binding (p : Parameter) : Binding := ⟨p.owner,p.element,p.writable,.root p.scope⟩

-- Parameters describe references, while the heap describes objects. Distinct
-- parameters may alias, including a mutable and a const view of the same root.
structure Family (params : List Parameter) (h : Heap) (f : Frame) (m : Resources) : Prop where
  valid : f.state.wellFormed = true
  models : HeapModels f.state h
  lengths : f.rootWritable.length = f.state.forest.objects.length
  bindings : ∀ p ∈ params, f.bindings[p.slot]? = some p.binding
  flags : ∀ p ∈ params, f.rootWritable[p.owner]? = some p.maximum
  permissions : ∀ p ∈ params, p.writable = true → p.maximum = true
  views : ∀ p ∈ params, ∃ v, h p.owner = some v ∧ v.element = p.element ∧ v.scope = p.scope
  measured : Measured f m

theorem Family.row_frame {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (p : Parameter) (member : p ∈ params)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : h p.owner = some (.rows ty sc ids epoch values)) :
    FWR f p.slot p.owner ty sc ids epoch values p.writable p.maximum m := by
  obtain ⟨v,hv,element,scope⟩ := family.views p member
  have equal : v = .rows ty sc ids epoch values := Option.some.inj (hv.symm.trans lookup)
  subst v
  refine ⟨family.models p.owner _ lookup,?_,family.lengths,family.flags p member,
    family.permissions p member,family.measured⟩
  simpa [Parameter.binding,← element,← scope,View.element,View.scope] using family.bindings p member

-- Updating one object updates every alias through the owner-keyed heap.
theorem Family.changed {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (root : Nat) (old new : View)
    (lookup : h root = some old) (element : new.element = old.element) (scope : new.scope = old.scope)
    (next : Frame) (m' : Resources) (models : HeapModels next.state (put h root new))
    (valid : next.state.wellFormed = true)
    (lengths : next.rootWritable.length = next.state.forest.objects.length)
    (bindings : ∀ p ∈ params, next.bindings[p.slot]? = some p.binding)
    (flags : ∀ p ∈ params, next.rootWritable[p.owner]? = some p.maximum)
    (measured : Measured next m') : Family params (put h root new) next m' := by
  refine ⟨valid,models,lengths,bindings,flags,family.permissions,?_,measured⟩
  intro p member
  obtain ⟨v,hv,ve,vs⟩ := family.views p member
  by_cases same : p.owner = root
  · rw [same] at hv
    have equal : v = old := Option.some.inj (hv.symm.trans lookup)
    subst v
    exact ⟨new,by simp [put,same],element.trans ve,scope.trans vs⟩
  · exact ⟨v,by simpa [put,same] using hv,ve,vs⟩

theorem Family.appendRoot {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (p : Parameter) (member : p ∈ params)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : h p.owner = some (.rows ty sc ids epoch values))
    (writable : p.writable = true) (maximum : p.maximum = true)
    (old : Buffer Value) (found : f.state.storage.lookup p.owner = some old)
    (room : old.items.length < old.limit) :
    ∃ r next, f.appendRow p.slot ty = some next ∧
      Family params (put h p.owner (.rows ty sc (ids ++ [m.count]) r.buffer.epoch (values ++ [[]])))
        next (afterRoot m old r) := by
  have fw := family.row_frame p member ty sc ids epoch values lookup
  rw [writable,maximum] at fw
  obtain ⟨r,next,run,post,_⟩ := CppRowsFrame.appendRoot f p.slot p.owner ty sc ids epoch values m fw old found room
  obtain ⟨buffer,obj,bfound,_,_⟩ := root_object f p.owner ty sc ids epoch fw.data.rows
  have equal : buffer = old := Option.some.inj (bfound.symm.trans found)
  subst buffer
  have resolved := resolve_root f p.slot (.vector (.integer ty))
    ⟨p.owner,.vector (.integer ty),true,.root sc⟩ sc old (tag ty sc ids) true fw.binding rfl rfl obj rfl rfl
    (maximum_root f p.owner ty sc ids epoch fw.data.rows true fw.lengths fw.flag) (fun h => h)
  obtain ⟨bindings,flags,others⟩ := append_frame_effect f next p.slot p.owner ty _ old (.rows ty sc ids epoch values) fw.data resolved rfl run
  have models : HeapModels next.state
      (put h p.owner (.rows ty sc (ids ++ [m.count]) r.buffer.epoch (values ++ [[]]))) := by
    apply heap_put next.state h p.owner (.rows ty sc (ids ++ [m.count]) r.buffer.epoch (values ++ [[]])) post.data
    intro other different v hv
    exact others other v different.symm (family.models other v hv)
  refine ⟨r,next,run,family.changed p.owner (.rows ty sc ids epoch values) (.rows ty sc (ids ++ [m.count]) r.buffer.epoch (values ++ [[]])) lookup rfl rfl next _ models post.data.rows.valid post.lengths ?_ ?_ post.measured⟩
  · intro q hq
    rw [bindings]
    exact family.bindings q hq
  · intro q hq
    obtain ⟨v,hv,_,_⟩ := family.views q hq
    have bound := (family.models q.owner v hv).bound
    have lengths := (wellFormed_parts f.state family.valid).1
    have rights := family.lengths
    rw [flags,List.getElem?_append_left (by omega)]
    exact family.flags q hq

theorem Family.updateChild {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (p : Parameter) (member : p ∈ params)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : h p.owner = some (.rows ty sc ids epoch values))
    (k owner : Nat) (rowLookup : ids[k]? = some owner) (old : Buffer Value)
    (found : f.state.storage.lookup owner = some old) (r : Result Value Unit) (row : List Int)
    (items : r.buffer.items = row.map Value.integer)
    (valid : (f.updated owner old r).state.wellFormed = true) :
    Family params (put h p.owner (.rows ty sc ids epoch (values.set k row)))
      (f.updated owner old r) (afterRow m old r) := by
  have fw := family.row_frame p member ty sc ids epoch values lookup
  have post := updateRow f p.slot p.owner ty sc ids epoch values m p.writable p.maximum fw
    k owner rowLookup old found r row items valid
  obtain ⟨buffer,obj,_,_⟩ := row_object f p.owner ty sc ids epoch k owner fw.data.rows rowLookup
  have facts := object_buffer f owner (.integer ty) buffer _ obj
  have models : HeapModels (f.updated owner old r).state
      (put h p.owner (.rows ty sc ids epoch (values.set k row))) := by
    apply heap_put _ h p.owner (.rows ty sc ids epoch (values.set k row)) post.data
    intro other different v hv
    exact updated_other f owner p.owner other _ old r v (family.models other v hv)
      different.symm facts.2.2.1 rfl valid
  exact family.changed p.owner (.rows ty sc ids epoch values) (.rows ty sc ids epoch (values.set k row)) lookup rfl rfl _ _ models valid post.lengths
    family.bindings family.flags post.measured

theorem Family.rebind {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (bs : List Binding)
    (bindings : ∀ p ∈ params, bs[p.slot]? = some p.binding) :
    Family params h {f with bindings := bs} m :=
  ⟨family.valid,family.models,family.lengths,bindings,family.flags,family.permissions,family.views,
    ⟨family.measured.live,family.measured.work,family.measured.peak,family.measured.count,family.measured.base⟩⟩

theorem Family.transport {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (next : Frame)
    (state : next.state = f.state) (rights : next.rootWritable = f.rootWritable)
    (bindings : ∀ p ∈ params, next.bindings[p.slot]? = some p.binding) :
    Family params h next m := by
  refine ⟨?_,?_,?_,bindings,?_,family.permissions,family.views,?_⟩
  · rw [state]; exact family.valid
  · rw [state]; exact family.models
  · rw [rights,state]; exact family.lengths
  · intro p hp; rw [rights]; exact family.flags p hp
  · refine ⟨?_,?_,?_,?_,?_⟩ <;> rw [state]
    · exact family.measured.live
    · exact family.measured.work
    · exact family.measured.peak
    · exact family.measured.count
    · exact family.measured.base

theorem Family.appendBound {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
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
      r.peak ≤ 3*old.capacity+3 := by
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
  obtain ⟨r,run,validNext,items,_,_,amort,peak,_⟩ := CppNestedGrowth.append_ok f cb ty x
    (CppRowsGraph.binding p.owner ty epoch k owner true) old _ resolved rfl valid obj tagFound found rfl owns bvalid accepted room
  obtain ⟨prev,pfound,pitems⟩ := fw.data.contents k owner rowLookup
  have equalPrev : prev = old := Option.some.inj (pfound.symm.trans found)
  subst prev
  have contents : r.buffer.items = (values[k]?.getD [] ++ [x]).map Value.integer := by
    simpa [pitems,List.map_append] using items
  exact ⟨r,f.updated owner old r,by simpa [Frame.append,CppRowsGraph.binding] using run,
    family.updateChild p member ty sc ids epoch values lookup k owner rowLookup old found r _ contents validNext,amort,peak⟩

end Proofs.MultiVecDynamic
