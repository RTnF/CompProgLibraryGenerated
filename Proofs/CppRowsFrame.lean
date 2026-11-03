import Proofs.CppRowsContents

namespace Proofs.CppRowsFrame
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedConstruct
open Proofs.CppRowsGraph Proofs.CppRowsContents

-- Resource quantities vary with the frame, rather than being constants in a
-- function's parameter layout. baseSpace remains the allocation baseline.
structure Resources where
  live : Nat
  work : Nat
  peak : Nat
  count : Nat
  base : Nat
  deriving DecidableEq, Repr

structure Measured (f : Frame) (m : Resources) : Prop where
  live : f.state.liveSpace = m.live
  work : f.state.storage.work = m.work
  peak : f.state.storage.peak = m.peak
  count : f.state.storage.objects.length = m.count
  base : f.state.storage.baseSpace = m.base

def resources (f : Frame) : Resources :=
  ⟨f.state.liveSpace,f.state.storage.work,f.state.storage.peak,
    f.state.storage.objects.length,f.state.storage.baseSpace⟩

theorem measured_resources (f : Frame) : Measured f (resources f) := ⟨rfl,rfl,rfl,rfl,rfl⟩

-- Other roots, objects, and temporary bindings may coexist with this root.
-- This is a per-root invariant; it does not impose contiguous allocation.
structure FWR (f : Frame) (slot root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (writable maximum : Bool) (m : Resources) : Prop where
  data : Data f.state root ty sc ids epoch values
  binding : f.bindings[slot]? = some ⟨root,.vector (.integer ty),writable,.root sc⟩
  lengths : f.rootWritable.length = f.state.forest.objects.length
  flag : f.rootWritable[root]? = some maximum
  permission : writable = true → maximum = true
  measured : Measured f m

def afterRoot (m : Resources) (old : Buffer Value) (r : Result Value Unit) : Resources :=
  ⟨m.live + r.buffer.capacity - old.capacity, m.work+r.work+1,
    max m.peak (m.live+(r.peak-(old.capacity+1))-m.base),m.count+1,m.base⟩

theorem appendRoot (f : Frame) (slot root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int)) (m : Resources)
    (fw : FWR f slot root ty sc ids epoch values true true m)
    (old : Buffer Value) (found : f.state.storage.lookup root = some old)
    (room : old.items.length < old.limit) :
    ∃ r next, f.appendRow slot ty = some next ∧
      FWR next slot root ty sc (ids ++ [m.count]) r.buffer.epoch (values ++ [[]])
        true true (afterRoot m old r) ∧
      next.state.liveSpace + old.capacity = m.live + r.buffer.capacity := by
  obtain ⟨r,run,data⟩ := appendRow_data f.state root ty sc ids epoch values fw.data old found room
  let state := CppAppendRow.added f.state root (tag ty sc ids) ty old r
  let next : Frame := {f with state := state, rootWritable := f.rootWritable ++ [false]}
  obtain ⟨buffer,obj,bfound,_,_⟩ := root_object f root ty sc ids epoch fw.data.rows
  have equal : buffer = old := Option.some.inj (bfound.symm.trans found)
  subst buffer
  have resolved := Proofs.CppNestedFacts.resolve_root f slot (.vector (.integer ty))
    ⟨root,.vector (.integer ty),true,.root sc⟩ sc old (tag ty sc ids) true fw.binding rfl rfl obj rfl rfl
    (maximum_root f root ty sc ids epoch fw.data.rows true fw.lengths fw.flag) (fun h => h)
  have runFrame := CppAppendRow.frame_appendRow_runs f slot ty _ old state resolved rfl run
  have rootBound := CppVectorStore.lookup_bound f.state.storage root old found
  have rwLengths := fw.lengths
  have forestLengths := (wellFormed_parts f.state fw.data.rows.valid).1
  have space := CppAppendRow.added_space f.state root (tag ty sc ids) ty old r fw.data.rows.valid found fw.data.rows.rootTag
  change state.liveSpace + old.capacity = f.state.liveSpace + r.buffer.capacity at space
  refine ⟨r,next,runFrame,?_,?_⟩
  · refine ⟨?_,fw.binding,?_,?_,(fun h => h),?_⟩
    · simpa [next,state,fw.measured.count] using data
    · simp [next,state,CppAppendRow.added,Forest.appendChild,fw.lengths]
    · change (f.rootWritable ++ [false])[root]? = some true
      rw [List.getElem?_append_left (by omega)]
      exact fw.flag
    · refine ⟨?_,?_,?_,?_,?_⟩
      · change state.liveSpace = m.live+r.buffer.capacity-old.capacity
        rw [fw.measured.live] at space
        omega
      · simp [next,state,CppAppendRow.added,afterRoot,fw.measured.work]
      · simp [next,state,CppAppendRow.added,afterRoot,fw.measured.live,fw.measured.peak,fw.measured.base]
      · simp [next,state,CppAppendRow.added,afterRoot,fw.measured.count]
      · exact fw.measured.base
  · simpa [next,state,fw.measured.live] using space

def afterRow (m : Resources) (old : Buffer Value) (r : Result Value Unit) : Resources :=
  ⟨m.live+r.buffer.capacity-old.capacity,m.work+r.work,
    max m.peak (m.live+(r.peak-(old.capacity+1))-m.base),m.count,m.base⟩

theorem FWR.addBinding {f : Frame} {slot root : Nat} {ty : Ty} {sc : Nat}
    {ids : List Nat} {epoch : Nat} {values : List (List Int)}
    {writable maximum : Bool} {m : Resources}
    (fw : FWR f slot root ty sc ids epoch values writable maximum m) (b : Binding) :
    FWR (f.addBinding b).1 slot root ty sc ids epoch values writable maximum m := by
  refine ⟨fw.data,?_,fw.lengths,fw.flag,fw.permission,⟨fw.measured.live,fw.measured.work,fw.measured.peak,fw.measured.count,fw.measured.base⟩⟩
  change (f.bindings ++ [b])[slot]? = _
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp fw.binding).1]
  exact fw.binding

theorem FWR.rebind {f : Frame} {slot root : Nat} {ty : Ty} {sc : Nat}
    {ids : List Nat} {epoch : Nat} {values : List (List Int)}
    {writable maximum : Bool} {m : Resources}
    (fw : FWR f slot root ty sc ids epoch values writable maximum m) (bs : List Binding)
    (binding : bs[slot]? = some ⟨root,.vector (.integer ty),writable,.root sc⟩) :
    FWR {f with bindings := bs} slot root ty sc ids epoch values writable maximum m :=
  ⟨fw.data,binding,fw.lengths,fw.flag,fw.permission,⟨fw.measured.live,fw.measured.work,fw.measured.peak,fw.measured.count,fw.measured.base⟩⟩

theorem FWR.transport {f : Frame} {slot root : Nat} {ty : Ty} {sc : Nat}
    {ids : List Nat} {epoch : Nat} {values : List (List Int)}
    {writable maximum : Bool} {m : Resources}
    (fw : FWR f slot root ty sc ids epoch values writable maximum m) (f' : Frame)
    (state : f'.state = f.state) (flags : f'.rootWritable = f.rootWritable)
    (binding : f'.bindings[slot]? = some ⟨root,.vector (.integer ty),writable,.root sc⟩) :
    FWR f' slot root ty sc ids epoch values writable maximum m := by
  refine ⟨?_,binding,?_,?_,fw.permission,?_⟩
  · rw [state]; exact fw.data
  · rw [flags,state]; exact fw.lengths
  · rw [flags]; exact fw.flag
  · refine ⟨?_,?_,?_,?_,?_⟩ <;> rw [state]
    · exact fw.measured.live
    · exact fw.measured.work
    · exact fw.measured.peak
    · exact fw.measured.count
    · exact fw.measured.base

theorem updateRow (f : Frame) (slot root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int)) (m : Resources)
    (writable maximum : Bool) (fw : FWR f slot root ty sc ids epoch values writable maximum m)
    (k owner : Nat) (lookup : ids[k]? = some owner) (old : Buffer Value)
    (found : f.state.storage.lookup owner = some old) (r : Result Value Unit) (row : List Int)
    (items : r.buffer.items = row.map Value.integer)
    (valid : (f.updated owner old r).state.wellFormed = true) :
    FWR (f.updated owner old r) slot root ty sc ids epoch (values.set k row)
      writable maximum (afterRow m old r) := by
  obtain ⟨b,object,bfound,earlier⟩ := row_object f root ty sc ids epoch k owner fw.data.rows lookup
  have equal : b = old := Option.some.inj (bfound.symm.trans found)
  subst b
  have facts := Proofs.CppNestedFacts.object_buffer f owner (.integer ty) old _ object
  have space := CppNestedGrowth.updated_space f owner old _ r found facts.2.2.1
  rw [fw.measured.live] at space
  refine ⟨updated_data f root ty sc ids epoch values fw.data k owner lookup old r row items valid,
    fw.binding,fw.lengths,fw.flag,fw.permission,?_⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · change _ = m.live+r.buffer.capacity-old.capacity
    omega
  · simp [Frame.updated,afterRow,fw.measured.work]
  · simp [Frame.updated,afterRow,fw.measured.live,fw.measured.peak,fw.measured.base]
  · simp [Frame.updated,afterRow,fw.measured.count]
  · exact fw.measured.base

theorem appendBound (f : Frame) (slot root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int)) (m : Resources)
    (fw : FWR f slot root ty sc ids epoch values true true m)
    (cb k owner : Nat) (lookup : ids[k]? = some owner)
    (binding : f.bindings[cb]? = some (CppRowsGraph.binding root ty epoch k owner true)) (old : Buffer Value)
    (found : f.state.storage.lookup owner = some old) (value : Int)
    (accepted : ty.valid value = true) (room : old.items.length < old.limit) :
    ∃ r next, f.append cb ty value = some next ∧
      FWR next slot root ty sc ids epoch
        (values.set k (values[k]?.getD [] ++ [value])) true true (afterRow m old r) ∧
      r.work + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old + 5 ∧
      r.peak ≤ 3*old.capacity+3 := by
  let b := CppRowsGraph.binding root ty epoch k owner true
  obtain ⟨buffer,resolved,bfound⟩ := resolve_row f cb root ty sc ids epoch k owner
    fw.data.rows lookup true true binding fw.lengths fw.flag (fun h => h)
  have equal : buffer = old := Option.some.inj (bfound.symm.trans found)
  subst buffer
  obtain ⟨objectBuffer,object,objectFound,_⟩ := row_object f root ty sc ids epoch k owner fw.data.rows lookup
  have same : objectBuffer = old := Option.some.inj (objectFound.symm.trans found)
  subst objectBuffer
  obtain ⟨valid,owns,bvalid,tagFound,element⟩ := Proofs.CppNestedRows.buffer_facts f owner ty old _ object
  obtain ⟨r,run,validNext,items,_,_,amort,peak,_⟩ := CppNestedGrowth.append_ok f cb ty value b old
    ⟨.integer ty,some root,none,[]⟩ resolved rfl valid object tagFound found rfl owns bvalid accepted room
  obtain ⟨previous,pfound,pitems⟩ := fw.data.contents k owner lookup
  have previousEqual : previous = old := Option.some.inj (pfound.symm.trans found)
  subst previous
  have contents : r.buffer.items = (values[k]?.getD [] ++ [value]).map Value.integer := by
    simpa [pitems,List.map_append] using items
  refine ⟨r,f.updated owner old r,?_,?_,amort,peak⟩
  · simpa [b,CppRowsGraph.binding,Frame.append] using run
  · exact updateRow f slot root ty sc ids epoch values m true true fw k owner lookup old found r _ contents validNext


theorem appendChild (f : Frame) (slot root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int)) (m : Resources)
    (fw : FWR f slot root ty sc ids epoch values true true m)
    (k owner : Nat) (lookup : ids[k]? = some owner) (old : Buffer Value)
    (found : f.state.storage.lookup owner = some old) (value : Int)
    (accepted : ty.valid value = true) (room : old.items.length < old.limit) :
    ∃ r next, ((f.child slot (.integer ty) k).bind fun p => p.1.append p.2 ty value) = some next ∧
      FWR next slot root ty sc ids epoch
        (values.set k (values[k]?.getD [] ++ [value])) true true (afterRow m old r) ∧
      r.work + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old + 5 ∧
      r.peak ≤ 3*old.capacity+3 := by
  let b := CppRowsGraph.binding root ty epoch k owner true
  let ff := (f.addBinding b).1
  have fw' : FWR ff slot root ty sc ids epoch values true true m := fw.addBinding b
  have chi := child_row f slot root ty sc ids epoch k owner fw.data.rows lookup true true
    fw.binding fw.lengths fw.flag (fun h => h)
  obtain ⟨r,next,run,post,amort,peak⟩ := appendBound ff slot root ty sc ids epoch values m fw'
    f.bindings.length k owner lookup (by simp [ff,b,Frame.addBinding]) old found value accepted room
  refine ⟨r,next,?_,post,amort,peak⟩
  simpa [chi,ff,b,Frame.addBinding] using run

end Proofs.CppRowsFrame
