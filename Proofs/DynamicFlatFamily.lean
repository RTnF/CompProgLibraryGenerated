import Proofs.DynamicOwnedAppendLayout

namespace Proofs.DynamicFlatFamily
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedFacts
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic

-- A flat root cannot be a row of any other root; ownership tags establish
-- separation even when root IDs and child IDs are noncontiguous.
theorem other (f : Frame) (root other : Nat) (ty : Ty) (sc : Nat) (old : Buffer Value)
    (r : Result Value Unit) (v : View) (model : Models f.state other v)
    (different : root ≠ other)
    (tag : f.state.forest.lookup root = some ⟨.integer ty,none,some sc,[]⟩)
    (valid : (f.updated root old r).state.wellFormed = true) :
    Models (f.updated root old r).state other v := by
  have rootBuffer := CppNestedOps.updated_lookup_other f root other old r different
  cases v with
  | flat t scope values =>
    obtain ⟨b,found,items⟩ := model.buffer
    exact ⟨valid,model.tag,b,rootBuffer.trans found,items⟩
  | rows t scope ids epoch values =>
    refine ⟨⟨valid,model.rows.rootTag,?_⟩,model.length,?_⟩
    · obtain ⟨b,found,epochs,items⟩ := model.rows.buffer
      exact ⟨b,rootBuffer.trans found,epochs,items⟩
    · intro k child lookup
      obtain ⟨b,found,items⟩ := model.contents k child lookup
      obtain ⟨buffer,obj,_,_⟩ := Proofs.CppRowsGraph.row_object f other t scope ids epoch k child model.rows lookup
      have facts := object_buffer f child (.integer t) buffer _ obj
      have distinct := root_ne_child f.state root child _ _ tag rfl facts.2.2.1 other rfl
      exact ⟨b,(CppNestedOps.updated_lookup_other f root child old r distinct).trans found,items⟩

theorem updated {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (root : Nat) (ty : Ty) (sc : Nat) (values nextValues : List Int)
    (lookup : h root = some (.flat ty sc values)) (old : Buffer Value)
    (found : f.state.storage.lookup root = some old) (r : Result Value Unit)
    (items : r.buffer.items = nextValues.map Value.integer)
    (valid : (f.updated root old r).state.wellFormed = true) :
    Family params (put h root (.flat ty sc nextValues)) (f.updated root old r) (resources (f.updated root old r)) := by
  have model : Flat f.state root ty sc values := family.models root _ lookup
  have nextModel : Flat (f.updated root old r).state root ty sc nextValues :=
    ⟨valid,model.tag,r.buffer,CppNestedOps.updated_lookup_self f root old r (lookup_bound f.state.storage root old found),items⟩
  have models : HeapModels (f.updated root old r).state (put h root (.flat ty sc nextValues)) := by
    apply heap_put _ h root (.flat ty sc nextValues) nextModel
    intro other different v hv
    exact DynamicFlatFamily.other f root other ty sc old r v (family.models other v hv) different.symm model.tag valid
  exact family.changed root (.flat ty sc values) (.flat ty sc nextValues) lookup rfl rfl _ _ models valid family.lengths family.bindings family.flags (measured_resources _)

theorem append {params : List Parameter} {h : Heap} {f : Frame} {m : Resources}
    (family : Family params h f m) (p : Parameter) (member : p ∈ params)
    (ty : Ty) (sc : Nat) (values : List Int) (lookup : h p.owner = some (.flat ty sc values))
    (writable : p.writable = true) (maximum : p.maximum = true)
    (old : Buffer Value) (found : f.state.storage.lookup p.owner = some old)
    (x : Int) (accepted : ty.valid x = true) (room : old.items.length < old.limit) :
    ∃ r, f.append p.slot ty x = some (f.updated p.owner old r) ∧
      Family params (put h p.owner (.flat ty sc (values ++ [x]))) (f.updated p.owner old r) (resources (f.updated p.owner old r)) ∧
      r.work+CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old+5 ∧
      r.peak ≤ 3*old.capacity+3 ∧ r.buffer.limit = old.limit ∧ r.buffer.items = old.items ++ [.integer x] := by
  have model : Flat f.state p.owner ty sc values := family.models p.owner _ lookup
  obtain ⟨view,hv,element,scope⟩ := family.views p member
  have equal : view = .flat ty sc values := Option.some.inj (hv.symm.trans lookup)
  subst view
  have binding : f.bindings[p.slot]? = some ⟨p.owner,.integer ty,true,.root sc⟩ := by
    simpa [Parameter.binding,← element,← scope,writable,View.element,View.scope] using family.bindings p member
  have obj := object_runs f p.owner (.integer ty) old _ family.valid found model.tag rfl
  have maxFlag : f.maximum p.owner = some true := maximum_runs f p.owner p.owner true family.lengths
    (Proofs.CppVectorOwnership.root_runs f.state.forest p.owner _ model.tag rfl) (by simpa [maximum] using family.flags p member)
  have resolved := resolve_root f p.slot (.integer ty) ⟨p.owner,.integer ty,true,.root sc⟩ sc old _ true
    binding rfl rfl obj rfl rfl maxFlag (fun h => h)
  obtain ⟨valid,owns,bvalid,tagFound,type⟩ := Proofs.CppNestedRows.buffer_facts f p.owner ty old _ obj
  obtain ⟨r,ran,nextValid,items,_,limit,amort,peak,_⟩ := CppNestedGrowth.append_ok f p.slot ty x _ old _ resolved rfl valid obj tagFound found rfl owns bvalid accepted room
  obtain ⟨prev,prevFound,prevItems⟩ := model.buffer
  have same : prev = old := Option.some.inj (prevFound.symm.trans found)
  subst prev
  have contents : r.buffer.items = (values ++ [x]).map Value.integer := by simpa [prevItems,List.map_append] using items
  exact ⟨r,by simpa [Frame.append] using ran,updated family p.owner ty sc values (values ++ [x]) lookup old found r contents nextValid,amort,peak,limit,items⟩

end Proofs.DynamicFlatFamily
