import Proofs.DynamicIndexRead

namespace Proofs.DynamicIndexAtoms
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedFacts
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim Proofs.CppRowsGraph
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicSizeSound
open Proofs.DynamicExprDerive Proofs.DynamicExprCertified

-- Evaluation of an index preserves the original logical environment even
-- when preceding indices or containers have left temporary bindings alive.
theorem index_ev {params : List Parameter} {l : Locals} {h : ContentsHeap} {idx : NExpr} {v : Int}
    (ready : Ready params l h idx) (value : denote params l h idx = some v)
    (s : NState) (realizes : Realizes params l h s) :
    ∀ u, Ext s u → ∃ t extra, Ev u idx t v extra (2*idx.nodes) (2*idx.nodes) := by
  intro u ext
  obtain ⟨_,t,extra,ev⟩ := DynamicExprCertified.sound (derive ready v value) u
    (DynamicExprCompose.in_extension params l h s u realizes ext)
  exact ⟨t,extra,ev⟩

theorem flat_read (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (slot : Nat) (p : Parameter)
    (location : locals.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc j : Nat) (values : List Int) (idx : NExpr) (x : Int)
    (lookup : contents p.owner = some (.flat ty sc values))
    (ready : Ready params locals contents idx) (idxValue : denote params locals contents idx = some (j : Int))
    (item : values[j]? = some x) : Atomic params locals contents (.read ty (.local slot) idx) x := by
  intro s realizes
  obtain ⟨h,m,family,he⟩ := realizes.heap
  have member := List.mem_of_find?_eq_some selected
  have hv := DynamicFlatSound.flat_lift h p.owner ty sc values (by rw [he]; exact lookup)
  have model : Flat s.frame.state p.owner ty sc values := family.models p.owner _ hv
  obtain ⟨view,vfound,ve,vs⟩ := family.views p member
  have same : view = .flat ty sc values := Option.some.inj (vfound.symm.trans hv)
  subst view
  have binding : s.frame.bindings[p.slot]? = some ⟨p.owner,.integer ty,p.writable,.root sc⟩ := by
    simpa [Parameter.binding,← ve,← vs,View.element,View.scope] using family.bindings p member
  obtain ⟨b,hb,hi⟩ := model.buffer
  have stored : b.items[j]? = some (.integer x) := by simp [hi,List.getElem?_map,item]
  have object := object_runs s.frame p.owner (.integer ty) b _ model.valid hb model.tag rfl
  obtain ⟨_,_,valid,_,_⟩ := Proofs.CppNestedRows.buffer_facts s.frame p.owner ty b _ object
  have accepted : ty.valid x = true := List.all_eq_true.mp valid.2.2 (.integer x) (List.mem_of_getElem? stored)
  obtain ⟨t,extra,ev⟩ := DynamicIndexEval.read_root s slot p.slot p.owner sc idx j ty p.writable p.maximum b x
    (2*idx.nodes) (2*idx.nodes) (index_ev ready idxValue s realizes)
    (vector_slot params locals contents s realizes slot p.slot location) binding model.valid model.tag hb
    family.lengths (family.flags p member) (family.permissions p member) stored
  have pure := DynamicExpr.read_root params locals contents slot p ty sc j values idx x location selected lookup ve.symm vs.symm
    idxValue item accepted
  exact ⟨pure,t,extra,ev.mono (by simp [NExpr.nodes,Container.nodes]; omega) (by simp [NExpr.nodes,Container.nodes]; omega)⟩

theorem row_size (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (slot : Nat) (p : Parameter)
    (location : locals.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc k : Nat) (values : List (List Int)) (vs : List Int) (idx : NExpr)
    (lookup : contents p.owner = some (.rows ty sc values))
    (ready : Ready params locals contents idx) (idxValue : denote params locals contents idx = some (k : Int))
    (row : values[k]? = some vs) (small : vs.length < 2^64) : Atomic params locals contents (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) (vs.length : Int) := by
  intro s realizes
  obtain ⟨ids,epoch,fw,element,scope⟩ := root_frame params locals contents s realizes p
    (List.mem_of_find?_eq_some selected) ty sc values lookup
  obtain ⟨owner,buffer,rowLookup,found,items⟩ := DynamicReadSound.row_buffer s p ty sc ids epoch values fw k vs row
  have sized : (⟨64,false,false⟩ : Ty).valid (vs.length : Int) = true := by simp [Ty.valid]; omega
  have pure := DynamicExpr.size_row params locals contents slot p ty sc k values vs idx location selected lookup element scope
    idxValue row sized
  obtain ⟨t,extra,ev⟩ := DynamicIndexRead.size_row s slot p.slot idx k p.owner sc epoch owner ids ty p.writable p.maximum buffer
    (2*idx.nodes) (2*idx.nodes) (index_ev ready idxValue s realizes)
    (vector_slot params locals contents s realizes slot p.slot location) fw.binding fw.data.rows fw.lengths fw.flag
    fw.permission rowLookup found (by simpa [items] using small)
  have actual : Ev s (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) t (vs.length : Int)
      (extra ++ [CppRowsGraph.binding p.owner ty epoch k owner p.writable]) (2*idx.nodes+3) (max (idx.nodes+4) (max (2*idx.nodes) 2)) := by simpa [items] using ev
  exact ⟨pure,t,_,actual.mono (by simp [NExpr.nodes,Container.nodes]; omega) (by simp [NExpr.nodes,Container.nodes]; omega)⟩


theorem row_read (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (slot : Nat) (p : Parameter)
    (location : locals.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc k j : Nat) (values : List (List Int)) (vs : List Int) (idx pos : NExpr) (x : Int)
    (lookup : contents p.owner = some (.rows ty sc values))
    (idxReady : Ready params locals contents idx) (idxValue : denote params locals contents idx = some (k : Int))
    (row : values[k]? = some vs) (posReady : Ready params locals contents pos)
    (posValue : denote params locals contents pos = some (j : Int)) (item : vs[j]? = some x) : Atomic params locals contents (.read ty (.row (.local slot) (.integer ty) idx) pos) x := by
  intro s realizes
  obtain ⟨ids,epoch,fw,element,scope⟩ := root_frame params locals contents s realizes p
    (List.mem_of_find?_eq_some selected) ty sc values lookup
  obtain ⟨owner,buffer,rowLookup,found,items⟩ := DynamicReadSound.row_buffer s p ty sc ids epoch values fw k vs row
  have stored : buffer.items[j]? = some (.integer x) := by simp [items,List.getElem?_map,item]
  obtain ⟨ob,obj,ofound,_⟩ := CppRowsGraph.row_object s.frame p.owner ty sc ids epoch k owner fw.data.rows rowLookup
  have same : ob = buffer := Option.some.inj (ofound.symm.trans found)
  subst ob
  obtain ⟨_,_,bvalid,_,_⟩ := Proofs.CppNestedRows.buffer_facts s.frame owner ty buffer _ obj
  have valid : ty.valid x = true := List.all_eq_true.mp bvalid.2.2 (.integer x) (List.mem_of_getElem? stored)
  have pure := DynamicExpr.read_row params locals contents slot p ty sc k j values vs idx pos x location selected lookup element scope
    idxValue row
    posValue item valid
  obtain ⟨t,extra1,extra2,ev⟩ := DynamicIndexRead.read_row s slot p.slot idx pos k j p.owner sc epoch owner ids ty x p.writable p.maximum
    buffer (2*idx.nodes) (2*idx.nodes) (2*pos.nodes) (2*pos.nodes) (index_ev idxReady idxValue s realizes)
    (vector_slot params locals contents s realizes slot p.slot location) fw.binding fw.data.rows fw.lengths fw.flag fw.permission
    rowLookup found stored (index_ev posReady posValue s realizes)
  exact ⟨pure,t,_,ev.mono (by simp [NExpr.nodes,Container.nodes]; omega) (by simp [NExpr.nodes,Container.nodes]; omega)⟩

end Proofs.DynamicIndexAtoms
