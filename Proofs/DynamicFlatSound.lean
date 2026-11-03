import Proofs.DynamicReadSound

namespace Proofs.DynamicFlatSound
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedFacts
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicSizeSound

theorem flat_lift (h : Heap) (root : Nat) (ty : Ty) (sc : Nat) (values : List Int)
    (lookup : eraseHeap h root = some (.flat ty sc values)) : h root = some (.flat ty sc values) := by
  cases found : h root with
  | none => simp [eraseHeap,found] at lookup
  | some view =>
    cases view with
    | rows t scope ids epoch vs => simp [eraseHeap,found,erase] at lookup
    | flat t scope vs =>
      simp only [eraseHeap,found,Option.map_some,erase,Option.some.injEq,Contents.flat.injEq] at lookup
      obtain ⟨rfl,rfl,rfl⟩ := lookup
      rfl

theorem size_flat (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s : NState) (realizes : Realizes params locals contents s) (slot : Nat) (p : Parameter)
    (location : locals.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc : Nat) (values : List Int)
    (lookup : contents p.owner = some (.flat ty sc values)) (small : values.length < 2^64) :
    DynamicExpr.denote params locals contents (.size (.integer ty) (.local slot)) = some (values.length : Int) ∧
      ∃ t, Ev s (.size (.integer ty) (.local slot)) t (values.length : Int) [] 3 3 ∧
        Realizes params locals contents ((t.release s).charge 1 0) := by
  obtain ⟨h,m,family,he⟩ := realizes.heap
  have member := List.mem_of_find?_eq_some selected
  have hv := flat_lift h p.owner ty sc values (by rw [he]; exact lookup)
  have model : Flat s.frame.state p.owner ty sc values := family.models p.owner _ hv
  obtain ⟨view,vfound,ve,vs⟩ := family.views p member
  have same : view = .flat ty sc values := Option.some.inj (vfound.symm.trans hv)
  subst view
  have binding : s.frame.bindings[p.slot]? = some ⟨p.owner,.integer ty,p.writable,.root sc⟩ := by
    simpa [Parameter.binding,← ve,← vs,View.element,View.scope] using family.bindings p member
  obtain ⟨b,hb,hi⟩ := model.buffer
  obtain ⟨t,ev⟩ := Ev.sizeRoot s slot p.slot p.owner sc ty p.writable p.maximum b
    (vector_slot params locals contents s realizes slot p.slot location) binding model.valid model.tag hb
    family.lengths (family.flags p member) (family.permissions p member) (by simpa [hi] using small)
  have actual : Ev s (.size (.integer ty) (.local slot)) t (values.length : Int) [] 3 3 := by simpa [hi] using ev
  have pure := DynamicExpr.size_root params locals contents slot p (.flat ty sc values) location selected lookup ve vs
  have sized : (⟨64,false,false⟩ : Ty).valid (values.length : Int) = true := by simp [Ty.valid]; omega
  refine ⟨?_,t,actual,(ev_preserves params locals contents s t realizes _ _ [] 3 3 actual).1⟩
  simpa [Contents.element,Contents.length,sized] using pure

theorem read_flat (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s : NState) (realizes : Realizes params locals contents s) (slot : Nat) (p : Parameter)
    (location : locals.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc j : Nat) (values : List Int) (idx : NExpr) (x : Int)
    (lookup : contents p.owner = some (.flat ty sc values))
    (scalar : idx.scalarOnly = true) (idxValue : idx.denote (environment locals) = some (j : Int))
    (item : values[j]? = some x) :
    DynamicExpr.denote params locals contents (.read ty (.local slot) idx) = some x ∧
      ∃ t, Ev s (.read ty (.local slot) idx) t x [] (idx.nodes+3) (idx.nodes+3) ∧
        Realizes params locals contents ((t.release s).charge 1 0) := by
  obtain ⟨h,m,family,he⟩ := realizes.heap
  have member := List.mem_of_find?_eq_some selected
  have hv := flat_lift h p.owner ty sc values (by rw [he]; exact lookup)
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
  have value : idx.denote (envOf s) = some (j : Int) := by rw [← snapshot_env,realizes.locals]; exact idxValue
  obtain ⟨t,ev⟩ := Ev.readRoot s slot p.slot p.owner sc idx j ty p.writable p.maximum b x scalar value
    (vector_slot params locals contents s realizes slot p.slot location) binding model.valid model.tag hb
    family.lengths (family.flags p member) (family.permissions p member) stored
  have pure := DynamicExpr.read_root params locals contents slot p ty sc j values idx x location selected lookup ve.symm vs.symm
    (by rw [DynamicExpr.denote_scalar _ _ _ _ scalar]; exact idxValue) item accepted
  exact ⟨pure,t,ev,(ev_preserves params locals contents s t realizes _ _ [] _ _ ev).1⟩

end Proofs.DynamicFlatSound
