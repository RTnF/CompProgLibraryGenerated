import Proofs.DynamicRealizes

namespace Proofs.DynamicSizeSound
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.CppRowsContents
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes

-- Lift a contents lookup to allocation metadata supplied by Realizes.
theorem rows_lift (h : Heap) (root : Nat) (ty : Ty) (sc : Nat) (values : List (List Int))
    (lookup : eraseHeap h root = some (.rows ty sc values)) :
    ∃ ids epoch, h root = some (.rows ty sc ids epoch values) := by
  cases found : h root with
  | none => simp [eraseHeap,found] at lookup
  | some view =>
    cases view with
    | flat t scope vs => simp [eraseHeap,found,erase] at lookup
    | rows t scope ids epoch vs =>
      simp only [eraseHeap,found,Option.map_some,erase,Option.some.injEq,Contents.rows.injEq] at lookup
      obtain ⟨rfl,rfl,rfl⟩ := lookup
      exact ⟨ids,epoch,rfl⟩

theorem root_frame (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s : NState) (realizes : Realizes params locals contents s) (p : Parameter)
    (member : p ∈ params) (ty : Ty) (sc : Nat) (values : List (List Int))
    (lookup : contents p.owner = some (.rows ty sc values)) :
    ∃ ids epoch, FWR s.frame p.slot p.owner ty sc ids epoch values p.writable p.maximum
      (resources s.frame) ∧ p.element = .vector (.integer ty) ∧ p.scope = sc := by
  obtain ⟨h,m,family,he⟩ := realizes.heap
  have logical : eraseHeap h p.owner = some (.rows ty sc values) := by rw [he]; exact lookup
  obtain ⟨ids,epoch,hv⟩ := rows_lift h p.owner ty sc values logical
  have fw := family.row_frame p member ty sc ids epoch values hv
  obtain ⟨view,vfound,ve,vs⟩ := family.views p member
  have same : view = .rows ty sc ids epoch values := Option.some.inj (vfound.symm.trans hv)
  subst view
  have metrics : m = resources s.frame := by
    obtain ⟨ml,mw,mp,mc,mb⟩ := fw.measured
    cases m
    simp_all [resources]
  rw [metrics] at fw
  exact ⟨ids,epoch,fw,ve.symm,vs.symm⟩

theorem vector_slot (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s : NState) (realizes : Realizes params locals contents s) (slot rb : Nat)
    (location : locals.slots[slot]? = some (.vector rb)) : s.vectorSlot slot = some rb := by
  rw [← realizes.locals] at location
  have found : s.slots[slot]? = some (.vector rb) := by simpa [snapshot] using location
  simp [NState.vectorSlot,found]

theorem root_size (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s : NState) (realizes : Realizes params locals contents s) (slot : Nat) (p : Parameter)
    (location : locals.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc : Nat) (values : List (List Int))
    (lookup : contents p.owner = some (.rows ty sc values)) (small : values.length < 2^64) :
    DynamicExpr.denote params locals contents (.size (.vector (.integer ty)) (.local slot)) = some (values.length : Int) ∧
      ∃ t, Ev s (.size (.vector (.integer ty)) (.local slot)) t (values.length : Int) [] 3 3 ∧
        Realizes params locals contents ((t.release s).charge 1 0) := by
  obtain ⟨h,m,family,he⟩ := realizes.heap
  have member : p ∈ params := List.mem_of_find?_eq_some selected
  have logical : eraseHeap h p.owner = some (.rows ty sc values) := by rw [he]; exact lookup
  obtain ⟨ids,epoch,hv⟩ := rows_lift h p.owner ty sc values logical
  have fw := family.row_frame p member ty sc ids epoch values hv
  obtain ⟨view,vfound,ve,vs⟩ := family.views p member
  have same : view = .rows ty sc ids epoch values := Option.some.inj (vfound.symm.trans hv)
  subst view
  have element : (.rows ty sc values : Contents).element = p.element := ve
  have scope : (.rows ty sc values : Contents).scope = p.scope := vs
  have sized : (⟨64,false,false⟩ : Ty).valid (values.length : Int) = true := by simp [Ty.valid]; omega
  have pure := DynamicExpr.size_root params locals contents slot p (.rows ty sc values) location selected lookup element scope
  have slotActual : s.vectorSlot slot = some p.slot := by
    rw [← realizes.locals] at location
    have found : s.slots[slot]? = some (.vector p.slot) := by simpa [snapshot] using location
    simp [NState.vectorSlot,found]
  obtain ⟨t,ev⟩ := DynamicRowsRead.Ev.sizeNested s slot p.slot p.owner sc epoch ids ty p.writable p.maximum
    slotActual fw.binding fw.data.rows fw.lengths fw.flag fw.permission (by rw [← fw.data.length]; exact small)
  have actual : Ev s (.size (.vector (.integer ty)) (.local slot)) t (values.length : Int) [] 3 3 := by
    simpa [← fw.data.length] using ev
  refine ⟨?_,t,actual,(ev_preserves params locals contents s t realizes _ _ [] 3 3 actual).1⟩
  simpa [Contents.element,Contents.length,sized] using pure

end Proofs.DynamicSizeSound
