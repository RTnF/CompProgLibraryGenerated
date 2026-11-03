import Proofs.MultiVecDynamic
import Proofs.CppRowsSteps

namespace Proofs.MultiVecDynamicSteps
open Proofs.CppScalar Proofs.CppVector Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedEval Proofs.CppNestedSim Proofs.CppNestedStmt
open Proofs.CppRowsGraph Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic

theorem appendRoot_stmt (s : NState) (params : List Parameter) (h : Heap) (m : Resources)
    (family : Family params h s.frame m) (p : Parameter) (member : p ∈ params)
    (localSlot : Nat) (hslot : s.vectorSlot localSlot = some p.slot)
    (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat) (values : List (List Int))
    (lookup : h p.owner = some (.rows ty sc ids epoch values))
    (writable : p.writable = true) (maximum : p.maximum = true)
    (old : Buffer Value) (found : s.frame.state.storage.lookup p.owner = some old)
    (room : old.items.length < old.limit) :
    ∃ r t, (NStmt.appendRow (.local localSlot) ty).run s = some ⟨t,none,false⟩ ∧
      Family params (put h p.owner (.rows ty sc (ids ++ [m.count]) r.buffer.epoch (values ++ [[]])))
        t.frame (afterRoot m old r) ∧ t.scalars.work = s.scalars.work+2 := by
  obtain ⟨r,frame,run,post⟩ := family.appendRoot p member ty sc ids epoch values lookup writable maximum old found room
  let next := (s.charge 0 ((Container.local localSlot).nodes+2)).charge 1 1
  have eval : (Container.local localSlot).eval (s.charge 0 ((Container.local localSlot).nodes+2)) =
      some (next,p.slot) := eval_local _ localSlot p.slot (by simpa [NState.vectorSlot] using hslot)
  have ran := Proofs.AppendRowStmt.appendRow_stmt s next (.local localSlot) p.slot ty frame eval run
  let t := (({next with frame := frame} : NState).release s).charge 1 1
  refine ⟨r,t,ran,post.rebind _ ?_,?_⟩
  · intro q hq
    have inside := (List.getElem?_eq_some_iff.mp (family.bindings q hq)).1
    rw [List.getElem?_take_of_lt inside]
    exact post.bindings q hq
  · simp [t,next,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]

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
      r.peak ≤ 3*old.capacity+3 := by
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
  obtain ⟨r,frame,run,post,amort,peak⟩ := family2.appendBound p member ty sc ids epoch values lookup writable maximum
    s.frame.bindings.length k owner rowLookup (by simp [bindings2]) old (by rw [good.1]; exact found) x accepted room
  let t := (({t2 with frame := frame} : NState).release s).charge 1 1
  refine ⟨r,t,?_,post.rebind _ ?_,?_,?_,amort,peak⟩
  · have evalRow : (Container.row (.local localSlot) (.integer ty) idx).eval
        (s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)) =
          some (t1,s.frame.bindings.length) := hrow
    simp [NStmt.run,evalRow,hvalue,run,t]
  · intro q hq
    have inside := (List.getElem?_eq_some_iff.mp (family.bindings q hq)).1
    rw [List.getElem?_take_of_lt inside]
    exact post.bindings q hq
  · have lower := good.2.2.2.2.2.2.2.1
    have work : t.scalars.work = t2.scalars.work+1 := by
      simp [t,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]
    omega
  · have upper := good.2.2.2.2.2.2.2.2.1
    have work : t.scalars.work = t2.scalars.work+1 := by
      simp [t,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]
    omega

end Proofs.MultiVecDynamicSteps
