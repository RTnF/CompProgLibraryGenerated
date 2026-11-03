import Proofs.CppRowsFrame
import Proofs.CppRowsStmt
import Proofs.AppendRowStmt

namespace Proofs.CppRowsSteps
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt
open Proofs.CppRowsGraph Proofs.CppRowsFrame

-- A successful statement restores the pre-expression binding lifetime while
-- retaining the dynamic allocation and logical-content changes.
theorem appendRoot_stmt (s : NState) (localSlot slot root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int)) (m : Resources)
    (fw : FWR s.frame slot root ty sc ids epoch values true true m)
    (hslot : s.vectorSlot localSlot = some slot) (old : Buffer Value)
    (found : s.frame.state.storage.lookup root = some old) (room : old.items.length < old.limit) :
    ∃ r t, (NStmt.appendRow (.local localSlot) ty).run s = some ⟨t,none,false⟩ ∧
      FWR t.frame slot root ty sc (ids ++ [m.count]) r.buffer.epoch (values ++ [[]])
        true true (afterRoot m old r) ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧ t.scalars.work = s.scalars.work+2 := by
  obtain ⟨r,frame,run,post,space⟩ := appendRoot s.frame slot root ty sc ids epoch values m fw old found room
  let next := (s.charge 0 ((Container.local localSlot).nodes+2)).charge 1 1
  have eval : (Container.local localSlot).eval (s.charge 0 ((Container.local localSlot).nodes+2)) =
      some (next,slot) := eval_local _ localSlot slot (by simpa [NState.vectorSlot] using hslot)
  have ran := Proofs.AppendRowStmt.appendRow_stmt s next (.local localSlot) slot ty frame eval run
  let t := (({next with frame := frame} : NState).release s).charge 1 1
  have inside : slot < s.frame.bindings.length := (List.getElem?_eq_some_iff.mp fw.binding).1
  have bound : (frame.bindings.take s.frame.bindings.length)[slot]? =
      some ⟨root,.vector (.integer ty),true,.root sc⟩ := by
    rw [List.getElem?_take_of_lt inside]
    exact post.binding
  refine ⟨r,t,ran,?_,?_,?_,?_,?_,?_⟩
  · exact post.rebind _ bound
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [t,next,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]

theorem appendChild_stmt (s : NState) (localSlot slot root : Nat) (ty : Ty) (sc : Nat)
    (ids : List Nat) (epoch : Nat) (values : List (List Int)) (m : Resources)
    (fw : FWR s.frame slot root ty sc ids epoch values true true m)
    (hslot : s.vectorSlot localSlot = some slot) (idx value : NExpr) (k owner : Nat) (x : Int)
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (vScalar : value.scalarOnly = true) (vValue : value.denote (envOf s) = some x)
    (lookup : ids[k]? = some owner) (old : Buffer Value)
    (found : s.frame.state.storage.lookup owner = some old)
    (accepted : ty.valid x = true) (room : old.items.length < old.limit) :
    ∃ r t, (NStmt.append (.row (.local localSlot) (.integer ty) idx) ty value).run s = some ⟨t,none,false⟩ ∧
      FWR t.frame slot root ty sc ids epoch (values.set k (values[k]?.getD [] ++ [x]))
        true true (afterRow m old r) ∧
      t.slots = s.slots ∧ t.scope = s.scope ∧ t.scalars.memory = s.scalars.memory ∧
      t.scalars.bindings = s.scalars.bindings ∧
      s.scalars.work ≤ t.scalars.work ∧ t.scalars.work ≤ s.scalars.work+idx.nodes+value.nodes+3 ∧
      r.work + CppVectorGrowth.potential r.buffer ≤ CppVectorGrowth.potential old + 5 ∧
      r.peak ≤ 3*old.capacity+3 := by
  let start := s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)
  obtain ⟨t1,hrow,good1,bindings1⟩ := CppRowsStmt.eval_row start localSlot slot idx k root sc epoch owner ids ty
    idxScalar (by rw [envOf_core (core_charge _ _ _)]; exact idxValue)
    (by simpa [NState.vectorSlot,start] using hslot) fw.binding fw.data.rows fw.lengths fw.flag lookup
  have goodStart : GoodF s start 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2) :=
    GoodF.charge s 0 _
  have goodRow := goodStart.trans good1
  obtain ⟨t2,hvalue,good2⟩ := scalar_eval value t1 x vScalar
    (by rw [envOf_goodF goodRow]; exact vValue)
  have good := goodRow.trans good2.toF
  have bindings2 : t2.frame.bindings = s.frame.bindings ++ [CppRowsGraph.binding root ty epoch k owner true] := by
    rw [good2.1.1,bindings1]; rfl
  have inside : slot < s.frame.bindings.length := (List.getElem?_eq_some_iff.mp fw.binding).1
  have rootBinding : t2.frame.bindings[slot]? = some ⟨root,.vector (.integer ty),true,.root sc⟩ := by
    rw [bindings2,List.getElem?_append_left inside]
    exact fw.binding
  have fw2 := fw.transport t2.frame good.1 good.2.1 rootBinding
  obtain ⟨r,frame,run,post,amort,peak⟩ := appendBound t2.frame slot root ty sc ids epoch values m fw2
    s.frame.bindings.length k owner lookup (by simp [bindings2]) old (by rw [good.1]; exact found) x accepted room
  let t := (({t2 with frame := frame} : NState).release s).charge 1 1
  have bound : (frame.bindings.take s.frame.bindings.length)[slot]? =
      some ⟨root,.vector (.integer ty),true,.root sc⟩ := by
    rw [List.getElem?_take_of_lt inside]
    exact post.binding
  refine ⟨r,t,?_,post.rebind _ bound,?_,?_,?_,?_,?_,?_,amort,peak⟩
  · have evalRow : (Container.row (.local localSlot) (.integer ty) idx).eval
        (s.charge 0 ((Container.row (.local localSlot) (.integer ty) idx).nodes+value.nodes+2)) =
          some (t1,s.frame.bindings.length) := hrow
    simp [NStmt.run,evalRow,hvalue,run,t]
  · simpa [t,NState.release] using good.2.2.1
  · simpa [t,NState.release] using good.2.2.2.1
  · simpa [t,NState.release] using good.2.2.2.2.1
  · simpa [t,NState.release] using good.2.2.2.2.2.1
  · have lower := good.2.2.2.2.2.2.2.1
    have work : t.scalars.work = t2.scalars.work+1 := by
      simp [t,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]
    omega
  · have upper := good.2.2.2.2.2.2.2.2.1
    have work : t.scalars.work = t2.scalars.work+1 := by
      simp [t,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe]
    omega

end Proofs.CppRowsSteps
