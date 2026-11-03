import Proofs.DynamicSizeSound

namespace Proofs.DynamicReadSound
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedSim Proofs.CppNestedFacts
open Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppRowsGraph Proofs.CppRowsContents
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicSizeSound

-- The row's storage owner is a witness, not an arithmetic function of its index.
theorem row_buffer (s : NState) (p : Parameter) (ty : Ty) (sc : Nat) (ids : List Nat) (epoch : Nat)
    (values : List (List Int)) (fw : FWR s.frame p.slot p.owner ty sc ids epoch values p.writable p.maximum (resources s.frame))
    (k : Nat) (vs : List Int) (row : values[k]? = some vs) :
    ∃ owner buffer, ids[k]? = some owner ∧ s.frame.state.storage.lookup owner = some buffer ∧
      buffer.items = vs.map Value.integer := by
  have bound : k < ids.length := by rw [← fw.data.length]; exact (List.getElem?_eq_some_iff.mp row).1
  obtain ⟨owner,lookup⟩ : ∃ owner, ids[k]? = some owner := ⟨ids[k],by simp⟩
  obtain ⟨b,hb,hi⟩ := fw.data.contents k owner lookup
  exact ⟨owner,b,lookup,hb,by simpa [row] using hi⟩

theorem row_size (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s : NState) (realizes : Realizes params locals contents s) (slot : Nat) (p : Parameter)
    (location : locals.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc k : Nat) (values : List (List Int)) (vs : List Int) (idx : NExpr)
    (lookup : contents p.owner = some (.rows ty sc values))
    (scalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (row : values[k]? = some vs) (small : vs.length < 2^64) :
    DynamicExpr.denote params locals contents (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) = some (vs.length : Int) ∧
      ∃ t extra, Ev s (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) t (vs.length : Int)
        extra (idx.nodes+3) (idx.nodes+4) ∧ Realizes params locals contents ((t.release s).charge 1 0) := by
  obtain ⟨ids,epoch,fw,element,scope⟩ := root_frame params locals contents s realizes p
    (List.mem_of_find?_eq_some selected) ty sc values lookup
  obtain ⟨owner,buffer,rowLookup,found,items⟩ := row_buffer s p ty sc ids epoch values fw k vs row
  have sized : (⟨64,false,false⟩ : Ty).valid (vs.length : Int) = true := by simp [Ty.valid]; omega
  have pure := DynamicExpr.size_row params locals contents slot p ty sc k values vs idx location selected lookup element scope
    (by rw [scalar_denote params locals contents s realizes idx scalar]; exact idxValue) row sized
  obtain ⟨t,ev⟩ := DynamicRowsRead.Ev.sizeRow s slot p.slot idx k p.owner sc epoch owner ids ty p.writable p.maximum buffer
    scalar idxValue (vector_slot params locals contents s realizes slot p.slot location) fw.binding fw.data.rows fw.lengths fw.flag
    fw.permission rowLookup found (by simpa [items] using small)
  have actual : Ev s (.size (.integer ty) (.row (.local slot) (.integer ty) idx)) t (vs.length : Int)
      [CppRowsGraph.binding p.owner ty epoch k owner p.writable] (idx.nodes+3) (idx.nodes+4) := by simpa [items] using ev
  exact ⟨pure,t,_,actual,(ev_preserves params locals contents s t realizes _ _ _ _ _ actual).1⟩

theorem row_read (params : List Parameter) (locals : Locals) (contents : ContentsHeap)
    (s : NState) (realizes : Realizes params locals contents s) (slot : Nat) (p : Parameter)
    (location : locals.slots[slot]? = some (.vector p.slot))
    (selected : params.find? (fun q => q.slot == p.slot) = some p)
    (ty : Ty) (sc k j : Nat) (values : List (List Int)) (vs : List Int) (idx pos : NExpr) (x : Int)
    (lookup : contents p.owner = some (.rows ty sc values))
    (idxScalar : idx.scalarOnly = true) (idxValue : idx.denote (envOf s) = some (k : Int))
    (row : values[k]? = some vs) (posScalar : pos.scalarOnly = true)
    (posValue : pos.denote (envOf s) = some (j : Int)) (item : vs[j]? = some x) :
    DynamicExpr.denote params locals contents (.read ty (.row (.local slot) (.integer ty) idx) pos) = some x ∧
      ∃ t extra, Ev s (.read ty (.row (.local slot) (.integer ty) idx) pos) t x
        extra (idx.nodes+pos.nodes+3) (idx.nodes+pos.nodes+4) ∧
          Realizes params locals contents ((t.release s).charge 1 0) := by
  obtain ⟨ids,epoch,fw,element,scope⟩ := root_frame params locals contents s realizes p
    (List.mem_of_find?_eq_some selected) ty sc values lookup
  obtain ⟨owner,buffer,rowLookup,found,items⟩ := row_buffer s p ty sc ids epoch values fw k vs row
  have stored : buffer.items[j]? = some (.integer x) := by simp [items,List.getElem?_map,item]
  obtain ⟨ob,obj,ofound,_⟩ := CppRowsGraph.row_object s.frame p.owner ty sc ids epoch k owner fw.data.rows rowLookup
  have same : ob = buffer := Option.some.inj (ofound.symm.trans found)
  subst ob
  obtain ⟨_,_,bvalid,_,_⟩ := Proofs.CppNestedRows.buffer_facts s.frame owner ty buffer _ obj
  have valid : ty.valid x = true := List.all_eq_true.mp bvalid.2.2 (.integer x) (List.mem_of_getElem? stored)
  have pure := DynamicExpr.read_row params locals contents slot p ty sc k j values vs idx pos x location selected lookup element scope
    (by rw [scalar_denote params locals contents s realizes idx idxScalar]; exact idxValue) row
    (by rw [scalar_denote params locals contents s realizes pos posScalar]; exact posValue) item valid
  have posEv : ∀ u, Ext s u → ∃ u2, Ev u pos u2 (j : Int) [] pos.nodes pos.nodes := by
    intro u ext
    obtain ⟨_,_,_,slots,_,memory,bindings,_⟩ := ext
    have env : envOf u = envOf s := by
      funext slot ty
      simp [envOf,NState.scalarCell,NState.scalarSlot,slots,memory,bindings]
    exact Ev.scalar posScalar (by rw [env]; exact posValue)
  obtain ⟨t,ev⟩ := DynamicRowsRead.Ev.readRow s slot p.slot idx pos k j p.owner sc epoch owner ids ty x p.writable p.maximum
    buffer [] pos.nodes pos.nodes idxScalar idxValue (vector_slot params locals contents s realizes slot p.slot location)
    fw.binding fw.data.rows fw.lengths fw.flag fw.permission rowLookup found stored posEv
  have actual : Ev s (.read ty (.row (.local slot) (.integer ty) idx) pos) t x
      ([CppRowsGraph.binding p.owner ty epoch k owner p.writable] ++ [])
      (idx.nodes+pos.nodes+3) (idx.nodes+pos.nodes+4) := ev.mono (by omega) (by omega)
  exact ⟨pure,t,_,actual,(ev_preserves params locals contents s t realizes _ _ _ _ _ actual).1⟩

end Proofs.DynamicReadSound
