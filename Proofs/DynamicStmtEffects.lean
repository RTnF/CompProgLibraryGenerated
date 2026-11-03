import Proofs.DynamicCallEffects

namespace Proofs.DynamicStmtEffects
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppVector Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedStmt Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicPhysicalEffects Proofs.DynamicResultValid Proofs.DynamicExprCertified

-- A successful buffer commit retains the ownership forest and owner flags.
theorem commit (f next : Frame) (owner : Nat) (element : Element) (r : Result Value Unit)
    (run : f.commit owner element r = some next) : Authority f next := by
  unfold Frame.commit at run
  split at run
  · contradiction
  · split at run
    · dsimp only at run
      split at run
      · have same := Option.some.inj run
        subst next; exact updated _ _ _ _
      · contradiction
    · contradiction

theorem append_frame (f next : Frame) (slot : Nat) (ty : Ty) (value : Int)
    (run : f.append slot ty value = some next) : Authority f next := by
  unfold Frame.append Frame.appendGrowing at run
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
  obtain ⟨binding,buffer⟩ := pair
  obtain ⟨r,_,appended⟩ := bind_some _ _ _ rest
  exact commit f next binding.owner (.integer ty) r appended

-- Pure success supplies an expression value; its certified evaluation gives
-- the physical core preservation, independently of scalar writes afterwards.
theorem scalar (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (real : Realizes params st.locals st.contents s) (stmt : NStmt) (form : DynamicStmtAuto.ScalarForm stmt)
    (result : DynamicStmt.Step) (pure : DynamicStmt.run params stmt st = some result)
    (out : NStep) (actual : stmt.run s = some out) : Change s out.state := by
  have eval (e : NExpr) (v : Int) (value : denote params st.locals st.contents e = some v) :=
    DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready params st.locals st.contents e) v value) s real
  cases stmt with
  | skip =>
    have same : (⟨s,none,false⟩ : NStep) = out := Option.some.inj actual
    subst out; exact Change.refl s
  | declare ty wr e =>
    obtain ⟨v,value,_⟩ := bind_some _ _ _ pure
    obtain ⟨_,t,extra,ev⟩ := eval e v value
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind] at actual
    obtain ⟨x,_,same⟩ := bind_some _ _ _ actual
    have equal := Option.some.inj same
    subst out
    exact ⟨Authority.same (congrArg State.forest ev.2.1.1) ev.2.1.2.1,ev.2.1.2.2.2.1⟩
  | assign slot ty e =>
    obtain ⟨v,value,_⟩ := bind_some _ _ _ pure
    obtain ⟨_,t,extra,ev⟩ := eval e v value
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind] at actual
    obtain ⟨pair,_,rest⟩ := bind_some _ _ _ actual
    obtain ⟨binding,cell⟩ := pair
    cases wr : binding.writable with
    | false => simp [wr] at rest
    | true =>
      simp only [wr,ite_true] at rest
      obtain ⟨x,_,same⟩ := bind_some _ _ _ rest
      have equal := Option.some.inj same
      subst out
      exact ⟨Authority.same (congrArg State.forest ev.2.1.1) ev.2.1.2.1,ev.2.1.2.2.2.1⟩
  | ret e =>
    obtain ⟨v,value,_⟩ := bind_some _ _ _ pure
    obtain ⟨_,t,extra,ev⟩ := eval e v value
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind] at actual
    have equal := Option.some.inj actual
    subst out
    exact ⟨Authority.same (congrArg State.forest ev.2.1.1) ev.2.1.2.1,ev.2.1.2.2.2.1⟩
  | check e =>
    obtain ⟨v,value,_⟩ := bind_some _ _ _ pure
    obtain ⟨_,t,extra,ev⟩ := eval e v value
    simp only [NStmt.run,ev.1,Bind.bind,Option.bind] at actual
    split at actual
    · contradiction
    · have equal := Option.some.inj actual
      subst out
      exact ⟨Authority.same (congrArg State.forest ev.2.1.1) ev.2.1.2.1,ev.2.1.2.2.2.1⟩
  | _ => simp [DynamicStmtAuto.ScalarForm] at form

-- Actual success supplies append's allocation check. This effect theorem
-- therefore needs no extra RoomAt assumption, unlike constructing success.
theorem child (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (real : Realizes params st.locals st.contents s) (slot : Nat) (element ty : Ty) (idx value : NExpr)
    (result : DynamicStmt.Step)
    (pure : DynamicStmt.run params (.append (.row (.local slot) (.integer element) idx) ty value) st = some result)
    (out : NStep) (actual : (NStmt.append (.row (.local slot) (.integer element) idx) ty value).run s = some out) : Change s out.state := by
  obtain ⟨p,sc,k,values,row,x,mutable,elementEq,lookup,index,val,item,accepted,_⟩ := DynamicAppendDecode.child params st slot element ty idx value result pure
  subst element
  obtain ⟨location,selected,writable,maximum,_,_⟩ := DynamicAppendSound.mutable_found params st slot _ p mutable
  obtain ⟨heap,m,family,he⟩ := real.heap
  obtain ⟨ids,epoch,hv⟩ := DynamicSizeSound.rows_lift heap p.owner ty sc values (by rw [he]; exact lookup)
  have fw := family.row_frame p (List.mem_of_find?_eq_some selected) ty sc ids epoch values hv
  have bound : k < ids.length := by rw [← fw.data.length]; exact (List.getElem?_eq_some_iff.mp item).1
  obtain ⟨owner,rowLookup⟩ : ∃ owner, ids[k]? = some owner := ⟨ids[k],by simp⟩
  rw [writable,maximum] at fw
  let start := s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)
  obtain ⟨t1,idxExtra,hrow,good1,bindings1⟩ := DynamicIndexEval.eval_row start slot p.slot idx k p.owner sc epoch owner ids ty true true
    (2*idx.nodes) (2*idx.nodes)
    (fun u ext => DynamicIndexAtoms.index_ev (DynamicExprAuto.ready _ _ _ _) index s real u ((Ext.charge s 0 _).trans ext))
    (by simpa [NState.vectorSlot,start] using DynamicSizeSound.vector_slot params st.locals st.contents s real slot p.slot location)
    fw.binding fw.data.rows fw.lengths fw.flag (fun h => h) rowLookup
  have firstGood := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)).trans good1
  have real1 := DynamicExprCompose.in_extension params st.locals st.contents s t1 real (Ext.of_goodF firstGood bindings1)
  obtain ⟨_,t2,extra,ev⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) x val) t1 real1
  have good := firstGood.trans ev.2.1
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)) =
      some (t1,s.frame.bindings.length+idxExtra.length) := hrow
  simp only [NStmt.run,evalRow,ev.1,Bind.bind,Option.bind] at actual
  obtain ⟨frame,appended,same⟩ := bind_some _ _ _ actual
  have equal := Option.some.inj same
  subst out
  exact ⟨(goodF good).1.trans ((append_frame t2.frame frame _ _ _ appended).trans (Authority.same rfl rfl)),(goodF good).2⟩

theorem effects (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (real : Realizes params st.locals st.contents s) (stmt : NStmt) (result : DynamicStmt.Step)
    (pure : DynamicStmt.run params stmt st = some result) (out : NStep) (actual : stmt.run s = some out) : Change s out.state := by
  cases stmt with
  | skip | declare _ _ _ | assign _ _ _ | ret _ | check _ => exact scalar params st s real _ (by trivial) result pure out actual
  | appendRow container ty =>
    cases container with
    | «local» slot => exact appendRoot_stmt s slot ty out actual
    | row _ _ _ => simp [DynamicStmt.run] at pure
  | append container ty value =>
    cases container with
    | «local» _ => simp [DynamicStmt.run] at pure
    | row parent element idx =>
      cases parent with
      | row _ _ _ => simp [DynamicStmt.run] at pure
      | «local» slot =>
        cases element with
        | vector _ => simp [DynamicStmt.run] at pure
        | integer element => exact child params st s real slot element ty idx value result pure out actual
  | _ => simp [DynamicStmt.run] at pure

theorem sound (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (real : Realizes params st.locals st.contents s) (stmt : NStmt) (result : DynamicStmt.Step)
    (pure : DynamicStmt.run params stmt st = some result) (available : DynamicAppendAuto.Available params st s stmt) :
    ∃ actual, stmt.run s = some actual ∧ DynamicScalarSound.Matches params result actual ∧ Change s actual.state := by
  obtain ⟨actual,ran,matched⟩ := DynamicAppendAuto.sound params st s real stmt result pure available
  exact ⟨actual,ran,matched,effects params st s real stmt result pure actual ran⟩

end Proofs.DynamicStmtEffects
