import Proofs.DynamicOwnedScalar
import Proofs.DynamicStmtEffects

namespace Proofs.DynamicOwnedAppendLayout
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedStmt Proofs.CppNestedSim Proofs.DynamicExpr Proofs.DynamicOwnedState
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic

-- Adding a row consumes one fresh object ID; the existing reference table is
-- unchanged. Appending an integer replaces a buffer without consuming an ID.
theorem root_frame (f next : Frame) (slot : Nat) (ty : Ty)
    (ran : f.appendRow slot ty = some next) :
    next.state.storage.objects.length = f.state.storage.objects.length+1 ∧ next.bindings = f.bindings := by
  unfold Frame.appendRow at ran
  obtain ⟨pair,_,rest⟩ := DynamicResultValid.bind_some _ _ _ ran
  obtain ⟨binding,buffer⟩ := pair
  dsimp only at rest
  split at rest
  · obtain ⟨state,appended,same⟩ := DynamicResultValid.bind_some _ _ _ rest
    have equal := Option.some.inj same
    subst next
    obtain ⟨old,tag,r,_,_,_,_,_,eq⟩ := Proofs.CppAppendRow.appendRow_inv f.state state binding.owner ty appended
    rw [eq]
    exact ⟨by simp [Proofs.CppAppendRow.added],rfl⟩
  · contradiction

theorem committed (f next : Frame) (owner : Nat) (element : Proofs.CppVectorOwnership.Element)
    (r : Proofs.CppVector.Result Proofs.CppNestedVectorStore.Value Unit)
    (ran : f.commit owner element r = some next) :
    next.state.storage.objects.length = f.state.storage.objects.length ∧ next.bindings = f.bindings := by
  unfold Frame.commit at ran
  split at ran
  · contradiction
  · split at ran
    · dsimp only at ran
      split at ran
      · have same := Option.some.inj ran
        subst next
        exact ⟨by simp [Frame.updated],rfl⟩
      · contradiction
    · contradiction

theorem child_frame (f next : Frame) (slot : Nat) (ty : Ty) (x : Int)
    (ran : f.append slot ty x = some next) :
    next.state.storage.objects.length = f.state.storage.objects.length ∧ next.bindings = f.bindings := by
  unfold Frame.append Frame.appendGrowing at ran
  obtain ⟨pair,_,rest⟩ := DynamicResultValid.bind_some _ _ _ ran
  obtain ⟨binding,buffer⟩ := pair
  obtain ⟨r,_,commit⟩ := DynamicResultValid.bind_some _ _ _ rest
  exact committed f next binding.owner (.integer ty) r commit

theorem root (s : NState) (out : NStep) (slot : Nat) (ty : Ty)
    (actual : (NStmt.appendRow (.local slot) ty).run s = some out) :
    out.state.frame.state.storage.objects.length = s.frame.state.storage.objects.length+1 ∧
      out.state.frame.bindings = s.frame.bindings ∧ out.state.scope = s.scope := by
  cases loc : s.vectorSlot slot with
  | none =>
    have missing : (Container.local slot).eval (s.charge 0 ((Container.local slot).nodes+2)) = none := by
      have loc' : (s.charge 0 ((Container.local slot).nodes+2)).vectorSlot slot = none := loc
      simp [Container.eval,loc']
    simp [NStmt.run,missing] at actual
  | some rb =>
    have eval := eval_local (s.charge 0 ((Container.local slot).nodes+2)) slot rb
      (by simpa [NState.vectorSlot] using loc)
    simp only [NStmt.run,eval,Bind.bind,Option.bind] at actual
    change (s.frame.appendRow rb ty).bind _ = _ at actual
    obtain ⟨frame,appended,same⟩ := DynamicResultValid.bind_some _ _ _ actual
    have equal := Option.some.inj same
    subst out
    obtain ⟨count,bindings⟩ := root_frame s.frame frame rb ty appended
    exact ⟨count,by simpa [NState.release,bindings] using bindings,rfl⟩

theorem child (st : State) (s : NState) (real : Realizes st s) (slot : Nat)
    (element ty : Ty) (idx value : NExpr) (result : DynamicStmt.Step)
    (pureRun : DynamicStmt.run st.params (.append (.row (.local slot) (.integer element) idx) ty value) st.core = some result)
    (out : NStep) (actual : (NStmt.append (.row (.local slot) (.integer element) idx) ty value).run s = some out) :
    out.state.frame.state.storage.objects.length = s.frame.state.storage.objects.length ∧
      out.state.frame.bindings = s.frame.bindings ∧ out.state.scope = s.scope := by
  obtain ⟨p,sc,k,values,row,x,mutable,elementEq,lookup,index,val,item,accepted,_⟩ := DynamicAppendDecode.child st.params st.core slot element ty idx value result pureRun
  subst element
  obtain ⟨location,selected,writable,maximum,_,_⟩ := DynamicAppendSound.mutable_found st.params st.core slot _ p mutable
  obtain ⟨heap,m,family,he⟩ := real.data.heap
  obtain ⟨ids,epoch,hv⟩ := DynamicSizeSound.rows_lift heap p.owner ty sc values (by rw [he]; exact lookup)
  have fw := family.row_frame p (List.mem_of_find?_eq_some selected) ty sc ids epoch values hv
  have bound : k < ids.length := by rw [← fw.data.length]; exact (List.getElem?_eq_some_iff.mp item).1
  obtain ⟨owner,rowLookup⟩ : ∃ owner, ids[k]? = some owner := ⟨ids[k],by simp⟩
  rw [writable,maximum] at fw
  let start := s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)
  obtain ⟨t1,idxExtra,hrow,good1,bindings1⟩ := DynamicIndexEval.eval_row start slot p.slot idx k p.owner sc epoch owner ids ty true true
    (2*idx.nodes) (2*idx.nodes)
    (fun u ext => DynamicIndexAtoms.index_ev (DynamicExprAuto.ready _ _ _ _) index s real.data u ((Ext.charge s 0 _).trans ext))
    (by simpa [NState.vectorSlot,start] using DynamicSizeSound.vector_slot st.params st.core.locals st.core.contents s real.data slot p.slot location)
    fw.binding fw.data.rows fw.lengths fw.flag (fun h => h) rowLookup
  have firstGood := (GoodF.charge s 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)).trans good1
  have real1 := DynamicExprCompose.in_extension st.params st.core.locals st.core.contents s t1 real.data (Ext.of_goodF firstGood bindings1)
  obtain ⟨_,t2,extra,ev⟩ := DynamicExprCertified.sound (DynamicExprDerive.derive (DynamicExprAuto.ready _ _ _ _) x val) t1 real1
  have good := firstGood.trans ev.2.1
  have allBindings : t2.frame.bindings = s.frame.bindings ++ (idxExtra ++ [Proofs.CppRowsGraph.binding p.owner ty epoch k owner true] ++ extra) := by
    rw [ev.2.2,bindings1]; simp [List.append_assoc,start]
  have evalRow : (Container.row (.local slot) (.integer ty) idx).eval
      (s.charge 0 ((Container.row (.local slot) (.integer ty) idx).nodes+value.nodes+2)) =
      some (t1,s.frame.bindings.length+idxExtra.length) := hrow
  simp only [NStmt.run,evalRow,ev.1,Bind.bind,Option.bind] at actual
  obtain ⟨frame,appended,same⟩ := DynamicResultValid.bind_some _ _ _ actual
  have equal := Option.some.inj same
  subst out
  obtain ⟨count,bindings⟩ := child_frame t2.frame frame _ ty x appended
  refine ⟨?_,?_,good.2.2.2.1⟩
  · change frame.state.storage.objects.length = s.frame.state.storage.objects.length
    rw [count,good.1]
  · change frame.bindings.take s.frame.bindings.length = s.frame.bindings
    rw [bindings,allBindings,List.take_left]

end Proofs.DynamicOwnedAppendLayout
