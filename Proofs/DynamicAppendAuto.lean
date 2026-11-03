import Proofs.DynamicAppendDecode

namespace Proofs.DynamicAppendAuto
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppVectorOwnership Proofs.CppVector
open Proofs.CppNestedVectorStore Proofs.CppNestedEval Proofs.MultiVecDynamic
open Proofs.DynamicContents Proofs.DynamicExpr Proofs.DynamicRealizes

-- Allocation limits are concrete; all pure lookup/value conditions are
-- recovered from success. The selected target is unique in the pure state.
def RootRoom (s : NState) (root : Nat) : Prop :=
  ∃ old, s.frame.state.storage.lookup root = some old ∧ old.items.length < old.limit

def Available (params : List Parameter) (st : DynamicStmt.State) (s : NState) : NStmt → Prop
  | .appendRow (.local slot) ty =>
      ∀ p, DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p → RootRoom s p.owner
  | .append (.row (.local slot) (.integer _) idx) ty _ =>
      ∀ p (k : Nat), DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p →
        denote params st.locals st.contents idx = some (k : Int) → DynamicAppendValue.RoomAt s p.owner k
  | _ => True

theorem root_sound (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (slot : Nat) (ty : Ty) (result : DynamicStmt.Step)
    (pure : DynamicStmt.run params (.appendRow (.local slot) ty) st = some result)
    (available : Available params st s (.appendRow (.local slot) ty)) :
    ∃ (p : Parameter) (old : Buffer Value) (r : Result Value Unit) (out : NState),
      DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p ∧
      s.frame.state.storage.lookup p.owner = some old ∧
      (NStmt.appendRow (.local slot) ty).run s = some ⟨out,none,false⟩ ∧
      DynamicScalarSound.Matches params result ⟨out,none,false⟩ ∧ out.work = s.work+r.work+3 := by
  obtain ⟨p,sc,values,mutable,lookup,resultEq⟩ := DynamicAppendDecode.root params st slot ty result pure
  obtain ⟨old,found,room⟩ := available p mutable
  obtain ⟨_,r,out,ran,matched,work⟩ := DynamicAppendSound.appendRoot params st s realizes slot ty p mutable sc values lookup old found room
  subst result
  exact ⟨p,old,r,out,mutable,found,ran,matched,work⟩

theorem child_sound (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (slot : Nat) (element ty : Ty) (idx value : NExpr)
    (result : DynamicStmt.Step)
    (pure : DynamicStmt.run params (.append (.row (.local slot) (.integer element) idx) ty value) st = some result)
    (available : Available params st s (.append (.row (.local slot) (.integer element) idx) ty value)) :
    ∃ (p : Parameter) (k : Nat) (x : Int) (old : Buffer Value) (r : Result Value Unit) (out : NState),
      DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p ∧
      denote params st.locals st.contents idx = some (k : Int) ∧ denote params st.locals st.contents value = some x ∧
      (NStmt.append (.row (.local slot) (.integer element) idx) ty value).run s = some ⟨out,none,false⟩ ∧
      DynamicScalarSound.Matches params result ⟨out,none,false⟩ ∧ DynamicAppendIndex.RowUpdate s out p.owner k x old r.buffer ∧
      out.work+CppVectorGrowth.potential r.buffer ≤ s.work+2*idx.nodes+2*value.nodes+8+CppVectorGrowth.potential old ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveS s+2*idx.nodes+2*value.nodes+4)+out.frame.state.storage.peak) := by
  obtain ⟨p,sc,k,values,row,x,mutable,elementEq,lookup,index,val,item,valid,resultEq⟩ :=
    DynamicAppendDecode.child params st slot element ty idx value result pure
  subst element
  obtain ⟨_,old,r,out,ran,matched,updated,work,peak⟩ := DynamicAppendIndex.appendChild params st s realizes slot ty p mutable
    sc k values row lookup item idx value (DynamicExprAuto.ready _ _ _ _) index x (DynamicExprAuto.ready _ _ _ _) val valid
    (available p k mutable index)
  subst result
  exact ⟨p,k,x,old,r,out,mutable,index,val,ran,matched,updated,work,peak⟩

-- Every successful primitive in the current pure interpreter is covered.
-- Unsupported syntax still cannot produce a pure success witness.
theorem sound (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (stmt : NStmt) (result : DynamicStmt.Step)
    (pure : DynamicStmt.run params stmt st = some result) (available : Available params st s stmt) :
    ∃ actual, stmt.run s = some actual ∧ DynamicScalarSound.Matches params result actual := by
  have scalarCase (statement : NStmt) (ran : DynamicStmt.run params statement st = some result)
      (form : DynamicStmtAuto.ScalarForm statement) :
      ∃ actual, statement.run s = some actual ∧ DynamicScalarSound.Matches params result actual := by
    obtain ⟨actual,ran,matched,_⟩ := DynamicStmtAuto.scalar_sound params st s realizes statement form result ran
    exact ⟨actual,ran,matched⟩
  cases stmt with
  | skip | declare _ _ _ | assign _ _ _ | ret _ | check _ =>
    exact scalarCase _ pure True.intro
  | appendRow container ty =>
    cases container with
    | «local» slot =>
      obtain ⟨_,_,_,out,_,_,ran,matched,_⟩ := root_sound params st s realizes slot ty result pure available
      exact ⟨⟨out,none,false⟩,ran,matched⟩
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
        | integer element =>
          obtain ⟨_,_,_,_,_,out,_,_,_,ran,matched,_⟩ := child_sound params st s realizes slot element ty idx value result pure available
          exact ⟨⟨out,none,false⟩,ran,matched⟩
  | _ => simp [DynamicStmt.run] at pure

theorem runs (params : List Parameter) (st : DynamicStmt.State) (s : NState)
    (realizes : Realizes params st.locals st.contents s) (stmt : NStmt) (result : DynamicStmt.Step)
    (pure : DynamicStmt.run params stmt st = some result) (available : Available params st s stmt) :
    DynamicControlBridge.Runs params (.primitive stmt) st s (fun final _ => final = DynamicControl.ofStmt result) := by
  obtain ⟨actual,ran,matched⟩ := sound params st s realizes stmt result pure available
  exact DynamicControlBridge.Runs.primitive pure ran matched rfl

end Proofs.DynamicAppendAuto
