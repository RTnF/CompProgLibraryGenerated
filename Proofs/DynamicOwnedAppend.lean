import Proofs.DynamicFlatAppend

namespace Proofs.DynamicOwnedAppend
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.DynamicOwnedState
open Proofs.CppVector
open Proofs.CppNestedVectorStore (Value)

-- Keep capacities outside the logical heap. The Available premise below
-- records the actual max-size check rather than assuming unlimited growth.
def run (stmt : NStmt) (st : State) : Option State := match stmt with
  | .appendRow (.local _) _ => do
      let result ← DynamicStmt.run st.params stmt st.core
      some {st with core := result.state,nextOwner := st.nextOwner+1}
  | .append (.local slot) ty value => DynamicFlatAppend.run slot ty value st
  | .append (.row (.local _) (.integer _) _) _ _ => do
      let result ← DynamicStmt.run st.params stmt st.core
      some {st with core := result.state}
  | _ => none

def Available (st : State) (s : NState) (stmt : NStmt) : Prop := match stmt with
  | .append (.local slot) ty _ => DynamicFlatAppend.Available st s slot ty
  | other => DynamicAppendAuto.Available st.params st.core s other

theorem root_sound (st : State) (s : NState) (real : Realizes st s) (slot : Nat) (ty : Ty)
    (result : DynamicStmt.Step)
    (pureRun : DynamicStmt.run st.params (.appendRow (.local slot) ty) st.core = some result)
    (available : DynamicAppendAuto.Available st.params st.core s (.appendRow (.local slot) ty)) :
    ∃ (r : Result Value Unit) (out : NState), (NStmt.appendRow (.local slot) ty).run s = some ⟨out,none,false⟩ ∧
      Realizes {st with core := result.state,nextOwner := st.nextOwner+1} out ∧
      out.work = s.work+r.work+3 := by
  obtain ⟨_,_,r,out,_,_,ran,matched,work⟩ := DynamicAppendAuto.root_sound st.params st.core s real.data slot ty result pureRun available
  obtain ⟨count,bindings,scope⟩ := DynamicOwnedAppendLayout.root s ⟨out,none,false⟩ slot ty ran
  exact ⟨r,out,ran,⟨matched.state,by rw [count,real.owner],by rw [bindings]; exact real.binding,scope.trans real.scopedState⟩,work⟩

theorem child_sound (st : State) (s : NState) (real : Realizes st s) (slot : Nat) (element ty : Ty)
    (idx value : NExpr) (result : DynamicStmt.Step)
    (pureRun : DynamicStmt.run st.params (.append (.row (.local slot) (.integer element) idx) ty value) st.core = some result)
    (available : DynamicAppendAuto.Available st.params st.core s (.append (.row (.local slot) (.integer element) idx) ty value)) :
    ∃ (p : Proofs.MultiVecDynamic.Parameter) (k : Nat) (x : Int) (old : Buffer Value) (r : Result Value Unit) (out : NState),
      DynamicStmt.mutableRoot st.params st.core slot (.vector (.integer ty)) = some p ∧
      Proofs.DynamicExpr.denote st.params st.core.locals st.core.contents idx = some (k : Int) ∧
      Proofs.DynamicExpr.denote st.params st.core.locals st.core.contents value = some x ∧
      (NStmt.append (.row (.local slot) (.integer element) idx) ty value).run s = some ⟨out,none,false⟩ ∧
      Realizes {st with core := result.state} out ∧
      DynamicAppendIndex.RowUpdate s out p.owner k x old r.buffer ∧
      out.work+CppVectorGrowth.potential r.buffer ≤ s.work+2*idx.nodes+2*value.nodes+8+CppVectorGrowth.potential old ∧
      out.peak ≤ max s.peak (max s.scalars.peak (Proofs.CppNestedEval.liveS s+2*idx.nodes+2*value.nodes+4)+out.frame.state.storage.peak) := by
  obtain ⟨p,k,x,old,r,out,mutable,index,valuePure,ran,matched,updated,work,peak⟩ :=
    DynamicAppendAuto.child_sound st.params st.core s real.data slot element ty idx value result pureRun available
  obtain ⟨count,bindings,scope⟩ := DynamicOwnedAppendLayout.child st s real slot element ty idx value result pureRun ⟨out,none,false⟩ ran
  exact ⟨p,k,x,old,r,out,mutable,index,valuePure,ran,
    ⟨matched.state,by rw [count]; exact real.owner,by rw [bindings]; exact real.binding,scope.trans real.scopedState⟩,
    updated,work,peak⟩

theorem sound (st : State) (s : NState) (real : Realizes st s) (stmt : NStmt) (final : State)
    (pureRun : run stmt st = some final) (available : Available st s stmt) :
    ∃ out, stmt.run s = some ⟨out,none,false⟩ ∧ Realizes final out := by
  cases stmt with
  | appendRow container ty =>
    cases container with
    | «local» slot =>
      obtain ⟨result,ran,same⟩ := DynamicResultValid.bind_some _ _ _ pureRun
      have eq := Option.some.inj same
      subst final
      obtain ⟨r,out,actual,after,_⟩ := root_sound st s real slot ty result ran available
      exact ⟨out,actual,after⟩
    | row _ _ _ => simp [run] at pureRun
  | append container ty value =>
    cases container with
    | «local» slot => exact DynamicFlatAppend.sound st s real slot ty value final pureRun available
    | row parent element idx =>
      cases parent with
      | row _ _ _ => simp [run] at pureRun
      | «local» slot =>
        cases element with
        | vector _ => simp [run] at pureRun
        | integer element =>
          obtain ⟨result,ran,same⟩ := DynamicResultValid.bind_some _ _ _ pureRun
          have eq := Option.some.inj same
          subst final
          obtain ⟨p,k,x,old,r,out,_,_,_,actual,after,_⟩ := child_sound st s real slot element ty idx value result ran available
          exact ⟨out,actual,after⟩
  | _ => simp [run] at pureRun

end Proofs.DynamicOwnedAppend
