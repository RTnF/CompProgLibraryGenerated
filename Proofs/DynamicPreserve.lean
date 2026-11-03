import Proofs.DynamicCall

namespace Proofs.DynamicPreserve
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.MultiVecDynamic Proofs.DynamicExpr
open Proofs.DynamicFinish Proofs.DynamicResultValid

-- Values can change and fresh locals can be appended; pre-existing cell
-- types remain a prefix. This is stronger than a length check alone.
def TypesPrefix (before after : Locals) : Prop :=
  ∃ extra, after.memory.map Proofs.CppState.Cell.type = before.memory.map Proofs.CppState.Cell.type ++ extra

theorem TypesPrefix.refl (l : Locals) : TypesPrefix l l := ⟨[],by simp⟩
theorem TypesPrefix.trans {a b c : Locals} (ab : TypesPrefix a b) (bc : TypesPrefix b c) : TypesPrefix a c := by
  obtain ⟨x,hx⟩ := ab
  obtain ⟨y,hy⟩ := bc
  exact ⟨x ++ y,by rw [hy,hx,List.append_assoc]⟩

theorem TypesPrefix.memory {a b : Locals} (memory : ∃ extra, b.memory = a.memory ++ extra) : TypesPrefix a b := by
  obtain ⟨extra,same⟩ := memory
  exact ⟨extra.map Proofs.CppState.Cell.type,by rw [same,List.map_append]⟩

theorem TypesPrefix.fields {a b : Locals} (types : TypesPrefix a b) :
    a.memory.length ≤ b.memory.length ∧
      (b.memory.take a.memory.length).map Proofs.CppState.Cell.type = a.memory.map Proofs.CppState.Cell.type := by
  obtain ⟨extra,same⟩ := types
  have length := congrArg List.length same
  simp only [List.length_map,List.length_append] at length
  refine ⟨by omega,?_⟩
  rw [List.map_take,same,← List.length_map (f := Proofs.CppState.Cell.type) (as := a.memory),List.take_append_length]

theorem assigned_types (l : Locals) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell) (x : Int)
    (found : l.memory[binding.address]? = some cell) : TypesPrefix l (DynamicStmt.assigned l binding cell x) := by
  refine ⟨[],?_⟩
  change (l.memory.set binding.address ⟨cell.type,x⟩).map Proofs.CppState.Cell.type = _
  rw [List.map_set,List.append_nil]
  have lookup : (l.memory.map Proofs.CppState.Cell.type)[binding.address]? = some cell.type := by simp [found]
  have bounds := (List.getElem?_eq_some_iff.mp lookup).1
  have atIndex := (List.getElem?_eq_some_iff.mp lookup).2
  rw [← atIndex,List.set_getElem_self bounds]

def Preserved (before after : DynamicStmt.State) : Prop :=
  SameShape before.contents after.contents ∧ TypesPrefix before.locals after.locals

theorem Preserved.refl (st : DynamicStmt.State) : Preserved st st := ⟨SameShape.refl _,TypesPrefix.refl _⟩
theorem Preserved.trans {a b c : DynamicStmt.State} (ab : Preserved a b) (bc : Preserved b c) : Preserved a c :=
  ⟨ab.1.trans bc.1,ab.2.trans bc.2⟩

theorem primitive (params : List Parameter) (st : DynamicStmt.State) (stmt : NStmt) (out : DynamicStmt.Step)
    (run : DynamicStmt.run params stmt st = some out) : Preserved st out.state := by
  cases stmt with
  | skip => simp only [DynamicStmt.run,Option.some.injEq] at run; subst out; exact Preserved.refl st
  | declare ty wr e =>
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ run
    obtain ⟨v,_,same⟩ := bind_some _ _ _ rest
    have equal := Option.some.inj same
    subst out
    exact ⟨SameShape.refl _,TypesPrefix.memory ⟨[⟨ty,v⟩],rfl⟩⟩
  | assign slot ty e =>
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ run
    obtain ⟨pair,found,rest⟩ := bind_some _ _ _ rest
    obtain ⟨binding,cell⟩ := pair
    cases wr : binding.writable with
    | false => simp [wr] at rest
    | true =>
      simp only [wr,ite_true] at rest
      obtain ⟨v,_,same⟩ := bind_some _ _ _ rest
      have equal := Option.some.inj same
      subst out
      exact ⟨SameShape.refl _,assigned_types st.locals binding cell v (DynamicBoundArguments.cell_facts _ _ _ _ _ found).1⟩
  | ret e =>
    obtain ⟨x,_,same⟩ := bind_some _ _ _ run
    have equal := Option.some.inj same
    subst out; exact Preserved.refl st
  | check e =>
    obtain ⟨x,_,rest⟩ := bind_some _ _ _ run
    split at rest
    · have equal := Option.some.inj rest
      subst out; exact Preserved.refl st
    · contradiction
  | appendRow container ty =>
    cases container with
    | «local» slot =>
      obtain ⟨p,sc,values,_,found,same⟩ := DynamicAppendDecode.root params st slot ty out run
      subst out
      exact ⟨same_put _ _ _ _ found rfl,TypesPrefix.refl _⟩
    | row _ _ _ => simp [DynamicStmt.run] at run
  | append container ty value =>
    cases container with
    | «local» _ => simp [DynamicStmt.run] at run
    | row parent element idx =>
      cases parent with
      | row _ _ _ => simp [DynamicStmt.run] at run
      | «local» slot =>
        cases element with
        | vector _ => simp [DynamicStmt.run] at run
        | integer element =>
          obtain ⟨p,sc,k,values,row,x,_,_,found,_,_,_,_,same⟩ := DynamicAppendDecode.child params st slot element ty idx value out run
          subst out
          exact ⟨same_put _ _ _ _ found rfl,TypesPrefix.refl _⟩
  | _ => simp [DynamicStmt.run] at run

theorem leave (outer inner final : DynamicStmt.State) (same : SameShape outer.contents inner.contents)
    (run : DynamicControl.leave outer inner = some final) : Preserved outer final := by
  obtain ⟨_,types,result⟩ := DynamicScopeAuto.leave_fields outer inner final run
  subst final
  exact ⟨same,[],by simpa using types⟩

theorem leave_exists (outer inner : DynamicStmt.State) (types : TypesPrefix outer.locals inner.locals) :
    ∃ final, DynamicControl.leave outer inner = some final := by
  obtain ⟨fits,typed⟩ := types.fields
  exact ⟨⟨⟨inner.locals.memory.take outer.locals.memory.length,outer.locals.bindings,outer.locals.slots⟩,inner.contents⟩,
    by simp [DynamicControl.leave,fits,typed]⟩

theorem finish_exists (outer inner : DynamicStmt.State) (types : TypesPrefix outer.locals inner.locals)
    (kind : Proofs.CppNestedCall.ResultKind) (returned : Option Int) (value : Ret) (accepted : resultValue kind returned = some value) :
    ∃ final, DynamicFinish.finish outer inner kind returned = some (final,value) := by
  obtain ⟨final,left⟩ := leave_exists outer inner types
  exact ⟨final,by simp [DynamicFinish.finish,left,accepted]⟩

end Proofs.DynamicPreserve
