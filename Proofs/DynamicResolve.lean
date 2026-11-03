import Proofs.DynamicResolveRoots

namespace Proofs.DynamicResolve
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedCall
open Proofs.CppNestedStmt Proofs.CppNestedEval Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic
open Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicFamilyInit

-- Keep the same concrete heap witness while expression references are added.
theorem family_extension {params : List Parameter} {h : Heap} {m : Resources} {s t : NState}
    (family : Family params h s.frame m) (ext : Ext s t) : Family params h t.frame m := by
  obtain ⟨state,flags,⟨extra,bindings⟩,_⟩ := ext
  apply family.transport t.frame state flags
  intro p hp
  rw [bindings,List.getElem?_append_left (List.getElem?_eq_some_iff.mp (family.bindings p hp)).1]
  exact family.bindings p hp

theorem one_sound (params : List Parameter) (st : DynamicStmt.State) (h : Heap) (m : Resources) (s : NState)
    (family : Family params h s.frame m) (real : Realizes params st.locals st.contents s)
    (parameter : Proofs.CppVectorBindings.Parameter) (argument : NArgument) (r : Resolved)
    (pure : DynamicArguments.resolve params st parameter argument = some r) :
    ∃ t, CppNestedCall.resolve s parameter argument = some (t,r) ∧
      GoodF s t (DynamicArguments.work parameter argument) (DynamicArguments.work parameter argument) ∧
      Ext s t ∧ Compatible h r := by
  cases parameter with
  | scalar ty reference wr =>
    cases reference with
    | false =>
      cases argument with
      | value e =>
        by_cases typed : e.resultType = ty
        · cases value : denote params st.locals st.contents e with
          | none => simp [DynamicArguments.resolve,typed,value] at pure
          | some v =>
            simp only [DynamicArguments.resolve,typed,ite_true,value,Option.map_some,Option.some.injEq] at pure
            subst r
            obtain ⟨_,t,extra,ev⟩ := DynamicExprAuto.sound params st.locals st.contents e v value s real
            exact ⟨t,by simp [CppNestedCall.resolve,typed,ev.1],ev.2.1,Ext.of_goodF ev.2.1 ev.2.2,True.intro⟩
        · simp [DynamicArguments.resolve,typed] at pure
      | _ => simp [DynamicArguments.resolve] at pure
    | true =>
      cases argument with
      | scalarReference slot =>
        cases cell : DynamicStmt.scalarCell st.locals slot ty with
        | none => simp [DynamicArguments.resolve,cell] at pure
        | some pair =>
          obtain ⟨binding,value⟩ := pair
          simp only [DynamicArguments.resolve,cell,Bind.bind,Option.bind] at pure
          split at pure
          · rename_i permission
            have actual : s.scalarCell slot ty = some (binding,value) := by
              rw [← DynamicScalarSteps.snapshot_cell,real.locals]; exact cell
            have same := Option.some.inj pure
            subst r
            exact ⟨s.charge 1 1,by simp [CppNestedCall.resolve,actual]; exact permission,GoodF.charge s 1 1,Ext.charge s 1 1,True.intro⟩
          · contradiction
      | _ => simp [DynamicArguments.resolve] at pure
  | vector ty wr =>
    cases argument with
    | vectorReference slot =>
      cases chosen : DynamicArguments.root params st slot (.integer ty) wr with
      | none => simp [DynamicArguments.resolve,chosen] at pure
      | some p =>
        simp only [DynamicArguments.resolve,chosen,Option.map_some,Option.some.injEq] at pure
        subst r
        obtain ⟨loc,selected,typed,permission⟩ := DynamicArguments.root_found params st slot (.integer ty) wr p chosen
        have member := List.mem_of_find?_eq_some selected
        have hslot := DynamicSizeSound.vector_slot params st.locals st.contents s real slot p.slot loc
        obtain ⟨buffer,resolved⟩ := DynamicResolveRoots.resolve_root family p member _ typed
        obtain ⟨view,lookup,element,scope⟩ := family.views p member
        refine ⟨s.charge 1 1,?_,GoodF.charge s 1 1,Ext.charge s 1 1,view,lookup,element.trans typed,scope⟩
        simp [CppNestedCall.resolve,hslot,family.bindings p member,resolved,Parameter.binding,typed]
        exact permission
    | _ => simp [DynamicArguments.resolve] at pure
  | nested ty wr =>
    cases argument with
    | vectorReference slot =>
      cases chosen : DynamicArguments.root params st slot (.vector (.integer ty)) wr with
      | none => simp [DynamicArguments.resolve,chosen] at pure
      | some p =>
        simp only [DynamicArguments.resolve,chosen,Option.map_some,Option.some.injEq] at pure
        subst r
        obtain ⟨loc,selected,typed,permission⟩ := DynamicArguments.root_found params st slot (.vector (.integer ty)) wr p chosen
        have member := List.mem_of_find?_eq_some selected
        have hslot := DynamicSizeSound.vector_slot params st.locals st.contents s real slot p.slot loc
        obtain ⟨buffer,resolved⟩ := DynamicResolveRoots.resolve_root family p member _ typed
        obtain ⟨view,lookup,element,scope⟩ := family.views p member
        refine ⟨s.charge 1 1,?_,GoodF.charge s 1 1,Ext.charge s 1 1,view,lookup,element.trans typed,scope⟩
        simp [CppNestedCall.resolve,hslot,family.bindings p member,resolved,Parameter.binding,typed]
        exact permission
    | _ => simp [DynamicArguments.resolve] at pure

theorem all_sound (params : List Parameter) (st : DynamicStmt.State) (h : Heap) (m : Resources) (s : NState)
    (family : Family params h s.frame m) (real : Realizes params st.locals st.contents s)
    (parameters : List Proofs.CppVectorBindings.Parameter) (arguments : List NArgument) (rs : List Resolved)
    (pure : DynamicArguments.resolveAll params st parameters arguments = some rs) :
    ∃ t, CppNestedCall.resolveAll s parameters arguments = some (t,rs) ∧
      GoodF s t (DynamicArguments.totalWork parameters arguments) (DynamicArguments.totalWork parameters arguments) ∧
      Ext s t ∧ Family params h t.frame m ∧ (∀ r ∈ rs, Compatible h r) ∧
      Realizes params st.locals st.contents t := by
  induction parameters generalizing s arguments rs with
  | nil =>
    cases arguments with
    | nil =>
      simp only [DynamicArguments.resolveAll,Option.some.injEq] at pure
      subst rs
      have identity : GoodF s s 0 0 := by
        simp [GoodF]
        exact ⟨Nat.le_max_left _ _,Nat.le_max_left _ _⟩
      have extension : Ext s s := ⟨rfl,rfl,⟨[],by simp⟩,rfl,rfl,rfl,rfl,rfl⟩
      exact ⟨s,rfl,identity,extension,family,by simp,real⟩
    | cons _ _ => simp [DynamicArguments.resolveAll] at pure
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp [DynamicArguments.resolveAll] at pure
    | cons argument arguments =>
      cases first : DynamicArguments.resolve params st parameter argument with
      | none => simp [DynamicArguments.resolveAll,first] at pure
      | some r =>
        cases rest : DynamicArguments.resolveAll params st parameters arguments with
        | none => simp [DynamicArguments.resolveAll,first,rest] at pure
        | some tail =>
          simp only [DynamicArguments.resolveAll,first,rest,Bind.bind,Option.bind,Option.some.injEq] at pure
          subst rs
          obtain ⟨next,ran,good,ext,compatible⟩ := one_sound params st h m s family real parameter argument r first
          have nextFamily := family_extension family ext
          have nextReal := DynamicExprCompose.in_extension params st.locals st.contents s next real ext
          obtain ⟨last,ranTail,goodTail,extTail,lastFamily,compatibleTail,lastReal⟩ := ih next nextFamily nextReal arguments tail rest
          refine ⟨last,by simp [CppNestedCall.resolveAll,ran,ranTail],?_,ext.trans extTail,lastFamily,?_,lastReal⟩
          · exact (good.trans goodTail).mono (by simp [DynamicArguments.totalWork]) (by simp only [DynamicArguments.totalWork]; omega)
          · intro q member
            rcases List.mem_cons.mp member with same | member
            · subst q; exact compatible
            · exact compatibleTail q member

end Proofs.DynamicResolve
