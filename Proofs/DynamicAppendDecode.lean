import Proofs.DynamicStmtAuto
import Proofs.DynamicAppendIndex

namespace Proofs.DynamicAppendDecode
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppVectorOwnership
open Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicExpr

theorem contents_root (h : ContentsHeap) (root : Nat) (ty : Ty) (next : ContentsHeap)
    (run : DynamicContents.appendRoot h root ty = some next) :
    ∃ sc values, h root = some (.rows ty sc values) ∧ next = putContents h root (.rows ty sc (values ++ [[]])) := by
  cases found : h root with
  | none => simp [DynamicContents.appendRoot,found] at run
  | some view =>
    cases view with
    | flat t sc values => simp [DynamicContents.appendRoot,found] at run
    | rows t sc values =>
      simp only [DynamicContents.appendRoot,found,Bind.bind,Option.bind] at run
      split at run
      · rename_i equal
        subst t
        exact ⟨sc,values,rfl,(Option.some.inj run).symm⟩
      · contradiction

theorem contents_child (h : ContentsHeap) (root : Nat) (ty : Ty) (k : Nat) (x : Int) (next : ContentsHeap)
    (run : DynamicContents.appendChild h root ty k x = some next) :
    ∃ sc values row, h root = some (.rows ty sc values) ∧ values[k]? = some row ∧ ty.valid x = true ∧
      next = putContents h root (.rows ty sc (values.set k (row ++ [x]))) := by
  cases found : h root with
  | none => simp [DynamicContents.appendChild,found] at run
  | some view =>
    cases view with
    | flat t sc values => simp [DynamicContents.appendChild,found] at run
    | rows t sc values =>
      cases item : values[k]? with
      | none => simp [DynamicContents.appendChild,found,item] at run
      | some row =>
        simp only [DynamicContents.appendChild,found,item,Bind.bind,Option.bind] at run
        split at run
        · rename_i good
          obtain ⟨rfl,valid⟩ := good
          exact ⟨sc,values,row,rfl,item,valid,(Option.some.inj run).symm⟩
        · contradiction

theorem root (params : List Parameter) (st : DynamicStmt.State) (slot : Nat) (ty : Ty) (result : DynamicStmt.Step)
    (run : DynamicStmt.run params (.appendRow (.local slot) ty) st = some result) :
    ∃ p sc values, DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p ∧
      st.contents p.owner = some (.rows ty sc values) ∧
      result = ⟨⟨st.locals,putContents st.contents p.owner (.rows ty sc (values ++ [[]]))⟩,none⟩ := by
  cases chosen : DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) with
  | none => simp [DynamicStmt.run,chosen] at run
  | some p =>
    cases appended : DynamicContents.appendRoot st.contents p.owner ty with
    | none => simp [DynamicStmt.run,chosen,appended] at run
    | some heap =>
      obtain ⟨sc,values,lookup,same⟩ := contents_root st.contents p.owner ty heap appended
      simp only [DynamicStmt.run,chosen,appended,Bind.bind,Option.bind,Option.some.injEq] at run
      exact ⟨p,sc,values,rfl,lookup,by rw [← run,same]⟩

theorem child (params : List Parameter) (st : DynamicStmt.State) (slot : Nat) (element ty : Ty)
    (idx value : NExpr) (result : DynamicStmt.Step)
    (run : DynamicStmt.run params (.append (.row (.local slot) (.integer element) idx) ty value) st = some result) :
    ∃ (p : Parameter) (sc k : Nat) (values : List (List Int)) (row : List Int) (x : Int),
      DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) = some p ∧ element = ty ∧
      st.contents p.owner = some (.rows ty sc values) ∧ denote params st.locals st.contents idx = some (k : Int) ∧
      denote params st.locals st.contents value = some x ∧ values[k]? = some row ∧ ty.valid x = true ∧
      result = ⟨⟨st.locals,putContents st.contents p.owner (.rows ty sc (values.set k (row ++ [x])))⟩,none⟩ := by
  cases chosen : DynamicStmt.mutableRoot params st slot (.vector (.integer ty)) with
  | none => simp [DynamicStmt.run,chosen] at run
  | some p =>
    cases index : denote params st.locals st.contents idx with
    | none => simp [DynamicStmt.run,chosen,index] at run
    | some i =>
      cases val : denote params st.locals st.contents value with
      | none => simp [DynamicStmt.run,chosen,index,val] at run
      | some x =>
        simp only [DynamicStmt.run,chosen,index,val,Bind.bind,Option.bind] at run
        split at run
        · rename_i good
          cases appended : DynamicContents.appendChild st.contents p.owner ty i.toNat x with
          | none => simp [appended] at run
          | some heap =>
            obtain ⟨sc,values,row,lookup,item,valid,same⟩ := contents_child st.contents p.owner ty i.toNat x heap appended
            simp only [appended,Option.bind_some,Option.some.injEq] at run
            have natural : (i.toNat : Int) = i := by omega
            refine ⟨p,sc,i.toNat,values,row,x,rfl,good.1,lookup,?_,rfl,item,valid,?_⟩
            · simp only [natural]
            · rw [← run,same]
        · contradiction

end Proofs.DynamicAppendDecode
