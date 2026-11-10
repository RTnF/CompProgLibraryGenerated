namespace GenericSetCallers
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall

open GenericAddSum
open CopiedScalarFieldsAudit
abbrev bl : Ty := ⟨1,false,true⟩
variable (ty : Ty)
def gSetNew1 (second : Bool) : NProgram :=
  ⟨[], .scalar (if second then bl else ty), copyBody 0 ty bl (zero64 ty) (.literal bl 1) second⟩


theorem set_default_correct (ty : Ty) (second : Bool) (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := gSetNew1 ty second
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar (if second then 1 else 0)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  let prog := gSetNew1 ty second
  refine constant_body_correct prog (if second then bl else ty) (if second then 1 else 0)
    (by cases second <;> rfl) (by cases second <;> rfl) (by show Scalar (gSetNew1 ty second).body = true; have h := Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl; cases second <;> simp [gSetNew1, copyBody, copyPicked, Scalar, NExpr.scalarOnly, h])
    (by cases second; exact Proofs.GenericLazy.valid_zero ty; rfl) caller valid lengths strict base ?_
  intro P hP
  subst hP
  obtain ⟨r,ran,ret,cost,need,ps⟩ := copy_exec (callerP caller) [] ty bl
    (zero64 ty) (.literal bl 1) 0 1 second (Proofs.GenericLazy.valid_zero ty) rfl (Proofs.GenericLazy.R0z_gen ty _) rfl
  have hn := Proofs.GenericLazy.castTo_nodes ty i32 (.literal i32 0)
  simp only [NExpr.nodes] at hn
  have body : prog.body = copyBody 0 ty bl (zero64 ty) (.literal bl 1) second := by cases second <;> rfl
  refine ⟨r,?_,ret,?_,?_,?_⟩
  · rw [body]; simpa only [ws_nil,List.length_nil] using ran
  · simp [NExpr.nodes, zero64] at cost
    omega
  · simp [NExpr.nodes, zero64] at need
    omega
  · rw [ps]
    exact take_P caller _

end GenericSetCallers
