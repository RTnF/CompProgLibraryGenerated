import Proofs.GroupCall

namespace Proofs.CppScalarValuePrepare
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





theorem prepare_values2 (ty tn : Ty) (caller : NState) (params : List Proofs.CppVectorBindings.Parameter)
    (hp : params = [.scalar ty false true, .scalar tn false true]) (e1 e2 : NExpr) (v1 v2 : Int)
    (h1 : e1.scalarOnly = true) (h2 : e2.scalarOnly = true) (t1ty : e1.resultType = ty) (t2ty : e2.resultType = tn)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (valid : caller.frame.state.wellFormed = true) (n1 : ty.valid v1 = true) (n2 : tn.valid v2 = true) :
    ∃ t1 t2, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller params [.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨ty,v1⟩,⟨tn,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+3 ∧ t2.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 h1 d1
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have frameT : t2.frame = caller.frame := by rw [g2.1.1,g1.1.1]
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have a := g2.1.2.2.2.1; have b := g1.1.2.2.2.1; rw [a,b]
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have a := g2.1.2.2.2.2.1; have b := g1.1.2.2.2.2.1; rw [a,b]
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have a := g2.1.2.2.2.2.2; have b := g1.1.2.2.2.2.2; rw [a,b]
  have res1 : resolve caller (.scalar ty false true) (.value e1) = some (t1,.scalar ty true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar tn false true) (.value e2) = some (t2,.scalar tn true v2) := by
    simp [resolve,t2ty,ran2]
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,n1,n2,callerP,
    NState.observe,CppState.State.observe]
  omega

theorem prepare_literals4 (t1 t2 t3 t4 : Ty) (caller : NState)
    (params : List CppVectorBindings.Parameter)
    (hp : params = [.scalar t1 false true,.scalar t2 false true,.scalar t3 false true,.scalar t4 false true])
    (v1 v2 v3 v4 : Int) (h1 : t1.valid v1 = true) (h2 : t2.valid v2 = true)
    (h3 : t3.valid v3 = true) (h4 : t4.valid v4 = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ initial, prepare caller params [.value (.literal t1 v1),.value (.literal t2 v2),
        .value (.literal t3 v3),.value (.literal t4 v4)] = some initial ∧
      initial.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧
      initial.scalars.memory = callerP caller ++ [⟨t1,v1⟩,⟨t2,v2⟩,⟨t3,v3⟩,⟨t4,v4⟩] ∧
      initial.scalars.bindings = (List.range 4).map (fun i => ⟨(callerP caller).length+i,true⟩) ∧
      initial.scalars.baseMemory = caller.scalars.baseMemory ∧ initial.scope = caller.scope+1 ∧
      initial.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      initial.scalars.work = caller.scalars.work+9 ∧ caller.scalars.peak ≤ initial.scalars.peak := by
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,NExpr.resultType,NExpr.eval,h1,h2,h3,h4]
  simp [bindAll,bindOne,CppState.bindArgument,h1,h2,h3,h4,callerP,NState.observe,CppState.State.observe,
    List.range_succ,Nat.add_assoc]
  simp only [charge_scalar_peak,charge_work]
  refine ⟨trivial,?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _

end Proofs.CppScalarValuePrepare
