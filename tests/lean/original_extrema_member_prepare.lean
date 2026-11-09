namespace ExtremaPrepareGeneral
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


open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

theorem prepare_reference_value1 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t0 tx : Ty) (hp : params = [.scalar t0 true true,.scalar tx false true])
    (s0 : Nat) (b0 : CppState.Binding) (v0 x : Int)
    (c0 : caller.scalarCell s0 t0 = some (b0,⟨t0,v0⟩)) (w0 : b0.writable = true)
    (hx : tx.valid x = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ initial, prepare caller params [.scalarReference s0,.value (.literal tx x)] = some initial ∧
      initial.slots = (List.range 2).map (fun i => .scalar i) ∧
      initial.scalars.memory = callerP caller ++ [⟨tx,x⟩] ∧
      initial.scalars.bindings = [⟨b0.address,true⟩,⟨(callerP caller).length,true⟩] ∧
      initial.scalars.baseMemory = caller.scalars.baseMemory ∧ initial.scope = caller.scope+1 ∧
      initial.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      initial.scalars.work = caller.scalars.work+5 ∧ caller.scalars.peak ≤ initial.scalars.peak := by
  obtain ⟨_,_,_,m0,_,v0ok⟩ := scalarCell_facts c0
  have l0 : b0.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m0).1
  have h0 : (callerP caller)[b0.address]? = some ⟨t0,v0⟩ := by
    rw [callerP,List.getElem?_append_left l0]; exact m0
  simp only [callerP] at h0
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,c0,w0,NExpr.resultType,NExpr.eval,hx]
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,
    h0,v0ok,hx,List.range_succ,Nat.add_assoc]
  simp only [charge_scalar_peak,charge_work]
  refine ⟨trivial,?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _

theorem prepare_references2_value1 (caller : NState) (params : List CppVectorBindings.Parameter)
    (t0 t1 tx : Ty) (hp : params = [.scalar t0 true true,.scalar t1 true true,.scalar tx false true])
    (s0 s1 : Nat) (b0 b1 : CppState.Binding) (v0 v1 x : Int)
    (c0 : caller.scalarCell s0 t0 = some (b0,⟨t0,v0⟩)) (w0 : b0.writable = true)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩)) (w1 : b1.writable = true)
    (hx : tx.valid x = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ initial, prepare caller params [.scalarReference s0,.scalarReference s1,.value (.literal tx x)] = some initial ∧
      initial.slots = (List.range 3).map (fun i => .scalar i) ∧
      initial.scalars.memory = callerP caller ++ [⟨tx,x⟩] ∧
      initial.scalars.bindings = [⟨b0.address,true⟩,⟨b1.address,true⟩,⟨(callerP caller).length,true⟩] ∧
      initial.scalars.baseMemory = caller.scalars.baseMemory ∧ initial.scope = caller.scope+1 ∧
      initial.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      initial.scalars.work = caller.scalars.work+7 ∧ caller.scalars.peak ≤ initial.scalars.peak := by
  obtain ⟨_,_,_,m0,_,v0ok⟩ := scalarCell_facts c0
  have l0 : b0.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m0).1
  have h0 : (callerP caller)[b0.address]? = some ⟨t0,v0⟩ := by
    rw [callerP,List.getElem?_append_left l0]; exact m0
  obtain ⟨_,_,_,m1,_,v1ok⟩ := scalarCell_facts c1
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have h1 : (callerP caller)[b1.address]? = some ⟨t1,v1⟩ := by
    rw [callerP,List.getElem?_append_left l1]; exact m1
  have c1' : (caller.charge 1 1).scalarCell s1 t1 = some (b1,⟨t1,v1⟩) := c1
  simp only [callerP] at h0 h1
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,c0,c1',w0,w1,NExpr.resultType,NExpr.eval,hx]
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,
    h0,h1,v0ok,v1ok,hx,List.range_succ,Nat.add_assoc]
  simp only [charge_scalar_peak,charge_work]
  refine ⟨trivial,?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _

end ExtremaPrepareGeneral
