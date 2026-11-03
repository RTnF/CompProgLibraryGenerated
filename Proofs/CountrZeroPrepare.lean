import Proofs.MatMulPrepare
import Proofs.Generated.CountrZero

namespace Proofs.CountrZeroPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

theorem prepare_ta (caller : NState) (e1 : NExpr) (v1 : Int) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = u64)
    (d1 : e1.denote (envOf caller) = some v1) (valid : caller.frame.state.wellFormed = true)
    (n1 : u64.valid v1 = true) :
    ∃ t1, Good caller t1 e1.nodes e1.nodes ∧
      ∃ Sinit, prepare caller Proofs.CountrZeroInstance.countr_zero_u64.parameters [.value e1] = some Sinit ∧
        Sinit.slots = [.scalar 0] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨u64,v1⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t1.scalars.work+2 ∧ t1.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 hs1 d1
  refine ⟨t1,g1,?_⟩
  have res1 : resolve caller (.scalar u64 false true) (.value e1) = some (t1,.scalar u64 true v1) := by
    simp [resolve,ty1,ran1]
  have frameT : t1.frame = caller.frame := g1.1.1
  have fs : t1.frame.state = caller.frame.state := by rw [frameT]
  have fr : t1.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t1.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t1.scalars.memory = caller.scalars.memory := g1.1.2.2.2.1
  have hbind : t1.scalars.bindings = caller.scalars.bindings := g1.1.2.2.2.2.1
  have hbase : t1.scalars.baseMemory = caller.scalars.baseMemory := g1.1.2.2.2.2.2
  have hp : Proofs.CountrZeroInstance.countr_zero_u64.parameters = [.scalar u64 false true] := rfl
  rw [hp]
  simp [prepare, valid, resolveAll, res1]
  simp [fs, fr, fb, hmem, hbind, hbase, bindAll, bindOne, CppState.bindArgument, n1, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  omega

end Proofs.CountrZeroPrepare
