import Proofs.MatMulPrepare
import Proofs.Generated.IsPrime

namespace Proofs.IsPrimePrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

theorem prepare_mul (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (e1 e2 e3 : NExpr) (v1 v2 v3 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = u64)
    (ty2 : e2.resultType = u64)
    (ty3 : e3.resultType = u64)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (n1 : u64.valid v1 = true)
    (n2 : u64.valid v2 = true)
    (n3 : u64.valid v3 = true) :
    ∃ t1 t2 t3, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.IsPrimeInstance.mul_mod_u64.parameters
          [.value e1, .value e2, .value e3] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨u64,v1⟩,⟨u64,v2⟩,⟨u64,v3⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          []⟩ ∧
        Sinit.scalars.work = t3.scalars.work+4 ∧ t3.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreV : Core caller caller := (core_charge caller 1 1)
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  refine ⟨t1,t2,t3,g1,g2,g3,?_⟩
  have res1 : resolve caller (.scalar u64 false true) (.value e1) = some (t1,.scalar u64 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar u64 false true) (.value e2) = some (t2,.scalar u64 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar u64 false true) (.value e3) = some (t3,.scalar u64 true v3) := by
    simp [resolve,ty3,ran3]
  have frameT : t3.frame = caller.frame := g3.1.1.trans (g2.1.1.trans (g1.1.1))
  have fs : t3.frame.state = caller.frame.state := by rw [frameT]
  have fr : t3.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t3.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t3.scalars.memory = caller.scalars.memory := g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1))
  have hbind : t3.scalars.bindings = caller.scalars.bindings := g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1))
  have hbase : t3.scalars.baseMemory = caller.scalars.baseMemory := g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2))
  have hp : Proofs.IsPrimeInstance.mul_mod_u64.parameters =
      [.scalar u64 false true,.scalar u64 false true,.scalar u64 false true] := rfl
  rw [hp]
  simp [prepare, valid, resolveAll, res1, res2, res3]
  simp [fs, fr, fb, hmem, hbind, hbase, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  omega

theorem prepare_pow (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (e1 e2 e3 : NExpr) (v1 v2 v3 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = u64)
    (ty2 : e2.resultType = u64)
    (ty3 : e3.resultType = u64)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (n1 : u64.valid v1 = true)
    (n2 : u64.valid v2 = true)
    (n3 : u64.valid v3 = true) :
    ∃ t1 t2 t3, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.IsPrimeInstance.pow_mod_u64.parameters
          [.value e1, .value e2, .value e3] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨u64,v1⟩,⟨u64,v2⟩,⟨u64,v3⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          []⟩ ∧
        Sinit.scalars.work = t3.scalars.work+4 ∧ t3.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreV : Core caller caller := (core_charge caller 1 1)
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  refine ⟨t1,t2,t3,g1,g2,g3,?_⟩
  have res1 : resolve caller (.scalar u64 false true) (.value e1) = some (t1,.scalar u64 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar u64 false true) (.value e2) = some (t2,.scalar u64 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar u64 false true) (.value e3) = some (t3,.scalar u64 true v3) := by
    simp [resolve,ty3,ran3]
  have frameT : t3.frame = caller.frame := g3.1.1.trans (g2.1.1.trans (g1.1.1))
  have fs : t3.frame.state = caller.frame.state := by rw [frameT]
  have fr : t3.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t3.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t3.scalars.memory = caller.scalars.memory := g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1))
  have hbind : t3.scalars.bindings = caller.scalars.bindings := g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1))
  have hbase : t3.scalars.baseMemory = caller.scalars.baseMemory := g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2))
  have hp : Proofs.IsPrimeInstance.pow_mod_u64.parameters =
      [.scalar u64 false true,.scalar u64 false true,.scalar u64 false true] := rfl
  rw [hp]
  simp [prepare, valid, resolveAll, res1, res2, res3]
  simp [fs, fr, fb, hmem, hbind, hbase, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  omega

theorem prepare_base (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (e1 : NExpr) (v1 : Int) (hs1 : e1.scalarOnly = true)
    (ty1 : e1.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1)
    (n1 : i32.valid v1 = true) :
    ∃ t1, Good caller t1 e1.nodes e1.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.IsPrimeInstance.mr_base.parameters
          [.value e1] = some Sinit ∧
        Sinit.slots = [.scalar 0] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          []⟩ ∧
        Sinit.scalars.work = t1.scalars.work+2 ∧ t1.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreV : Core caller caller := (core_charge caller 1 1)
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 hs1 (by rw [envOf_core coreV]; exact d1)
  refine ⟨t1,g1,?_⟩
  have res1 : resolve caller (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have frameT : t1.frame = caller.frame := g1.1.1
  have fs : t1.frame.state = caller.frame.state := by rw [frameT]
  have fr : t1.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t1.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t1.scalars.memory = caller.scalars.memory := g1.1.2.2.2.1
  have hbind : t1.scalars.bindings = caller.scalars.bindings := g1.1.2.2.2.2.1
  have hbase : t1.scalars.baseMemory = caller.scalars.baseMemory := g1.1.2.2.2.2.2
  have hp : Proofs.IsPrimeInstance.mr_base.parameters =
      [.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare, valid, resolveAll, res1]
  simp [fs, fr, fb, hmem, hbind, hbase, bindAll, bindOne, CppState.bindArgument, n1, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  omega

theorem prepare_wit (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (e1 e2 e3 e4 : NExpr) (v1 v2 v3 v4 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = u64)
    (ty2 : e2.resultType = u64)
    (ty3 : e3.resultType = i32)
    (ty4 : e4.resultType = u64)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (d4 : e4.denote (envOf caller) = some v4)
    (n1 : u64.valid v1 = true)
    (n2 : u64.valid v2 = true)
    (n3 : i32.valid v3 = true)
    (n4 : u64.valid v4 = true) :
    ∃ t1 t2 t3 t4, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ Good t3 t4 e4.nodes e4.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.IsPrimeInstance.mr_witness.parameters
          [.value e1, .value e2, .value e3, .value e4] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨u64,v1⟩,⟨u64,v2⟩,⟨i32,v3⟩,⟨u64,v4⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          []⟩ ∧
        Sinit.scalars.work = t4.scalars.work+5 ∧ t4.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreV : Core caller caller := (core_charge caller 1 1)
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  obtain ⟨t4,ran4,g4⟩ := scalar_eval e4 t3 v4 hs4 (by rw [envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d4)
  refine ⟨t1,t2,t3,t4,g1,g2,g3,g4,?_⟩
  have res1 : resolve caller (.scalar u64 false true) (.value e1) = some (t1,.scalar u64 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar u64 false true) (.value e2) = some (t2,.scalar u64 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,ty3,ran3]
  have res4 : resolve t3 (.scalar u64 false true) (.value e4) = some (t4,.scalar u64 true v4) := by
    simp [resolve,ty4,ran4]
  have frameT : t4.frame = caller.frame := g4.1.1.trans (g3.1.1.trans (g2.1.1.trans (g1.1.1)))
  have fs : t4.frame.state = caller.frame.state := by rw [frameT]
  have fr : t4.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t4.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t4.scalars.memory = caller.scalars.memory := g4.1.2.2.2.1.trans (g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1)))
  have hbind : t4.scalars.bindings = caller.scalars.bindings := g4.1.2.2.2.2.1.trans (g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1)))
  have hbase : t4.scalars.baseMemory = caller.scalars.baseMemory := g4.1.2.2.2.2.2.trans (g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2)))
  have hp : Proofs.IsPrimeInstance.mr_witness.parameters =
      [.scalar u64 false true,.scalar u64 false true,.scalar i32 false true,.scalar u64 false true] := rfl
  rw [hp]
  simp [prepare, valid, resolveAll, res1, res2, res3, res4]
  simp [fs, fr, fb, hmem, hbind, hbase, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, n4, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  have a4 := g4.2.2.2.2.1
  omega

theorem prepare_isp (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (e1 : NExpr) (v1 : Int) (hs1 : e1.scalarOnly = true)
    (ty1 : e1.resultType = u64)
    (d1 : e1.denote (envOf caller) = some v1)
    (n1 : u64.valid v1 = true) :
    ∃ t1, Good caller t1 e1.nodes e1.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.IsPrimeInstance.is_prime.parameters
          [.value e1] = some Sinit ∧
        Sinit.slots = [.scalar 0] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨u64,v1⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          []⟩ ∧
        Sinit.scalars.work = t1.scalars.work+2 ∧ t1.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have coreV : Core caller caller := (core_charge caller 1 1)
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 hs1 (by rw [envOf_core coreV]; exact d1)
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
  have hp : Proofs.IsPrimeInstance.is_prime.parameters =
      [.scalar u64 false true] := rfl
  rw [hp]
  simp [prepare, valid, resolveAll, res1]
  simp [fs, fr, fb, hmem, hbind, hbase, bindAll, bindOne, CppState.bindArgument, n1, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  omega


end Proofs.IsPrimePrepare
