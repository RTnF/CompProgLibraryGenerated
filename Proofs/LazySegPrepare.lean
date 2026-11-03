import Proofs.MatMulPrepare
import Proofs.Generated.LazySegmentTree

namespace Proofs.LazySegPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

set_option maxHeartbeats 16000000

theorem prepare_set (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0)
    (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (e1 e2 e3 e4 e5 : NExpr) (v1 v2 v3 v4 v5 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32)
    (ty3 : e3.resultType = i32)
    (ty4 : e4.resultType = i32)
    (ty5 : e5.resultType = s64)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (d4 : e4.denote (envOf caller) = some v4)
    (d5 : e5.denote (envOf caller) = some v5)
    (n1 : i32.valid v1 = true)
    (n2 : i32.valid v2 = true)
    (n3 : i32.valid v3 = true)
    (n4 : i32.valid v4 = true)
    (n5 : s64.valid v5 = true) :
    ∃ t1 t2 t3 t4 t5, Good ((caller.charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ Good t3 t4 e4.nodes e4.nodes ∧ Good t4 t5 e5.nodes e5.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_set.parameters
          [.vectorReference s0, .vectorReference s1, .value e1, .value e2, .value e3, .value e4, .value e5] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.scalar 0,.scalar 1,.scalar 2,.scalar 3,.scalar 4] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩,⟨i32,v3⟩,⟨i32,v4⟩,⟨s64,v5⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = t5.scalars.work+8 ∧ t5.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
    (fun h => rfl)
  have coreV : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge _ 1 1))
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  obtain ⟨t4,ran4,g4⟩ := scalar_eval e4 t3 v4 hs4 (by rw [envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d4)
  obtain ⟨t5,ran5,g5⟩ := scalar_eval e5 t4 v5 hs5 (by rw [envOf_core g4.1, envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d5)
  refine ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,?_⟩
  have res1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,ty3,ran3]
  have res4 : resolve t3 (.scalar i32 false true) (.value e4) = some (t4,.scalar i32 true v4) := by
    simp [resolve,ty4,ran4]
  have res5 : resolve t4 (.scalar s64 false true) (.value e5) = some (t5,.scalar s64 true v5) := by
    simp [resolve,ty5,ran5]
  have frameT : t5.frame = caller.frame := g5.1.1.trans (g4.1.1.trans (g3.1.1.trans (g2.1.1.trans (g1.1.1))))
  have fs : t5.frame.state = caller.frame.state := by rw [frameT]
  have fr : t5.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t5.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t5.scalars.memory = caller.scalars.memory := g5.1.2.2.2.1.trans (g4.1.2.2.2.1.trans (g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1))))
  have hbind : t5.scalars.bindings = caller.scalars.bindings := g5.1.2.2.2.2.1.trans (g4.1.2.2.2.2.1.trans (g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1))))
  have hbase : t5.scalars.baseMemory = caller.scalars.baseMemory := g5.1.2.2.2.2.2.trans (g4.1.2.2.2.2.2.trans (g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2))))
  have hp : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_set.parameters =
      [.vector s64 true,.vector s64 true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar s64 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true) (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame) (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, res1, res2, res3, res4, res5]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, n4, n5, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  have a4 := g4.2.2.2.2.1
  have a5 := g5.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

theorem prepare_get (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0)
    (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (e1 e2 e3 e4 : NExpr) (v1 v2 v3 v4 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32)
    (ty3 : e3.resultType = i32)
    (ty4 : e4.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (d4 : e4.denote (envOf caller) = some v4)
    (n1 : i32.valid v1 = true)
    (n2 : i32.valid v2 = true)
    (n3 : i32.valid v3 = true)
    (n4 : i32.valid v4 = true) :
    ∃ t1 t2 t3 t4, Good ((caller.charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ Good t3 t4 e4.nodes e4.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_get.parameters
          [.vectorReference s0, .vectorReference s1, .value e1, .value e2, .value e3, .value e4] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩,⟨i32,v3⟩,⟨i32,v4⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = t4.scalars.work+7 ∧ t4.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
    (fun h => rfl)
  have coreV : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge _ 1 1))
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  obtain ⟨t4,ran4,g4⟩ := scalar_eval e4 t3 v4 hs4 (by rw [envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d4)
  refine ⟨t1,t2,t3,t4,g1,g2,g3,g4,?_⟩
  have res1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,ty3,ran3]
  have res4 : resolve t3 (.scalar i32 false true) (.value e4) = some (t4,.scalar i32 true v4) := by
    simp [resolve,ty4,ran4]
  have frameT : t4.frame = caller.frame := g4.1.1.trans (g3.1.1.trans (g2.1.1.trans (g1.1.1)))
  have fs : t4.frame.state = caller.frame.state := by rw [frameT]
  have fr : t4.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t4.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t4.scalars.memory = caller.scalars.memory := g4.1.2.2.2.1.trans (g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1)))
  have hbind : t4.scalars.bindings = caller.scalars.bindings := g4.1.2.2.2.2.1.trans (g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1)))
  have hbase : t4.scalars.baseMemory = caller.scalars.baseMemory := g4.1.2.2.2.2.2.trans (g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2)))
  have hp : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_get.parameters =
      [.vector s64 true,.vector s64 true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true) (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame) (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, res1, res2, res3, res4]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, n4, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  have a4 := g4.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

theorem prepare_prod (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0)
    (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (e1 e2 e3 e4 e5 : NExpr) (v1 v2 v3 v4 v5 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32)
    (ty3 : e3.resultType = i32)
    (ty4 : e4.resultType = i32)
    (ty5 : e5.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (d4 : e4.denote (envOf caller) = some v4)
    (d5 : e5.denote (envOf caller) = some v5)
    (n1 : i32.valid v1 = true)
    (n2 : i32.valid v2 = true)
    (n3 : i32.valid v3 = true)
    (n4 : i32.valid v4 = true)
    (n5 : i32.valid v5 = true) :
    ∃ t1 t2 t3 t4 t5, Good ((caller.charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ Good t3 t4 e4.nodes e4.nodes ∧ Good t4 t5 e5.nodes e5.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product.parameters
          [.vectorReference s0, .vectorReference s1, .value e1, .value e2, .value e3, .value e4, .value e5] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.scalar 0,.scalar 1,.scalar 2,.scalar 3,.scalar 4] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩,⟨i32,v3⟩,⟨i32,v4⟩,⟨i32,v5⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = t5.scalars.work+8 ∧ t5.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
    (fun h => rfl)
  have coreV : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge _ 1 1))
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  obtain ⟨t4,ran4,g4⟩ := scalar_eval e4 t3 v4 hs4 (by rw [envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d4)
  obtain ⟨t5,ran5,g5⟩ := scalar_eval e5 t4 v5 hs5 (by rw [envOf_core g4.1, envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d5)
  refine ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,?_⟩
  have res1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,ty3,ran3]
  have res4 : resolve t3 (.scalar i32 false true) (.value e4) = some (t4,.scalar i32 true v4) := by
    simp [resolve,ty4,ran4]
  have res5 : resolve t4 (.scalar i32 false true) (.value e5) = some (t5,.scalar i32 true v5) := by
    simp [resolve,ty5,ran5]
  have frameT : t5.frame = caller.frame := g5.1.1.trans (g4.1.1.trans (g3.1.1.trans (g2.1.1.trans (g1.1.1))))
  have fs : t5.frame.state = caller.frame.state := by rw [frameT]
  have fr : t5.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t5.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t5.scalars.memory = caller.scalars.memory := g5.1.2.2.2.1.trans (g4.1.2.2.2.1.trans (g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1))))
  have hbind : t5.scalars.bindings = caller.scalars.bindings := g5.1.2.2.2.2.1.trans (g4.1.2.2.2.2.1.trans (g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1))))
  have hbase : t5.scalars.baseMemory = caller.scalars.baseMemory := g5.1.2.2.2.2.2.trans (g4.1.2.2.2.2.2.trans (g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2))))
  have hp : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product.parameters =
      [.vector s64 true,.vector s64 true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true) (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame) (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, res1, res2, res3, res4, res5]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, n4, n5, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  have a4 := g4.2.2.2.2.1
  have a5 := g5.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

theorem prepare_all (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0)
    (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (e1 e2 e3 : NExpr) (v1 v2 v3 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32)
    (ty3 : e3.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (n1 : i32.valid v1 = true)
    (n2 : i32.valid v2 = true)
    (n3 : i32.valid v3 = true) :
    ∃ t1 t2 t3, Good ((caller.charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product_all.parameters
          [.vectorReference s0, .vectorReference s1, .value e1, .value e2, .value e3] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.scalar 0,.scalar 1,.scalar 2] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩,⟨i32,v3⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = t3.scalars.work+6 ∧ t3.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
    (fun h => rfl)
  have coreV : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge _ 1 1))
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  refine ⟨t1,t2,t3,g1,g2,g3,?_⟩
  have res1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,ty3,ran3]
  have frameT : t3.frame = caller.frame := g3.1.1.trans (g2.1.1.trans (g1.1.1))
  have fs : t3.frame.state = caller.frame.state := by rw [frameT]
  have fr : t3.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t3.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t3.scalars.memory = caller.scalars.memory := g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1))
  have hbind : t3.scalars.bindings = caller.scalars.bindings := g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1))
  have hbase : t3.scalars.baseMemory = caller.scalars.baseMemory := g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2))
  have hp : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product_all.parameters =
      [.vector s64 true,.vector s64 true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true) (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame) (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, res1, res2, res3]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

theorem prepare_ap (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0)
    (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (e1 e2 e3 e4 e5 : NExpr) (v1 v2 v3 v4 v5 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32)
    (ty3 : e3.resultType = i32)
    (ty4 : e4.resultType = i32)
    (ty5 : e5.resultType = s64)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (d4 : e4.denote (envOf caller) = some v4)
    (d5 : e5.denote (envOf caller) = some v5)
    (n1 : i32.valid v1 = true)
    (n2 : i32.valid v2 = true)
    (n3 : i32.valid v3 = true)
    (n4 : i32.valid v4 = true)
    (n5 : s64.valid v5 = true) :
    ∃ t1 t2 t3 t4 t5, Good ((caller.charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ Good t3 t4 e4.nodes e4.nodes ∧ Good t4 t5 e5.nodes e5.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_2.parameters
          [.vectorReference s0, .vectorReference s1, .value e1, .value e2, .value e3, .value e4, .value e5] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.scalar 0,.scalar 1,.scalar 2,.scalar 3,.scalar 4] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩,⟨i32,v3⟩,⟨i32,v4⟩,⟨s64,v5⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = t5.scalars.work+8 ∧ t5.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
    (fun h => rfl)
  have coreV : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge _ 1 1))
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  obtain ⟨t4,ran4,g4⟩ := scalar_eval e4 t3 v4 hs4 (by rw [envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d4)
  obtain ⟨t5,ran5,g5⟩ := scalar_eval e5 t4 v5 hs5 (by rw [envOf_core g4.1, envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d5)
  refine ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,?_⟩
  have res1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,ty3,ran3]
  have res4 : resolve t3 (.scalar i32 false true) (.value e4) = some (t4,.scalar i32 true v4) := by
    simp [resolve,ty4,ran4]
  have res5 : resolve t4 (.scalar s64 false true) (.value e5) = some (t5,.scalar s64 true v5) := by
    simp [resolve,ty5,ran5]
  have frameT : t5.frame = caller.frame := g5.1.1.trans (g4.1.1.trans (g3.1.1.trans (g2.1.1.trans (g1.1.1))))
  have fs : t5.frame.state = caller.frame.state := by rw [frameT]
  have fr : t5.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t5.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t5.scalars.memory = caller.scalars.memory := g5.1.2.2.2.1.trans (g4.1.2.2.2.1.trans (g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1))))
  have hbind : t5.scalars.bindings = caller.scalars.bindings := g5.1.2.2.2.2.1.trans (g4.1.2.2.2.2.1.trans (g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1))))
  have hbase : t5.scalars.baseMemory = caller.scalars.baseMemory := g5.1.2.2.2.2.2.trans (g4.1.2.2.2.2.2.trans (g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2))))
  have hp : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_2.parameters =
      [.vector s64 true,.vector s64 true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar s64 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true) (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame) (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, res1, res2, res3, res4, res5]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, n4, n5, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  have a4 := g4.2.2.2.2.1
  have a5 := g5.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

theorem prepare_ar (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0)
    (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (e1 e2 e3 e4 e5 e6 : NExpr) (v1 v2 v3 v4 v5 v6 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true) (hs6 : e6.scalarOnly = true)
    (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32)
    (ty3 : e3.resultType = i32)
    (ty4 : e4.resultType = i32)
    (ty5 : e5.resultType = i32)
    (ty6 : e6.resultType = s64)
    (d1 : e1.denote (envOf caller) = some v1)
    (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (d4 : e4.denote (envOf caller) = some v4)
    (d5 : e5.denote (envOf caller) = some v5)
    (d6 : e6.denote (envOf caller) = some v6)
    (n1 : i32.valid v1 = true)
    (n2 : i32.valid v2 = true)
    (n3 : i32.valid v3 = true)
    (n4 : i32.valid v4 = true)
    (n5 : i32.valid v5 = true)
    (n6 : s64.valid v6 = true) :
    ∃ t1 t2 t3 t4 t5 t6, Good ((caller.charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧ Good t3 t4 e4.nodes e4.nodes ∧ Good t4 t5 e5.nodes e5.nodes ∧ Good t5 t6 e6.nodes e6.nodes ∧ 
      ∃ Sinit, prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_3.parameters
          [.vectorReference s0, .vectorReference s1, .value e1, .value e2, .value e3, .value e4, .value e5, .value e6] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.scalar 0,.scalar 1,.scalar 2,.scalar 3,.scalar 4,.scalar 5] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩,⟨i32,v3⟩,⟨i32,v4⟩,⟨i32,v5⟩,⟨s64,v6⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩,⟨(callerP caller).length+5,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = t6.scalars.work+9 ∧ t6.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
    (fun h => rfl)
  have coreV : Core caller ((caller.charge 1 1).charge 1 1) := ((core_charge caller 1 1).trans (core_charge _ 1 1))
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) v1 hs1 (by rw [envOf_core coreV]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core coreV]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d3)
  obtain ⟨t4,ran4,g4⟩ := scalar_eval e4 t3 v4 hs4 (by rw [envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d4)
  obtain ⟨t5,ran5,g5⟩ := scalar_eval e5 t4 v5 hs5 (by rw [envOf_core g4.1, envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d5)
  obtain ⟨t6,ran6,g6⟩ := scalar_eval e6 t5 v6 hs6 (by rw [envOf_core g5.1, envOf_core g4.1, envOf_core g3.1, envOf_core g2.1, envOf_core g1.1, envOf_core coreV]; exact d6)
  refine ⟨t1,t2,t3,t4,t5,t6,g1,g2,g3,g4,g5,g6,?_⟩
  have res1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,ty3,ran3]
  have res4 : resolve t3 (.scalar i32 false true) (.value e4) = some (t4,.scalar i32 true v4) := by
    simp [resolve,ty4,ran4]
  have res5 : resolve t4 (.scalar i32 false true) (.value e5) = some (t5,.scalar i32 true v5) := by
    simp [resolve,ty5,ran5]
  have res6 : resolve t5 (.scalar s64 false true) (.value e6) = some (t6,.scalar s64 true v6) := by
    simp [resolve,ty6,ran6]
  have frameT : t6.frame = caller.frame := g6.1.1.trans (g5.1.1.trans (g4.1.1.trans (g3.1.1.trans (g2.1.1.trans (g1.1.1)))))
  have fs : t6.frame.state = caller.frame.state := by rw [frameT]
  have fr : t6.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t6.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t6.scalars.memory = caller.scalars.memory := g6.1.2.2.2.1.trans (g5.1.2.2.2.1.trans (g4.1.2.2.2.1.trans (g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans (g1.1.2.2.2.1)))))
  have hbind : t6.scalars.bindings = caller.scalars.bindings := g6.1.2.2.2.2.1.trans (g5.1.2.2.2.2.1.trans (g4.1.2.2.2.2.1.trans (g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans (g1.1.2.2.2.2.1)))))
  have hbase : t6.scalars.baseMemory = caller.scalars.baseMemory := g6.1.2.2.2.2.2.trans (g5.1.2.2.2.2.2.trans (g4.1.2.2.2.2.2.trans (g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans (g1.1.2.2.2.2.2)))))
  have hp : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_3.parameters =
      [.vector s64 true,.vector s64 true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar s64 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true) (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame) (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, res1, res2, res3, res4, res5, res6]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, n4, n5, n6, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  have a4 := g4.2.2.2.2.1
  have a5 := g5.2.2.2.2.1
  have a6 := g6.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

theorem prepare_ctor (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m2 : Bool} {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0)
    (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2) :
    
      ∃ Sinit, prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_new0.parameters
          [.vectorReference s0, .vectorReference s1, .vectorReference s2] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.vector 2] ∧
        Sinit.scalars.memory = callerP caller ∧
        Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩,⟨V2,.integer s64,false,.root vsc2⟩]⟩ ∧
        Sinit.scalars.work = (((caller.charge 1 1).charge 1 1).charge 1 1).scalars.work+4 ∧ (((caller.charge 1 1).charge 1 1).charge 1 1).scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
    (fun h => rfl)
  have rv2 := resolve_vref ((caller.charge 1 1).charge 1 1) s64 false ok2.slot ok2.binding ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
    (fun h => absurd h (by decide))
  have coreV : Core caller (((caller.charge 1 1).charge 1 1).charge 1 1) := (((core_charge caller 1 1).trans (core_charge _ 1 1)).trans (core_charge _ 1 1))
  have hp : Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_new0.parameters =
      [.vector s64 true,.vector s64 true,.vector s64 false] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true) (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame) (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  have b2 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ : Frame) (V := V2) (vsc := vsc2) (m := m2) (vbuf := vbuf2) s64 false ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1 b2
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, rv2]
  simp [b0, b1, b2, bindAll, bindOne, CppState.bindArgument, callerP,
    NState.observe, CppState.State.observe, NState.charge]


end Proofs.LazySegPrepare
