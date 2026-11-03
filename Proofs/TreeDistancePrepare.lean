import Proofs.MatMulPrepare
import Proofs.Generated.TreeDistance

namespace Proofs.TreeDistancePrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

theorem prepare_td (caller : NState) {s0 vb0 V0 vsc0 : Nat} {m0 : Bool} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0)
    (e1 e2 e3 : NExpr) (v1 v2 v3 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (hs3 : e3.scalarOnly = true) (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (n1 : i32.valid v1 = true) (n2 : i32.valid v2 = true) (n3 : i32.valid v3 = true) :
    ∃ t1 t2 t3, Good (caller.charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧
      ∃ Sinit, prepare caller Proofs.TreeDistanceInstance.tree_distance_std_vector_long_long.parameters
          [.vectorReference s0,.value e1,.value e2,.value e3] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1,.scalar 2] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩,⟨i32,v3⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,
          ⟨(callerP caller).length+2,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,false,.root vsc0⟩]⟩ ∧
        Sinit.scalars.work = t3.scalars.work+5 ∧ t3.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 false ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => absurd h (by decide))
  have core1 : Core caller (caller.charge 1 1) := core_charge caller 1 1
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 (caller.charge 1 1) v1 hs1 (by rw [envOf_core core1]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core core1]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 hs3 (by rw [envOf_core g2.1, envOf_core g1.1, envOf_core core1]; exact d3)
  refine ⟨t1,t2,t3,g1,g2,g3,?_⟩
  have res1 : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,ty3,ran3]
  have frameT : t3.frame = caller.frame := g3.1.1.trans (g2.1.1.trans g1.1.1)
  have fs : t3.frame.state = caller.frame.state := by rw [frameT]
  have fr : t3.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t3.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t3.scalars.memory = caller.scalars.memory := g3.1.2.2.2.1.trans (g2.1.2.2.2.1.trans g1.1.2.2.2.1)
  have hbind : t3.scalars.bindings = caller.scalars.bindings :=
    g3.1.2.2.2.2.1.trans (g2.1.2.2.2.2.1.trans g1.1.2.2.2.2.1)
  have hbase : t3.scalars.baseMemory = caller.scalars.baseMemory :=
    g3.1.2.2.2.2.2.trans (g2.1.2.2.2.2.2.trans g1.1.2.2.2.2.2)
  have hp : Proofs.TreeDistanceInstance.tree_distance_std_vector_long_long.parameters =
      [.vector s64 false,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := m0)
    (vbuf := vbuf0) s64 false ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons, List.length_singleton] at b0
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, res1, res2, res3]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, bindAll, bindOne, CppState.bindArgument, n1, n2, n3, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  have a3 := g3.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  left
  omega

end Proofs.TreeDistancePrepare
