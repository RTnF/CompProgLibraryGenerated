import Proofs.MatMulPrepare
import Proofs.Generated.InvGcd

namespace Proofs.InvGcdPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

theorem prepare_ta (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0)
    (e1 e2 : NExpr) (v1 v2 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = s64) (ty2 : e2.resultType = s64)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (n1 : s64.valid v1 = true) (n2 : s64.valid v2 = true) :
    ∃ t1 t2, Good (caller.charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller Proofs.InvGcdInstance.inv_gcd.parameters
          [.vectorReference s0,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨s64,v1⟩,⟨s64,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+4 ∧ t2.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have core1 : Core caller (caller.charge 1 1) := core_charge caller 1 1
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 (caller.charge 1 1) v1 hs1 (by rw [envOf_core core1]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core core1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have res1 : resolve (caller.charge 1 1) (.scalar s64 false true) (.value e1) = some (t1,.scalar s64 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar s64 false true) (.value e2) = some (t2,.scalar s64 true v2) := by
    simp [resolve,ty2,ran2]
  have frameT : t2.frame = caller.frame := g2.1.1.trans g1.1.1
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := g2.1.2.2.2.1.trans g1.1.2.2.2.1
  have hbind : t2.scalars.bindings = caller.scalars.bindings := g2.1.2.2.2.2.1.trans g1.1.2.2.2.2.1
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := g2.1.2.2.2.2.2.trans g1.1.2.2.2.2.2
  have hp : Proofs.InvGcdInstance.inv_gcd.parameters =
      [.vector s64 true,.scalar s64 false true,.scalar s64 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true)
    (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, res1, res2]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, bindAll, bindOne, CppState.bindArgument, n1, n2, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

end Proofs.InvGcdPrepare
