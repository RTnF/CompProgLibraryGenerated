import Proofs.MatMulPrepare
import Proofs.Generated.TreePath

namespace Proofs.TreePathPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

theorem prepare_ta (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 true true vbuf1)
    (e1 e2 : NExpr) (v1 v2 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (n1 : i32.valid v1 = true) (n2 : i32.valid v2 = true) :
    ∃ t1 t2, Good ((caller.charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller Proofs.TreePathInstance.tree_path.parameters
          [.vectorReference s0,.vectorReference s1,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,true,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+5 ∧ t2.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller i32 false ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => absurd h (by decide))
  have rv1 := resolve_vref (caller.charge 1 1) i32 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => rfl)
  have core2 : Core caller ((caller.charge 1 1).charge 1 1) := (core_charge caller 1 1).trans (core_charge _ 1 1)
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) v1 hs1
    (by rw [envOf_core core2]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core core2]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have res1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) =
      some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have frameT : t2.frame = caller.frame := g2.1.1.trans g1.1.1
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := g2.1.2.2.2.1.trans g1.1.2.2.2.1
  have hbind : t2.scalars.bindings = caller.scalars.bindings := g2.1.2.2.2.2.1.trans g1.1.2.2.2.2.1
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := g2.1.2.2.2.2.2.trans g1.1.2.2.2.2.2
  have hp : Proofs.TreePathInstance.tree_path.parameters =
      [.vector i32 false,.vector i32 true,.scalar i32 false true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := m0)
    (vbuf := vbuf0) i32 false ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer i32,false,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) i32 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, res1, res2]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, bindAll, bindOne, CppState.bindArgument, n1, n2, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

end Proofs.TreePathPrepare
