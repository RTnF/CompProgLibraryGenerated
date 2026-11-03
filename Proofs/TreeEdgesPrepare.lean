import Proofs.MatMulPrepare
import Proofs.Generated.TreeEdges

namespace Proofs.TreeEdgesPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

theorem prepare_te (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2)
    (e1 : NExpr) (v1 : Int) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1) (n1 : i32.valid v1 = true) :
    ∃ t1, Good (((caller.charge 1 1).charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧
      ∃ Sinit, prepare caller Proofs.TreeEdgesInstance.tree_edges_from_parent.parameters
          [.vectorReference s0,.vectorReference s1,.vectorReference s2,.value e1] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.vector 2,.scalar 0] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,true,.root vsc1⟩,⟨V2,.integer i32,true,.root vsc2⟩]⟩ ∧
        Sinit.scalars.work = t1.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak ∧
        t1.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller i32 false ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => absurd h (by decide))
  have rv1 := resolve_vref (caller.charge 1 1) i32 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => rfl)
  have rv2 := resolve_vref ((caller.charge 1 1).charge 1 1) i32 true ok2.slot ok2.binding ok2.valid ok2.vtag ok2.vfound
    ok2.lengths ok2.flag ok2.perm (fun h => rfl)
  have core3 : Core caller (((caller.charge 1 1).charge 1 1).charge 1 1) :=
    ((core_charge caller 1 1).trans (core_charge _ 1 1)).trans (core_charge _ 1 1)
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 (((caller.charge 1 1).charge 1 1).charge 1 1) v1 hs1
    (by rw [envOf_core core3]; exact d1)
  refine ⟨t1,g1,?_⟩
  have res1 : resolve (((caller.charge 1 1).charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) =
      some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have frameT : t1.frame = caller.frame := g1.1.1
  have fs : t1.frame.state = caller.frame.state := by rw [frameT]
  have fr : t1.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t1.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t1.scalars.memory = caller.scalars.memory := g1.1.2.2.2.1
  have hbind : t1.scalars.bindings = caller.scalars.bindings := g1.1.2.2.2.2.1
  have hbase : t1.scalars.baseMemory = caller.scalars.baseMemory := g1.1.2.2.2.2.2
  have hp : Proofs.TreeEdgesInstance.tree_edges_from_parent.parameters =
      [.vector i32 false,.vector i32 true,.vector i32 true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := m0)
    (vbuf := vbuf0) i32 false ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer i32,false,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) i32 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  have b2 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer i32,false,.root vsc0⟩,
    ⟨V1,.integer i32,true,.root vsc1⟩]⟩ : Frame)
    (V := V2) (vsc := vsc2) (m := true) (vbuf := vbuf2) i32 true ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons, List.length_singleton] at b0 b1 b2
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, rv2, res1]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, b2, bindAll, bindOne, CppState.bindArgument, n1, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  omega

end Proofs.TreeEdgesPrepare
