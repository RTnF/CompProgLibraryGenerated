import Proofs.MatMulPrepare
import Proofs.Generated.TopologicalSort

namespace Proofs.TopoSortPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare

theorem prepare_ts (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (e : NExpr) (v : Int) (hs : e.scalarOnly = true) (hty : e.resultType = i32)
    (value : e.denote (envOf caller) = some v) (hv : i32.valid v = true) :
    ∃ t, Good ((((caller.charge 1 1).charge 1 1).charge 1 1).charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.TopoInstance.topological_sort.parameters
          [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.vector 2,.vector 3,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,false,.root vsc1⟩,⟨V2,.integer i32,true,.root vsc2⟩,
           ⟨V3,.integer i32,true,.root vsc3⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+6 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller i32 false ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => absurd h (by decide))
  have rv1 := resolve_vref (caller.charge 1 1) i32 false ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => absurd h (by decide))
  have rv2 := resolve_vref ((caller.charge 1 1).charge 1 1) i32 true ok2.slot ok2.binding ok2.valid ok2.vtag ok2.vfound
    ok2.lengths ok2.flag ok2.perm (fun h => rfl)
  have rv3 := resolve_vref (((caller.charge 1 1).charge 1 1).charge 1 1) i32 true ok3.slot ok3.binding ok3.valid ok3.vtag
    ok3.vfound ok3.lengths ok3.flag ok3.perm (fun h => rfl)
  have core4 : Core caller ((((caller.charge 1 1).charge 1 1).charge 1 1).charge 1 1) :=
    (((core_charge caller 1 1).trans (core_charge _ 1 1)).trans (core_charge _ 1 1)).trans (core_charge _ 1 1)
  obtain ⟨t,ran,good⟩ := scalar_eval e ((((caller.charge 1 1).charge 1 1).charge 1 1).charge 1 1) v hs
    (by rw [envOf_core core4]; exact value)
  refine ⟨t,good,?_⟩
  have res : resolve ((((caller.charge 1 1).charge 1 1).charge 1 1).charge 1 1) (.scalar i32 false true) (.value e) =
      some (t,.scalar i32 true v) := by
    simp [resolve,hty,ran]
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have hp : Proofs.TopoInstance.topological_sort.parameters =
      [.vector i32 false,.vector i32 false,.vector i32 true,.vector i32 true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := m0)
    (vbuf := vbuf0) i32 false ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer i32,false,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := m1) (vbuf := vbuf1) i32 false ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  have b2 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer i32,false,.root vsc0⟩,
    ⟨V1,.integer i32,false,.root vsc1⟩]⟩ : Frame)
    (V := V2) (vsc := vsc2) (m := true) (vbuf := vbuf2) i32 true ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
  have b3 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer i32,false,.root vsc0⟩,
    ⟨V1,.integer i32,false,.root vsc1⟩,⟨V2,.integer i32,true,.root vsc2⟩]⟩ : Frame)
    (V := V3) (vsc := vsc3) (m := true) (vbuf := vbuf3) i32 true ok3.valid ok3.vtag ok3.vfound ok3.lengths ok3.flag ok3.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons, List.length_singleton] at b0 b1 b2 b3
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, rv2, rv3, res]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, b2, b3, bindAll, bindOne, CppState.bindArgument, hv, callerP,
    NState.observe, CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at g
  omega

end Proofs.TopoSortPrepare
