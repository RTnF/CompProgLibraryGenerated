import Proofs.MatMulExec

namespace Proofs.MatMulPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulExec

/-- Binding a caller root vector in a frame (whatever bindings it already has). -/
theorem bindRoot_g (f : Frame) {V vsc : Nat} {m : Bool} {vbuf : Buffer Value} (ty : Ty) (w : Bool)
    (valid : f.state.wellFormed = true) (vtag : f.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (vfound : f.state.storage.lookup V = some vbuf) (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (flag : f.rootWritable[V]? = some m) (hperm : w = true → m = true) :
    f.bindRoot V (.integer ty) vsc w = some (f.addBinding ⟨V,.integer ty,w,.root vsc⟩) := by
  have vobject : f.object V (.integer ty) = some (vbuf,⟨.integer ty,none,some vsc,[]⟩) :=
    object_runs f V _ vbuf _ valid vfound vtag rfl
  have vrooted : f.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ vtag rfl
  have vmax : f.maximum V = some m := maximum_runs f V V m lengths vrooted flag
  simp only [Frame.bindRoot, vobject, vmax, Bind.bind, Option.bind]
  simp
  exact hperm

/-- Resolving a vector reference argument against a caller whose slot holds a bound root. -/
theorem resolve_vref (c : NState) (ty : Ty) (writable : Bool) {slot vb V vsc : Nat} {wb m : Bool} {vbuf : Buffer Value}
    (hslot : c.vectorSlot slot = some vb) (hbind : c.frame.bindings[vb]? = some ⟨V,.integer ty,wb,.root vsc⟩)
    (valid : c.frame.state.wellFormed = true) (vtag : c.frame.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩)
    (vfound : c.frame.state.storage.lookup V = some vbuf) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
    (flag : c.frame.rootWritable[V]? = some m) (hperm : wb = true → m = true) (hw : writable = true → wb = true) :
    resolve c (.vector ty writable) (.vectorReference slot) = some (c.charge 1 1, .vector V vsc ty writable) := by
  obtain ⟨resolved, _, _⟩ := resolve_vroot c.frame vb V vsc ty wb m vbuf hbind valid vtag vfound lengths flag hperm
  simp [resolve, hslot, hbind, resolved]
  exact hw

/-- The caller owns a root vector with element type `ty`, passed through the slot `vslot`. -/
structure VOKG (caller : NState) (ty : Ty) (vslot vb V vsc : Nat) (wb m : Bool) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer ty,wb,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer ty,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some m
  perm : wb = true → m = true
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

theorem prepare_mm (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc2 s2 vb2 V2 vsc1 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller u64 s2 vb2 V2 vsc2 true true vbuf2)
    (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v) (hv : i32.valid v = true) :
    ∃ t, Good (((caller.charge 1 1).charge 1 1).charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.SquareMatrixInstance.mat_mul_std_vector_unsigned_long_long.parameters
          [.vectorReference s0,.vectorReference s1,.vectorReference s2,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.vector 2,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer u64,false,.root vsc0⟩,⟨V1,.integer u64,false,.root vsc1⟩,⟨V2,.integer u64,true,.root vsc2⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+5 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller u64 false ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => absurd h (by decide))
  have rv1 := resolve_vref (caller.charge 1 1) u64 false ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => absurd h (by decide))
  have rv2 := resolve_vref ((caller.charge 1 1).charge 1 1) u64 true ok2.slot ok2.binding ok2.valid ok2.vtag ok2.vfound
    ok2.lengths ok2.flag ok2.perm (fun h => rfl)
  have core3 : Core caller (((caller.charge 1 1).charge 1 1).charge 1 1) :=
    ((core_charge caller 1 1).trans (core_charge _ 1 1)).trans (core_charge _ 1 1)
  obtain ⟨t,ran,good⟩ := scalar_eval e (((caller.charge 1 1).charge 1 1).charge 1 1) v hs
    (by rw [envOf_core core3]; exact value)
  refine ⟨t,good,?_⟩
  have res : resolve (((caller.charge 1 1).charge 1 1).charge 1 1) (.scalar i32 false true) (.value e) =
      some (t,.scalar i32 true v) := by
    simp [resolve,hty,ran]
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have hp : Proofs.SquareMatrixInstance.mat_mul_std_vector_unsigned_long_long.parameters =
      [.vector u64 false,.vector u64 false,.vector u64 true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := m0)
    (vbuf := vbuf0) u64 false ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer u64,false,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := m1) (vbuf := vbuf1) u64 false ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  have b2 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer u64,false,.root vsc0⟩,
    ⟨V1,.integer u64,false,.root vsc1⟩]⟩ : Frame)
    (V := V2) (vsc := vsc2) (m := true) (vbuf := vbuf2) u64 true ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons, List.length_singleton] at b0 b1 b2
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, rv2, res]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, b2, bindAll, bindOne, CppState.bindArgument, hv, callerP,
    NState.observe, CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at g
  omega

end Proofs.MatMulPrepare
