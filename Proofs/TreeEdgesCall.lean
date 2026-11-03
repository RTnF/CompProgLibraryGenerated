import Proofs.TreeEdgesPrepare
import Proofs.TreeEdgesExec
import Proofs.MultiVecCall

namespace Proofs.TreeEdgesCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeEdgesPrepare Proofs.TreeEdgesExec
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `tree_edges_from_parent`: three `int` vectors, the last two writable. -/
def mvTE (V0 V1 V2 vsc0 vsc1 vsc2 : Nat) (m0 : Bool) (L0 T0 sc N : Nat) (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2) : MV where
  nv := 3
  ty := fun _ => i32
  wV := fun k => decide (k = 1 ∨ k = 2)
  flag := fun k => if k = 0 then m0 else true
  R := fun k => if k = 0 then V0 else if k = 1 then V1 else V2
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else vsc2
  perm := by
    intro k hk
    have : k = 1 ∨ k = 2 := by simpa using hk
    rcases this with rfl | rfl <;> simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 1 ∨ k = 2 := by simpa using hw
    rcases this with rfl | rfl
    · have : j = 0 ∨ j = 2 := by omega
      rcases this with rfl | rfl
      · simpa using h01
      · simpa using h12.symm
    · have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · simpa using h02
      · simpa using h12

def bbTE (b0 b1 b2 : Buffer Value) : Nat → Buffer Value := fun k => if k = 0 then b0 else if k = 1 then b1 else b2

theorem wr_bodyTE : WrM (fun k => decide (k = 1 ∨ k = 2)) (bodyTE 3) = true := by decide

theorem cases3 (k : Nat) (hk : k < 3) : k = 0 ∨ k = 1 ∨ k = 2 := by omega

theorem fwTE_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2)
    (Pr F T : List Int) (hP : Pr.length < 2147483647) (hF : F.length < 2147483647) (hT : T.length < 2147483647)
    (i0 : vbuf0.items = Pr.map Value.integer) (i1 : vbuf1.items = F.map Value.integer)
    (i2 : vbuf2.items = T.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) :
    FWM (mvTE V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12)
      (VE Pr F T) (bbTE vbuf0 vbuf1 vbuf2) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,true,.root vsc1⟩,⟨V2,.integer i32,true,.root vsc2⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTE] using ok0.vtag
    · simpa [mvTE] using ok1.vtag
    · simpa [mvTE] using ok2.vtag
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTE, bbTE] using ok0.vfound
    · simpa [mvTE, bbTE] using ok1.vfound
    · simpa [mvTE, bbTE] using ok2.vfound
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTE] using ok0.flag
    · simpa [mvTE] using ok1.flag
    · simpa [mvTE] using ok2.flag
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTE, bbTE, VE] using i0
    · simpa [mvTE, bbTE, VE] using i1
    · simpa [mvTE, bbTE, VE] using i2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTE, bbTE] using bv0
    · simpa [mvTE, bbTE] using bv1
    · simpa [mvTE, bbTE] using bv2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTE, bbTE] using l0
    · simpa [mvTE, bbTE] using l1
    · simpa [mvTE, bbTE] using l2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTE, bbTE] using o0
    · simpa [mvTE, bbTE] using o1
    · simpa [mvTE, bbTE] using o2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simp [VE]; omega
    · simp [VE]; omega
    · simp [VE]; omega

set_option maxHeartbeats 8000000 in
/-- `cp::tree_edges_from_parent(parent, from, to, n)` appends the arcs of the parent array and returns their number. -/
theorem tree_edges_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2)
    (Pr F0 T0 : List Int) (n : Nat) (hn : n < 1073741824) (hPl : n ≤ Pr.length) (hF : 2 * n ≤ F0.length)
    (hT : 2 * n ≤ T0.length) (hP2 : Pr.length < 2147483647) (hF2 : F0.length < 2147483647) (hT2 : T0.length < 2147483647)
    (hPv : ∀ x ∈ Pr, i32.valid x = true)
    (i0 : vbuf0.items = Pr.map Value.integer) (i1 : vbuf1.items = F0.map Value.integer)
    (i2 : vbuf2.items = T0.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32) (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.TreeEdgesInstance.tree_edges_from_parent.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.value e1] = some Sinit ∧
      Proofs.TreeEdgesInstance.tree_edges_from_parent.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.value e1] =
        .finished (res,.scalar (((arcP Pr n n).length : Nat) : Int)) ∧
      ScalarPostM (mvTE V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12)
        caller Sinit res e1.nodes (420 * n + 200) caller.scalars.memory (4 * n)
        (VE Pr (FFt Pr n n F0) (TTt Pr n n T0)) := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_te caller ok0 ok1 ok2 e1 (n : Int) hs1 ty1 value1 (validN n hn32)
  have fwS := fwTE_init caller ok0 ok1 ok2 h01 h02 h12 Pr F0 T0 hP2 hF2 hT2 i0 i1 i2 bv0 bv1 bv2 l0 l1 l2 o0 o1 o2
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cs,hrps⟩,hcost,hneed,hwk⟩ :=
    body_exec (mvTE V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12) rfl rfl rfl rfl Pr F0 T0 (callerP caller) n hn hPl hF hT
    hPv (n + 2) (Nat.le_refl _)
  have hallM : (arcP Pr n n).length < 2147483648 := by have := arcP_len_le Pr n n; omega
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n] := by
    simp [gS]
  have gw := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hpost := call_vecm (mvTE V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12) (fun k => decide (k = 1 ∨ k = 2))
    (by intro k hk; have : k = 1 ∨ k = 2 := by simpa using hk
        rcases this with rfl | rfl <;> simp [mvTE])
    caller Proofs.TreeEdgesInstance.tree_edges_from_parent
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqTE]; exact wr_bodyTE)
    (n + 2) rr (by rw [hmk, body_eqTE]; exact hexec) _ hret i32 rfl (validN _ hallM) (by omega) (by simp [hlenP])
    e1.nodes (420 * n + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TreeEdgesCall
