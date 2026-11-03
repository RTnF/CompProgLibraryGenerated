import Proofs.TreePathPrepare
import Proofs.TreePathExec
import Proofs.MultiVecCall

namespace Proofs.TreePathCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreePathPrepare Proofs.TreePathExec
open Proofs.TreeArcCostsExec (VC VC_get0 VC_get1 VC_set1)
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `tree_path`: two `int` vectors, the last one writable. -/
def mvTP (V0 V1 vsc0 vsc1 : Nat) (m0 : Bool) (L0 T0 sc N : Nat) (h01 : V0 ≠ V1) : MV where
  nv := 2
  ty := fun _ => i32
  wV := fun k => decide (k = 1)
  flag := fun k => if k = 0 then m0 else true
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by
    intro k hk
    have : k = 1 := by simpa using hk
    subst this; simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 1 := by simpa using hw
    subst this
    have : j = 0 := by omega
    subst this
    simpa using h01

def bbTP (b0 b1 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else b1

theorem wr_bodyTP : WrM (fun k => decide (k = 1)) (bodyTP 2) = true := by decide

theorem cases2P (k : Nat) (hk : k < 2) : k = 0 ∨ k = 1 := by omega

theorem fwTP_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (V O : List Int) (hV : V.length < 2147483647) (hO : O.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (i1 : vbuf1.items = O.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvTP V0 V1 vsc0 vsc1 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01)
      (VC V O) (bbTP vbuf0 vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,true,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2P k hk with rfl | rfl
    · simpa [mvTP] using ok0.vtag
    · simpa [mvTP] using ok1.vtag
  · intro k hk
    rcases cases2P k hk with rfl | rfl
    · simpa [mvTP, bbTP] using ok0.vfound
    · simpa [mvTP, bbTP] using ok1.vfound
  · intro k hk
    rcases cases2P k hk with rfl | rfl
    · simpa [mvTP] using ok0.flag
    · simpa [mvTP] using ok1.flag
  · intro k hk
    rcases cases2P k hk with rfl | rfl
    · simpa [mvTP, bbTP, VC] using i0
    · simpa [mvTP, bbTP, VC] using i1
  · intro k hk
    rcases cases2P k hk with rfl | rfl
    · simpa [mvTP, bbTP] using bv0
    · simpa [mvTP, bbTP] using bv1
  · intro k hk
    rcases cases2P k hk with rfl | rfl
    · simpa [mvTP, bbTP] using l0
    · simpa [mvTP, bbTP] using l1
  · intro k hk
    rcases cases2P k hk with rfl | rfl
    · simpa [mvTP, bbTP] using o0
    · simpa [mvTP, bbTP] using o1
  · intro k hk
    rcases cases2P k hk with rfl | rfl
    · simp [VC]; omega
    · simp [VC]; omega

set_option maxHeartbeats 8000000 in
/-- `cp::tree_path(parent, out, from, to)` writes the chain `ch 0 = to, ch 1, ..., ch m = from` to `out[0 .. m]` and returns `m + 1`. -/
theorem tree_path_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (V O : List Int) (ch : Nat → Nat) (f tg m : Nat) (hm : m + 1 ≤ O.length)
    (hlt : ∀ i, i ≤ m → ch i < 2147483648)
    (hch : ∀ i, i < m → ch i < V.length ∧ V.getD (ch i) 0 = ((ch (i + 1) : Nat) : Int)) (hne : ∀ i, i < m → ch i ≠ f)
    (hend : ch m = f) (h0 : ch 0 = tg) (hmM : m + 1 < 2147483648)
    (hV : V.length < 2147483647) (hO : O.length < 2147483647)
    (i0 : vbuf0.items = V.map Value.integer) (i1 : vbuf1.items = O.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32) (value1 : e1.denote (envOf caller) = some (f : Int))
    (value2 : e2.denote (envOf caller) = some (tg : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.TreePathInstance.tree_path.parameters
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2] = some Sinit ∧
      Proofs.TreePathInstance.tree_path.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2] = .finished (res,.scalar ((m + 1 : Nat) : Int)) ∧
      ScalarPostM (mvTP V0 V1 vsc0 vsc1 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01)
        caller Sinit res (e1.nodes + e2.nodes) (400 * m + 200) caller.scalars.memory (m + 1)
        (VC V (Ot ch O (m + 1))) := by
  have hfM : f < 2147483648 := by rw [← hend]; exact hlt m (le_refl _)
  have htM : tg < 2147483648 := by rw [← h0]; exact hlt 0 (by omega)
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_ta caller ok0 ok1 e1 e2 (f : Int) (tg : Int) hs1 hs2 ty1 ty2 value1 value2 (validN f hfM) (validN tg htM)
  have fwS := fwTP_init caller ok0 ok1 h01 V O hV hO i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cs,hrps⟩,hcost,hneed,hwk⟩ :=
    body_exec (mvTP V0 V1 vsc0 vsc1 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl V O ch (callerP caller) f tg m hm hlt hch hne
    hend h0 hfM htM hmM (m + 2) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(f : Int)⟩ : Cell),⟨i32,(tg : Int)⟩]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(f : Int)⟩ : Cell),⟨i32,(tg : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [ci f, ci tg] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hpost := call_vecm (mvTP V0 V1 vsc0 vsc1 m0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun k => decide (k = 1))
    (by intro k hk; have : k = 1 := by simpa using hk
        subst this; simp [mvTP])
    caller Proofs.TreePathInstance.tree_path
    [.vectorReference s0,.vectorReference s1,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(f : Int)⟩ : Cell),⟨i32,(tg : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqTP]; exact wr_bodyTP)
    (m + 2) rr (by rw [hmk, body_eqTP]; exact hexec) _ hret i32 rfl (validN (m + 1) hmM) (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes) (400 * m + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TreePathCall
