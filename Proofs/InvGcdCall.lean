import Proofs.InvGcdPrepare
import Proofs.InvGcdExec
import Proofs.MultiVecCall

namespace Proofs.InvGcdCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.InvGcdPrepare Proofs.InvGcdExec
open Proofs.InvGcdExec (VO)
open Proofs.BellmanFordExec (cs)
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `inv_gcd`: one writable `long long` vector. -/
def mvIG (V0 vsc0 : Nat) (L0 T0 sc N : Nat) : MV where
  nv := 1
  ty := fun _ => s64
  wV := fun _ => true
  flag := fun _ => true
  R := fun _ => V0
  vsc := fun _ => vsc0
  perm := by intro k hk; rfl
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; exact absurd hjk (by simp at hj hk; omega)

theorem wr_bodyIG : WrM (fun _ => true) (bodyIG 1) = true := by decide

theorem fwIG_init (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (O : List Int) (hO : O.length < 2147483647)
    (i0 : vbuf0.items = O.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0) :
    FWM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (VO O) (fun _ => vbuf0) 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    have : k = 0 := by simp [mvIG] at hk; omega
    subst this
    simpa [mvIG] using ok0.vtag
  · intro k hk
    have : k = 0 := by simp [mvIG] at hk; omega
    subst this
    simpa [mvIG] using ok0.vfound
  · intro k hk
    have : k = 0 := by simp [mvIG] at hk; omega
    subst this
    simpa [mvIG] using ok0.flag
  · intro k hk
    have : k = 0 := by simp [mvIG] at hk; omega
    subst this
    simpa [mvIG, VO] using i0
  · intro k hk
    have : k = 0 := by simp [mvIG] at hk; omega
    subst this
    simpa [mvIG] using bv0
  · intro k hk
    have : k = 0 := by simp [mvIG] at hk; omega
    subst this
    simpa [mvIG] using l0
  · intro k hk
    have : k = 0 := by simp [mvIG] at hk; omega
    subst this
    simpa [mvIG] using o0
  · intro k hk
    have : k = 0 := by simp [mvIG] at hk; omega
    subst this
    simp [VO]; omega

set_option maxHeartbeats 8000000 in
/-- `cp::inv_gcd(out, a, b)` writes `g = gcd(a mod b, b)` to `out[0]` and `x` with `0 <= x < b / g`, `x * a == g (mod b)` to `out[1]`. -/
theorem inv_gcd_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (O : List Int) (a0 : Int) (b : Nat) (hb : 0 < b)
    (hb63 : b < 9223372036854775808) (va : s64.valid a0 = true) (hO2 : 2 ≤ O.length) (hO : O.length < 2147483647)
    (i0 : vbuf0.items = O.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = s64)
    (ty2 : e2.resultType = s64) (value1 : e1.denote (envOf caller) = some a0)
    (value2 : e2.denote (envOf caller) = some (b : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.InvGcdInstance.inv_gcd.parameters [.vectorReference s0,.value e1,.value e2] = some Sinit ∧
      Proofs.InvGcdInstance.inv_gcd.callFuel fuel caller [.vectorReference s0,.value e1,.value e2] = .finished (res,Ret.unit) ∧
      ∃ (an sF : Nat) (xF : Int), (an : Int) = a0 % (b : Int) ∧ an < b ∧ sF = Nat.gcd b an ∧ 0 ≤ xF ∧
        xF < ((b / sF : Nat) : Int) ∧ (b : Int) ∣ xF * (an : Int) - (sF : Int) ∧
        ScalarPostM (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
          caller.frame.state.storage.objects.length)
          caller Sinit res (e1.nodes + e2.nodes) (1040 * Nat.log2 b + 900) caller.scalars.memory 2
          (VO ((O.set 0 (sF : Int)).set 1 xF)) := by
  have vb : s64.valid (b : Int) = true := Proofs.InvGcdExec.v64 _ (by rw [Int.natAbs_natCast]; omega)
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_ta caller ok0 e1 e2 a0 (b : Int) hs1 hs2 ty1 ty2 value1 value2 va vb
  have fwS := fwIG_init caller ok0 O hO i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,an,sF,xF,han,hanb,hg,hx0,hx1,hx2,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.InvGcdExec.body_exec (mvIG V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl O (callerP caller) a0 b hb hb63 va hO2
    (2 * Nat.log2 b + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨s64,a0⟩ : Cell),⟨s64,(b : Int)⟩]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨s64,a0⟩ : Cell),⟨s64,(b : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [cs a0, cs b] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hpost := call_vecm_unit (mvIG V0 vsc0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.InvGcdInstance.inv_gcd
    [.vectorReference s0,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨s64,a0⟩ : Cell),⟨s64,(b : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqIG]; exact wr_bodyIG)
    (2 * Nat.log2 b + 3) rr (by rw [hmk, body_eqIG]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes) (1040 * Nat.log2 b + 900) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,an,sF,xF,han,hanb,hg,hx0,hx1,hx2,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.InvGcdCall
