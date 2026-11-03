import Proofs.MatMulPrepare
import Proofs.FenwickTreeExec
import Proofs.MultiVecCall

namespace Proofs.FenwickTreeVecCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.FenwickTreeExec Proofs.FenwickMath Proofs.FenwickBuildMath
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

theorem prepare_ft (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1) :
    ∃ Sinit, prepare caller Proofs.FenwickTreeInstance.FenwickTree_long_long_new2.parameters
          [.vectorReference s0,.vectorReference s1] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1] ∧ Sinit.scalars.memory = callerP caller ∧
        Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,false,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 false ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => absurd h (by decide))
  have fs : (caller.charge 1 1).frame.state = caller.frame.state := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true)
    (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := m1) (vbuf := vbuf1) s64 false ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons, List.length_singleton] at b0 b1
  have hp : Proofs.FenwickTreeInstance.FenwickTree_long_long_new2.parameters = [.vector s64 true,.vector s64 false] := rfl
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1]
  simp [b0, b1, bindAll, bindOne, CppState.bindArgument, callerP, NState.observe, CppState.State.observe,
    NState.charge]


/-- The callee of the constructor: the flat vectors `tree` (writable) and `v` (`long long`). -/
def mvFT (V0 V1 vsc0 vsc1 : Nat) (m1 : Bool) (L0 T0 sc N : Nat) (h10 : V1 ≠ V0) : MV where
  nv := 2
  ty := fun _ => s64
  wV := fun k => decide (k = 0)
  flag := fun k => if k = 0 then true else m1
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by
    intro k hk
    have : k = 0 := by simpa using hk
    subst this
    simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 0 := by simpa using hw
    subst this
    have : j = 1 := by omega
    subst this
    simpa using h10

def bbFT (b0 b1 : Buffer Value) : Nat → Buffer Value := fun k => if k = 0 then b0 else b1

theorem body_eqFT : Proofs.FenwickTreeInstance.FenwickTree_long_long_new2.body = progN 2 := rfl

theorem wr_bodyFT : WrM (fun k => decide (k = 0)) (progN 2) = true := by decide

theorem cases2 (k : Nat) (hk : k < 2) : k = 0 ∨ k = 1 := by omega

theorem items_valid (b : Buffer Value) (L : List Int) (ty : Ty) (hit : b.items = L.map Value.integer)
    (hv : b.Valid (accepts (.integer ty))) : ∀ y ∈ L, ty.valid y = true := by
  intro y hy
  have h := hv.2.2
  rw [hit, List.all_eq_true] at h
  have := h (Value.integer y) (List.mem_map_of_mem hy)
  simpa [accepts] using this

/-- The frame facts at entry of the constructor body. -/
theorem fwFT_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h10 : V1 ≠ V0) (T0 V : List Int) (hT : T0.length < 2147483647) (hV : V.length < 2147483647)
    (i0 : vbuf0.items = T0.map Value.integer) (i1 : vbuf1.items = V.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvFT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10)
      (VFT T0 V) (bbFT vbuf0 vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,false,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFT] using ok0.vtag
    · simpa [mvFT] using ok1.vtag
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFT, bbFT] using ok0.vfound
    · simpa [mvFT, bbFT] using ok1.vfound
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFT] using ok0.flag
    · simpa [mvFT] using ok1.flag
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFT, bbFT, VFT] using i0
    · simpa [mvFT, bbFT, VFT] using i1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFT, bbFT] using bv0
    · simpa [mvFT, bbFT] using bv1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFT, bbFT] using l0
    · simpa [mvFT, bbFT] using l1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFT, bbFT] using o0
    · simpa [mvFT, bbFT] using o1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simp [VFT]; omega
    · simp [VFT]; omega

set_option maxHeartbeats 4000000 in
/-- `FenwickTree<long long>(v)` initialises the field `tree` (already `v.size() + 1` elements long by the standard
constructor) to the Fenwick tree of `v`. -/
theorem fenwick_tree_from_vector_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h10 : V1 ≠ V0) (T0 V : List Int) (n : Nat) (hn : n + 1 ≤ 1073741824) (hV : V.length = n) (hT : T0.length = n + 1)
    (hok : BOkT V (n + 1))
    (i0 : vbuf0.items = T0.map Value.integer) (i1 : vbuf1.items = V.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (X2 : List Int),
      prepare caller Proofs.FenwickTreeInstance.FenwickTree_long_long_new2.parameters
        [.vectorReference s0,.vectorReference s1] = some Sinit ∧
      Proofs.FenwickTreeInstance.FenwickTree_long_long_new2.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1] = .finished (res,Ret.unit) ∧
      FInv X2 V ∧
      ScalarPostM (mvFT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10)
        caller Sinit res 0 (560 * n + 200) caller.scalars.memory (2 * n) (VFT X2 V) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_ft caller ok0 ok1
  have fwS := fwFT_init caller ok0 ok1 h10 T0 V (by omega) (by omega) i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  have hVv := items_valid vbuf1 V s64 i1 bv1
  have hTv := items_valid vbuf0 T0 s64 i0 bv0
  obtain ⟨rr,X2,hexec,hret,hrps,hrvv,hfin,hcost,hneed,hwk⟩ :=
    body_exec (mvFT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10) rfl (by simp [mvFT]) (by simp [mvFT])
      (n + 1) (callerP caller) T0 V n hn hV hT hVv hTv hok (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm_unit (mvFT V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h10)
    (fun k => decide (k = 0))
    (by intro k hk; have : k = 0 := by simpa using hk
        subst this; simp [mvFT])
    caller Proofs.FenwickTreeInstance.FenwickTree_long_long_new2
    [.vectorReference s0,.vectorReference s1] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by simp [callerP]) ok0.base (by rw [body_eqFT]; exact wr_bodyFT)
    (n + 1) rr (by rw [hmk, body_eqFT]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) 0 (560 * n + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,X2,hprep,hrun,hfin,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.FenwickTreeVecCall
