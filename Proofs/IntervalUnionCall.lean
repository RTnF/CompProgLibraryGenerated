import Proofs.IntervalUnionExec
import Proofs.CompressPrepare

namespace Proofs.IntervalUnionCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.IntervalUnionMath Proofs.IntervalUnionExec

theorem prepare_iu4 (caller : NState) (prog : NProgram)
    (hp : prog.parameters = [.vector s64 true,.vector s64 true,.vector s64 true,.vector s64 true])
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3) :
    ∃ Sinit, prepare caller prog.parameters
          [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.vector 2,.vector 3] ∧ Sinit.scalars.memory = callerP caller ∧
        Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩,⟨V2,.integer s64,true,.root vsc2⟩,
           ⟨V3,.integer s64,true,.root vsc3⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work + 9 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => rfl)
  have rv2 := resolve_vref ((caller.charge 1 1).charge 1 1) s64 true ok2.slot ok2.binding ok2.valid ok2.vtag ok2.vfound
    ok2.lengths ok2.flag ok2.perm (fun h => rfl)
  have rv3 := resolve_vref (((caller.charge 1 1).charge 1 1).charge 1 1) s64 true ok3.slot ok3.binding ok3.valid ok3.vtag
    ok3.vfound ok3.lengths ok3.flag ok3.perm (fun h => rfl)
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true)
    (vbuf := vbuf0) s64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  have b2 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩,
    ⟨V1,.integer s64,true,.root vsc1⟩]⟩ : Frame)
    (V := V2) (vsc := vsc2) (m := true) (vbuf := vbuf2) s64 true ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
  have b3 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,true,.root vsc0⟩,
    ⟨V1,.integer s64,true,.root vsc1⟩,⟨V2,.integer s64,true,.root vsc2⟩]⟩ : Frame)
    (V := V3) (vsc := vsc3) (m := true) (vbuf := vbuf3) s64 true ok3.valid ok3.vtag ok3.vfound ok3.lengths ok3.flag ok3.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons, List.length_singleton] at b0 b1 b2 b3
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, rv2, rv3]
  simp [b0, b1, b2, b3, bindAll, bindOne, CppState.bindArgument, callerP, NState.observe, CppState.State.observe]
  constructor
  · simp [NState.charge, NState.observe, CppState.State.observe]
  · simp [NState.charge, NState.observe, CppState.State.observe]

theorem cases4 (k : Nat) (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

/-- The callee of `interval_union_inclusive`: four writable `long long` vectors. -/
def mvIU (V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 : Nat) (L0 T0 sc N : Nat)
    (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h03 : V0 ≠ V3) (h12 : V1 ≠ V2) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) : MV where
  nv := 4
  ty := fun _ => s64
  wV := fun _ => true
  flag := fun _ => true
  R := fun k => if k = 0 then V0 else if k = 1 then V1 else if k = 2 then V2 else V3
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else if k = 2 then vsc2 else vsc3
  perm := by intro k hk; rfl
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    rcases cases4 j hj with rfl | rfl | rfl | rfl <;> rcases cases4 k hk with rfl | rfl | rfl | rfl <;>
      (show _ ≠ _; split_ifs <;> first | omega | simp_all)

def bbIU (b0 b1 b2 b3 : Buffer Value) : Nat → Buffer Value := fun k =>
  if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else b3

theorem fwIU_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3)
    (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h03 : V0 ≠ V3) (h12 : V1 ≠ V2) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3)
    (X0 X1 X2 X3 : List Int) (n : Nat) (hn : n < 2147483647) (l0 : X0.length = n) (l1 : X1.length = n)
    (l2 : X2.length < 2147483648) (l3 : X3.length < 2147483648)
    (i0 : vbuf0.items = X0.map Value.integer) (i1 : vbuf1.items = X1.map Value.integer)
    (i2 : vbuf2.items = X2.map Value.integer) (i3 : vbuf3.items = X3.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (bv2 : vbuf2.Valid (accepts (.integer s64))) (bv3 : vbuf3.Valid (accepts (.integer s64)))
    (lm0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (lm1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (lm2 : vbuf2.limit = CppVectorBindings.sizeLimit s64) (lm3 : vbuf3.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) :
    FWM (mvIU V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length h01 h02 h03 h12 h13 h23)
      (V4 X0 X1 X2 X3) (bbIU vbuf0 vbuf1 vbuf2 vbuf3) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩,⟨V2,.integer s64,true,.root vsc2⟩,
         ⟨V3,.integer s64,true,.root vsc3⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvIU] using ok0.vtag
    · simpa [mvIU] using ok1.vtag
    · simpa [mvIU] using ok2.vtag
    · simpa [mvIU] using ok3.vtag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvIU, bbIU] using ok0.vfound
    · simpa [mvIU, bbIU] using ok1.vfound
    · simpa [mvIU, bbIU] using ok2.vfound
    · simpa [mvIU, bbIU] using ok3.vfound
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvIU] using ok0.flag
    · simpa [mvIU] using ok1.flag
    · simpa [mvIU] using ok2.flag
    · simpa [mvIU] using ok3.flag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvIU, bbIU, V4] using i0
    · simpa [mvIU, bbIU, V4] using i1
    · simpa [mvIU, bbIU, V4] using i2
    · simpa [mvIU, bbIU, V4] using i3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvIU, bbIU] using bv0
    · simpa [mvIU, bbIU] using bv1
    · simpa [mvIU, bbIU] using bv2
    · simpa [mvIU, bbIU] using bv3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvIU, bbIU] using lm0
    · simpa [mvIU, bbIU] using lm1
    · simpa [mvIU, bbIU] using lm2
    · simpa [mvIU, bbIU] using lm3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvIU, bbIU] using o0
    · simpa [mvIU, bbIU] using o1
    · simpa [mvIU, bbIU] using o2
    · simpa [mvIU, bbIU] using o3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simp [V4]; omega
    · simp [V4]; omega
    · simp [V4]; omega
    · simp [V4]; omega

theorem Cov_perm {S T : List (Int × Int)} (h : S.Perm T) (x : Int) : Cov S x ↔ Cov T x := by
  unfold Cov
  constructor
  · rintro ⟨p, hp, h2⟩; exact ⟨p, h.subset hp, h2⟩
  · rintro ⟨p, hp, h2⟩; exact ⟨p, h.symm.subset hp, h2⟩

theorem wr_bodyIU : WrM (fun _ => true) (progIU 4) = true := by decide

set_option maxHeartbeats 4000000 in
/-- `cp::interval_union_inclusive(l, r, ret_l, ret_r)` sorts the pairs `(l[i], r[i])` lexicographically in place, writes the
union of the closed intervals `[l[i], r[i]]` to the front of `ret_l`, `ret_r` and returns the number of its intervals. -/
theorem interval_union_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3)
    (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h03 : V0 ≠ V3) (h12 : V1 ≠ V2) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3)
    (L R RL RR : List Int) (n : Nat) (hn : n < 2147483647) (hlL : L.length = n) (hlR : R.length = n)
    (hRL : n ≤ RL.length) (hRR : n ≤ RR.length) (hRL' : RL.length < 2147483648) (hRR' : RR.length < 2147483648)
    (hvL : ∀ x ∈ L, s64.valid x = true) (hvR : ∀ x ∈ R, s64.valid x = true)
    (hle : ∀ i (h : i < n), L[i]'(by omega) ≤ R[i]'(by omega))
    (i0 : vbuf0.items = L.map Value.integer) (i1 : vbuf1.items = R.map Value.integer)
    (i2 : vbuf2.items = RL.map Value.integer) (i3 : vbuf3.items = RR.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (bv2 : vbuf2.Valid (accepts (.integer s64))) (bv3 : vbuf3.Valid (accepts (.integer s64)))
    (lm0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (lm1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (lm2 : vbuf2.limit = CppVectorBindings.sizeLimit s64) (lm3 : vbuf3.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (S' M : List (Int × Int)),
      prepare caller Proofs.IntervalUnionInstance.interval_union_inclusive_std_vector_long_long.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3] = some Sinit ∧
      Proofs.IntervalUnionInstance.interval_union_inclusive_std_vector_long_long.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3] = .finished (res,.scalar (M.length : Int)) ∧
      Sorted S' ∧ S'.Perm (L.zip R) ∧ Good M ∧ M.length ≤ n ∧ (∀ x, Cov M x ↔ Cov (L.zip R) x) ∧
      ScalarPostM (mvIU V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h03 h12 h13 h23)
        caller Sinit res 0 ((410 * n + 120) * n + 420 * n + 140) caller.scalars.memory (4 * n * n + 2 * n) (PW S' M RL RR) := by
  have hzl : (L.zip R).length = n := by simp [hlL, hlR]
  have hvalid : ∀ p ∈ L.zip R, s64.valid p.1 = true ∧ s64.valid p.2 = true := by
    intro p hp
    exact ⟨hvL _ (List.of_mem_zip hp).1, hvR _ (List.of_mem_zip hp).2⟩
  have hleZ : ∀ p ∈ L.zip R, p.1 ≤ p.2 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    simp only [List.getElem_zip]
    exact hle i (by omega)
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_iu4 caller Proofs.IntervalUnionInstance.interval_union_inclusive_std_vector_long_long rfl ok0 ok1 ok2 ok3
  have fwS := fwIU_init caller ok0 ok1 ok2 ok3 h01 h02 h03 h12 h13 h23 L R RL RR n hn hlL hlR hRL' hRR' i0 i1 i2 i3 bv0 bv1 bv2 bv3
    lm0 lm1 lm2 lm3 o0 o1 o2 o3
  rw [← sFrame] at fwS
  obtain ⟨rr,S',M,hexec,hret,hrps,hrvv,hS's,hS'p,hMI,hMl,hMv,hcost,hneed,hwk⟩ :=
    prog_exec (mvIU V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h03 h12 h13 h23) rfl rfl rfl rfl rfl L R RL RR n hlL hlR
      hvalid hleZ hRL hRR (callerP caller) hn (3 * n + 5) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm (mvIU V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h03 h12 h13 h23) (fun _ => true)
    (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.IntervalUnionInstance.interval_union_inclusive_std_vector_long_long
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3] Sinit
    (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by rw [takeM]) ok0.base (by rw [body_eqIU]; exact wr_bodyIU) (3 * n + 5) rr
    (by rw [hmk, body_eqIU]; exact hexec) (M.length : Int) hret i32 rfl (validN _ (by omega))
    (by omega) (by simp) 0 ((410 * n + 120) * n + 420 * n + 140) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,S',M,hprep,hrun,hS's,hS'p,hMI.good,hMl,?_,?_⟩
  · intro x
    exact (hMI.cov x).trans (Cov_perm hS'p x)
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.IntervalUnionCall
