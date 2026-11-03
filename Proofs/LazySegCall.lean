import Proofs.LazySegPrepare
import Proofs.LazySegUpdBody
import Proofs.LazySegGet
import Proofs.LazySegApplyPt
import Proofs.LazySegAll
import Proofs.LazySegCtorRep
import Proofs.MultiVecCallB

namespace Proofs.LazySegCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCallB
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (cs)
open Proofs.LazySegMath (Rep)
open Proofs.LazySegChmin (chminMon mi)
open Proofs.SegmentTreeExec (maxMon)
open Proofs.SegTreeMath (AllV rfold)

/-- The callee of the methods: the vectors `node` and `lazy` (both writable `long long` vectors). -/
def mvLZ (V0 V1 vsc0 vsc1 : Nat) (L0 T0 sc N : Nat) (h01 : V0 ≠ V1) : MV where
  nv := 2
  ty := fun _ => s64
  wV := fun _ => true
  flag := fun _ => true
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by intro k hk; rfl
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using h01
    · simpa using h01.symm

/-- The two vectors `node`, `lazy` as the model state. -/
def VZ (A Z : List Int) : Nat → List Int := fun k => if k = 0 then A else if k = 1 then Z else []

theorem cases2z (k : Nat) (hk : k < 2) : k = 0 ∨ k = 1 := by omega

theorem fwLZ_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (A Z : List Int) (hA : A.length < 2147483647) (hZ : Z.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = Z.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01)
      (VZ A Z) (fun k => if k = 0 then vbuf0 else vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2z k hk with rfl | rfl
    · simpa [mvLZ] using ok0.vtag
    · simpa [mvLZ] using ok1.vtag
  · intro k hk
    rcases cases2z k hk with rfl | rfl
    · simpa [mvLZ] using ok0.vfound
    · simpa [mvLZ] using ok1.vfound
  · intro k hk
    rcases cases2z k hk with rfl | rfl
    · simpa [mvLZ] using ok0.flag
    · simpa [mvLZ] using ok1.flag
  · intro k hk
    rcases cases2z k hk with rfl | rfl
    · simpa [mvLZ, VZ] using i0
    · simpa [mvLZ, VZ] using i1
  · intro k hk
    rcases cases2z k hk with rfl | rfl
    · simpa [mvLZ] using bv0
    · simpa [mvLZ] using bv1
  · intro k hk
    rcases cases2z k hk with rfl | rfl
    · simpa [mvLZ] using l0
    · simpa [mvLZ] using l1
  · intro k hk
    rcases cases2z k hk with rfl | rfl
    · simpa [mvLZ] using o0
    · simpa [mvLZ] using o1
  · intro k hk
    rcases cases2z k hk with rfl | rfl
    · simp [VZ]; omega
    · simp [VZ]; omega

theorem wr_bodySet : WrM (fun _ => true) (Proofs.LazySegSet.bodySet 2) = true := by decide
theorem wr_bodyGet : WrM (fun _ => true) (Proofs.LazySegGet.bodyGet 2) = true := by decide
theorem wr_bodyProd : WrM (fun _ => true) (Proofs.LazySegRange.bodyProd 2) = true := by decide
theorem wr_bodyAll : WrM (fun _ => true) (Proofs.LazySegAll.bodyAll 2) = true := by decide
theorem wr_bodyApplyPt : WrM (fun _ => true) (Proofs.LazySegApplyPt.bodyApplyPt 2) = true := by decide
theorem wr_bodyUpd : WrM (fun _ => true) (Proofs.LazySegUpdBody.bodyUpd 2) = true := by decide

/-- `hh30`-style facts: the node vector has `2 * N` entries, so `h ≤ 29`. -/
theorem h_le_29 (h : Nat) (hn : 2 * 2 ^ h < 2147483647) : h ≤ 29 := by
  apply Classical.byContradiction
  intro hc
  have h1 : 2 ^ 30 ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ 30 = 1073741824 := by norm_num
  omega

set_option maxHeartbeats 64000000 in
/-- `LazySegmentTree::set(idx, val)`: `A[idx] = val`. -/
theorem lazy_set_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (A node lz : List Int) (N h : Nat) (hN : N = 2 ^ h) (hR : Rep chminMon N A node lz)
    (hnode : node.length < 2147483647)
    (n idx : Nat) (val : Int) (hn : n < 2147483648) (hidx : idx < N) (hval : s64.valid val = true)
    (i0 : vbuf0.items = node.map Value.integer) (i1 : vbuf1.items = lz.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 e2 e3 e4 e5 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some ((2 ^ h : Nat) : Int)) (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (idx : Int)) (value5 : e5.denote (envOf caller) = some val) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_set.parameters
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] = some Sinit ∧
      Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_set.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] = .finished (res,Ret.unit) ∧
      ∃ vF : Nat → List Int, Rep chminMon N (A.set idx val) (vF 0) (vF 1) ∧
        ScalarPostMB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work
          (caller.scope + 1) caller.frame.state.storage.objects.length h01)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (2500 * h + 450) caller.scalars.memory (6 * h + 2) vF := by
  subst hN
  have hlen := hR.1
  have hh29 : h ≤ 29 := h_le_29 h (by omega)
  have hN30 : 2 ^ h ≤ 536870912 := by
    have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hh29
    have h29 : 2 ^ 29 = 536870912 := by norm_num
    omega
  have hlz : lz.length < 2147483647 := by rw [hR.2.1]; omega

  obtain ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.LazySegPrepare.prepare_set caller ok0 ok1 e1 e2 e3 e4 e5 ((n : Int)) (((2 ^ h : Nat) : Int)) ((h : Int)) ((idx : Int)) (val) hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 value1 value2 value3 value4 value5 (validN n hn) (validN (2 ^ h) (by omega)) (validN h (by omega)) (validN idx (by omega)) hval
  have fwS := fwLZ_init caller ok0 ok1 h01 node lz hnode hlz i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,vF,hexec,hret,hrvv,hRep,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.LazySegSet.body_execSet (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) (VZ node lz) n h idx val A (by omega) hn hidx hval (by simpa [VZ] using hR) (h + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]⟩ : PS) = gS (callerP caller) [ci n, ci (2 ^ h), ci h, ci idx, cs val] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  have gw5 := g5.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4 gw5
  have hpost := call_vecm_unitB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_set
    [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,val⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.LazySegSet.body_eqSet]; exact wr_bodySet)
    (h + 3) rr (by rw [hmk, Proofs.LazySegSet.body_eqSet]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (2500 * h + 450) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,vF,(by simpa using hRep),?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 64000000 in
/-- `LazySegmentTree::get(idx)`: `A[idx]`. -/
theorem lazy_get_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (A node lz : List Int) (N h : Nat) (hN : N = 2 ^ h) (hR : Rep chminMon N A node lz)
    (hnode : node.length < 2147483647)
    (n idx : Nat) (hn : n < 2147483648) (hidx : idx < N)
    (i0 : vbuf0.items = node.map Value.integer) (i1 : vbuf1.items = lz.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 e2 e3 e4 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some ((2 ^ h : Nat) : Int)) (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (idx : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_get.parameters
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4] = some Sinit ∧
      Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_get.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4] = .finished (res,.scalar (A.getD idx 0)) ∧
      ∃ vF : Nat → List Int, Rep chminMon N A (vF 0) (vF 1) ∧
        ScalarPostMB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work
          (caller.scope + 1) caller.frame.state.storage.objects.length h01)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes) (1500 * h + 250) caller.scalars.memory (5 * h) vF := by
  subst hN
  have hlen := hR.1
  have hh29 : h ≤ 29 := h_le_29 h (by omega)
  have hN30 : 2 ^ h ≤ 536870912 := by
    have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hh29
    have h29 : 2 ^ 29 = 536870912 := by norm_num
    omega
  have hlz : lz.length < 2147483647 := by rw [hR.2.1]; omega

  obtain ⟨t1,t2,t3,t4,g1,g2,g3,g4,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.LazySegPrepare.prepare_get caller ok0 ok1 e1 e2 e3 e4 ((n : Int)) (((2 ^ h : Nat) : Int)) ((h : Int)) ((idx : Int)) hs1 hs2 hs3 hs4 ty1 ty2 ty3 ty4 value1 value2 value3 value4 (validN n hn) (validN (2 ^ h) (by omega)) (validN h (by omega)) (validN idx (by omega))
  have fwS := fwLZ_init caller ok0 ok1 h01 node lz hnode hlz i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,vF,hexec,hret,hrvv,hRep,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.LazySegGet.body_execGet (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) (VZ node lz) n h idx A (by omega) hn hidx (by simpa [VZ] using hR) (h + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩]⟩ : PS) = gS (callerP caller) [ci n, ci (2 ^ h), ci h, ci idx] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4
  have hpost := call_vecmB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_get
    [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.LazySegGet.body_eqGet]; exact wr_bodyGet)
    (h + 3) rr (by rw [hmk, Proofs.LazySegGet.body_eqGet]; exact hexec) _ hret s64 rfl (Proofs.SegTreeMath.getD_V _ A hR.2.2.2.2.2.1 idx (by rw [hR.2.2.1]; exact hidx)) (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes) (1500 * h + 250) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,vF,(by simpa using hRep),?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 64000000 in
/-- `LazySegmentTree::product(l, r)`: the product (maximum) of `[l, r)`. -/
theorem lazy_product_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (A node lz : List Int) (N h : Nat) (hN : N = 2 ^ h) (hR : Rep chminMon N A node lz)
    (hnode : node.length < 2147483647)
    (n l r : Nat) (hn : n < 2147483648) (hlr : l ≤ r) (hrN : r ≤ N)
    (i0 : vbuf0.items = node.map Value.integer) (i1 : vbuf1.items = lz.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 e2 e3 e4 e5 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some ((2 ^ h : Nat) : Int)) (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (l : Int)) (value5 : e5.denote (envOf caller) = some (r : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product.parameters
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] = some Sinit ∧
      Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] = .finished (res,.scalar (rfold maxMon A l (r - l))) ∧
      ∃ vF : Nat → List Int, Rep chminMon N A (vF 0) (vF 1) ∧
        ScalarPostMB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work
          (caller.scope + 1) caller.frame.state.storage.objects.length h01)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (3400 * h + 1600 * (Nat.log2 (r - l) + 1) + 800) caller.scalars.memory (10 * h) vF := by
  subst hN
  have hlen := hR.1
  have hh29 : h ≤ 29 := h_le_29 h (by omega)
  have hN30 : 2 ^ h ≤ 536870912 := by
    have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hh29
    have h29 : 2 ^ 29 = 536870912 := by norm_num
    omega
  have hlz : lz.length < 2147483647 := by rw [hR.2.1]; omega

  obtain ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.LazySegPrepare.prepare_prod caller ok0 ok1 e1 e2 e3 e4 e5 ((n : Int)) (((2 ^ h : Nat) : Int)) ((h : Int)) ((l : Int)) ((r : Int)) hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 value1 value2 value3 value4 value5 (validN n hn) (validN (2 ^ h) (by omega)) (validN h (by omega)) (validN l (by omega)) (validN r (by omega))
  have fwS := fwLZ_init caller ok0 ok1 h01 node lz hnode hlz i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,vF,hexec,hret,hrvv,hRep,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.LazySegRange.body_execProd (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) (VZ node lz) n h l r A hh29 hn hlr hrN (by simpa [VZ] using hR) (h + Nat.log2 (r - l) + 8) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l : Int)⟩,⟨i32,(r : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l : Int)⟩,⟨i32,(r : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]⟩ : PS) = gS (callerP caller) [ci n, ci (2 ^ h), ci h, ci l, ci r] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  have gw5 := g5.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4 gw5
  have hpost := call_vecmB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product
    [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l : Int)⟩,⟨i32,(r : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.LazySegRange.body_eqProd]; exact wr_bodyProd)
    (h + Nat.log2 (r - l) + 8) rr (by rw [hmk, Proofs.LazySegRange.body_eqProd]; exact hexec) _ hret s64 rfl (Proofs.SegTreeMath.rfold_V maxMon A hR.2.2.2.2.2.1 (r - l) l (by rw [hR.2.2.1]; omega)) (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (3400 * h + 1600 * (Nat.log2 (r - l) + 1) + 800) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,vF,(by simpa using hRep),?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 64000000 in
/-- `LazySegmentTree::product_all()`: the product (maximum) of all elements. -/
theorem lazy_product_all_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (A node lz : List Int) (N h : Nat) (hN : N = 2 ^ h) (hR : Rep chminMon N A node lz)
    (hnode : node.length < 2147483647)
    (n : Nat) (hn : n < 2147483648) (hh1 : 1 ≤ h)
    (i0 : vbuf0.items = node.map Value.integer) (i1 : vbuf1.items = lz.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 e2 e3 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some ((2 ^ h : Nat) : Int)) (value3 : e3.denote (envOf caller) = some (h : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product_all.parameters
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3] = some Sinit ∧
      Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product_all.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3] = .finished (res,.scalar (rfold maxMon A 0 N)) ∧
      ∃ vF : Nat → List Int, Rep chminMon N A (vF 0) (vF 1) ∧
        ScalarPostMB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work
          (caller.scope + 1) caller.frame.state.storage.objects.length h01)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes) (100) caller.scalars.memory (0) vF := by
  subst hN
  have hlen := hR.1
  have hh29 : h ≤ 29 := h_le_29 h (by omega)
  have hN30 : 2 ^ h ≤ 536870912 := by
    have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hh29
    have h29 : 2 ^ 29 = 536870912 := by norm_num
    omega
  have hlz : lz.length < 2147483647 := by rw [hR.2.1]; omega

  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.LazySegPrepare.prepare_all caller ok0 ok1 e1 e2 e3 ((n : Int)) (((2 ^ h : Nat) : Int)) ((h : Int)) hs1 hs2 hs3 ty1 ty2 ty3 value1 value2 value3 (validN n hn) (validN (2 ^ h) (by omega)) (validN h (by omega))
  have fwS := fwLZ_init caller ok0 ok1 h01 node lz hnode hlz i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.LazySegAll.body_execAll (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl (callerP caller) (VZ node lz) n h A hh1 (by simpa [VZ] using hR) 2
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩ : PS) = gS (callerP caller) [ci n, ci (2 ^ h), ci h] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3
  have hpost := call_vecmB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_product_all
    [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.LazySegAll.body_eqAll]; exact wr_bodyAll)
    (2) rr (by rw [hmk, Proofs.LazySegAll.body_eqAll]; exact hexec) _ hret s64 rfl (Proofs.SegTreeMath.rfold_V maxMon A hR.2.2.2.2.2.1 (2 ^ h) 0 (by rw [hR.2.2.1]; omega)) (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes) (100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,VZ node lz,(by simpa [VZ] using hR),?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 64000000 in
/-- `LazySegmentTree::update(idx, f)`: `A[idx] = mapping(f, A[idx])`. -/
theorem lazy_apply_point_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (A node lz : List Int) (N h : Nat) (hN : N = 2 ^ h) (hR : Rep chminMon N A node lz)
    (hnode : node.length < 2147483647)
    (n idx : Nat) (f : Int) (hn : n < 2147483648) (hidx : idx < N) (hf : s64.valid f = true)
    (i0 : vbuf0.items = node.map Value.integer) (i1 : vbuf1.items = lz.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 e2 e3 e4 e5 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = s64)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some ((2 ^ h : Nat) : Int)) (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (idx : Int)) (value5 : e5.denote (envOf caller) = some f) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_2.parameters
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] = some Sinit ∧
      Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_2.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] = .finished (res,Ret.unit) ∧
      ∃ vF : Nat → List Int, Rep chminMon N (A.set idx (mi f (A.getD idx 0))) (vF 0) (vF 1) ∧
        ScalarPostMB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work
          (caller.scope + 1) caller.frame.state.storage.objects.length h01)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (2500 * h + 450) caller.scalars.memory (6 * h + 2) vF := by
  subst hN
  have hlen := hR.1
  have hh29 : h ≤ 29 := h_le_29 h (by omega)
  have hN30 : 2 ^ h ≤ 536870912 := by
    have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hh29
    have h29 : 2 ^ 29 = 536870912 := by norm_num
    omega
  have hlz : lz.length < 2147483647 := by rw [hR.2.1]; omega

  obtain ⟨t1,t2,t3,t4,t5,g1,g2,g3,g4,g5,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.LazySegPrepare.prepare_ap caller ok0 ok1 e1 e2 e3 e4 e5 ((n : Int)) (((2 ^ h : Nat) : Int)) ((h : Int)) ((idx : Int)) (f) hs1 hs2 hs3 hs4 hs5 ty1 ty2 ty3 ty4 ty5 value1 value2 value3 value4 value5 (validN n hn) (validN (2 ^ h) (by omega)) (validN h (by omega)) (validN idx (by omega)) hf
  have fwS := fwLZ_init caller ok0 ok1 h01 node lz hnode hlz i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,vF,hexec,hret,hrvv,hRep,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.LazySegApplyPt.body_execApplyPt (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) (VZ node lz) n h idx f A (by omega) hn hidx hf (by simpa [VZ] using hR) (h + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,f⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,f⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]⟩ : PS) = gS (callerP caller) [ci n, ci (2 ^ h), ci h, ci idx, cs f] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  have gw5 := g5.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4 gw5
  have hpost := call_vecm_unitB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_2
    [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(idx : Int)⟩,⟨s64,f⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.LazySegApplyPt.body_eqApplyPt]; exact wr_bodyApplyPt)
    (h + 3) rr (by rw [hmk, Proofs.LazySegApplyPt.body_eqApplyPt]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes) (2500 * h + 450) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,vF,(by simpa using hRep),?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 64000000 in
/-- `LazySegmentTree::update(l, r, f)`: `A[i] = mapping(f, A[i])` for `l ≤ i < r`. -/
theorem lazy_apply_range_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (A node lz : List Int) (N h : Nat) (hN : N = 2 ^ h) (hR : Rep chminMon N A node lz)
    (hnode : node.length < 2147483647)
    (n l r : Nat) (f : Int) (hn : n < 2147483648) (hlr : l ≤ r) (hrN : r ≤ N) (hf : s64.valid f = true)
    (i0 : vbuf0.items = node.map Value.integer) (i1 : vbuf1.items = lz.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 e2 e3 e4 e5 e6 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true) (hs5 : e5.scalarOnly = true) (hs6 : e6.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32) (ty4 : e4.resultType = i32) (ty5 : e5.resultType = i32) (ty6 : e6.resultType = s64)
    (value1 : e1.denote (envOf caller) = some (n : Int)) (value2 : e2.denote (envOf caller) = some ((2 ^ h : Nat) : Int)) (value3 : e3.denote (envOf caller) = some (h : Int)) (value4 : e4.denote (envOf caller) = some (l : Int)) (value5 : e5.denote (envOf caller) = some (r : Int)) (value6 : e6.denote (envOf caller) = some f) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_3.parameters
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5,.value e6] = some Sinit ∧
      Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_3.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5,.value e6] = .finished (res,Ret.unit) ∧
      ∃ vF : Nat → List Int, Rep chminMon N (Proofs.LazySegApplyGlue.chminRange A l r f) (vF 0) (vF 1) ∧
        ScalarPostMB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work
          (caller.scope + 1) caller.frame.state.storage.objects.length h01)
          caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes + e6.nodes) (7000 * h + 3100 * (Nat.log2 (r - l) + 1) + 1100) caller.scalars.memory (12 * h + 4 * (Nat.log2 (r - l) + 1)) vF := by
  subst hN
  have hlen := hR.1
  have hh29 : h ≤ 29 := h_le_29 h (by omega)
  have hN30 : 2 ^ h ≤ 536870912 := by
    have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) hh29
    have h29 : 2 ^ 29 = 536870912 := by norm_num
    omega
  have hlz : lz.length < 2147483647 := by rw [hR.2.1]; omega

  obtain ⟨t1,t2,t3,t4,t5,t6,g1,g2,g3,g4,g5,g6,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.LazySegPrepare.prepare_ar caller ok0 ok1 e1 e2 e3 e4 e5 e6 ((n : Int)) (((2 ^ h : Nat) : Int)) ((h : Int)) ((l : Int)) ((r : Int)) (f) hs1 hs2 hs3 hs4 hs5 hs6 ty1 ty2 ty3 ty4 ty5 ty6 value1 value2 value3 value4 value5 value6 (validN n hn) (validN (2 ^ h) (by omega)) (validN h (by omega)) (validN l (by omega)) (validN r (by omega)) hf
  have fwS := fwLZ_init caller ok0 ok1 h01 node lz hnode hlz i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,vF,hexec,hret,hrvv,hRep,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    Proofs.LazySegUpdBody.body_execUpd (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) (VZ node lz) n h l r f A hh29 hn hlr hrN hf (by simpa [VZ] using hR) (h + Nat.log2 (r - l) + 8) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l : Int)⟩,⟨i32,(r : Int)⟩,⟨s64,f⟩]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l : Int)⟩,⟨i32,(r : Int)⟩,⟨s64,f⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩,⟨(callerP caller).length+5,true⟩]⟩ : PS) = gS (callerP caller) [ci n, ci (2 ^ h), ci h, ci l, ci r, cs f] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  have gw4 := g4.2.2.1
  have gw5 := g5.2.2.1
  have gw6 := g6.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3 gw4 gw5 gw6
  have hpost := call_vecm_unitB 1000 (mvLZ V0 V1 vsc0 vsc1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun _ => true) (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_update_3
    [.vectorReference s0,.vectorReference s1,.value e1,.value e2,.value e3,.value e4,.value e5,.value e6] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),⟨i32,((2 ^ h : Nat) : Int)⟩,⟨i32,(h : Int)⟩,⟨i32,(l : Int)⟩,⟨i32,(r : Int)⟩,⟨s64,f⟩])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩,⟨(callerP caller).length+4,true⟩,⟨(callerP caller).length+5,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.LazySegUpdBody.body_eqUpd]; exact wr_bodyUpd)
    (h + Nat.log2 (r - l) + 8) rr (by rw [hmk, Proofs.LazySegUpdBody.body_eqUpd]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes + e5.nodes + e6.nodes) (7000 * h + 3100 * (Nat.log2 (r - l) + 1) + 1100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,vF,(by simpa using hRep),?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)


/-- The callee of the constructor: `node`, `lazy` (writable) and the input `v` (read-only), all `long long` vectors. -/
def mvLC (V0 V1 V2 vsc0 vsc1 vsc2 : Nat) (m2 : Bool) (L0 T0 sc N : Nat) (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2) : MV where
  nv := 3
  ty := fun _ => s64
  wV := fun k => decide (k < 2)
  flag := fun k => if k < 2 then true else m2
  R := fun k => if k = 0 then V0 else if k = 1 then V1 else V2
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else vsc2
  perm := by
    intro k hk
    have : k < 2 := by simpa using hk
    simp [this]
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have hk2 : k < 2 := by simpa using hw
    have : (j = 1 ∧ k = 0) ∨ (j = 2 ∧ k = 0) ∨ (j = 0 ∧ k = 1) ∨ (j = 2 ∧ k = 1) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using h01.symm
    · simpa using h02.symm
    · simpa using h01
    · simpa using h12.symm

theorem wr_bodyCtor : WrM (fun k => decide (k < 2)) (Proofs.LazySegCtor.bodyCtor 3) = true := by decide

theorem cases3c (k : Nat) (hk : k < 3) : k = 0 ∨ k = 1 ∨ k = 2 := by omega

theorem fwLC_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m2 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2)
    (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2) (A Z B : List Int) (hA : A.length < 2147483647)
    (hZ : Z.length < 2147483647) (hB : B.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = Z.map Value.integer) (i2 : vbuf2.items = B.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (bv2 : vbuf2.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) :
    FWM (mvLC V0 V1 V2 vsc0 vsc1 vsc2 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12)
      (Proofs.LazySegCtor.VC Z A B) (fun k => if k = 0 then vbuf0 else if k = 1 then vbuf1 else vbuf2) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,true,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩,⟨V2,.integer s64,false,.root vsc2⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases3c k hk with rfl | rfl | rfl
    · simpa [mvLC] using ok0.vtag
    · simpa [mvLC] using ok1.vtag
    · simpa [mvLC] using ok2.vtag
  · intro k hk
    rcases cases3c k hk with rfl | rfl | rfl
    · simpa [mvLC] using ok0.vfound
    · simpa [mvLC] using ok1.vfound
    · simpa [mvLC] using ok2.vfound
  · intro k hk
    rcases cases3c k hk with rfl | rfl | rfl
    · simpa [mvLC] using ok0.flag
    · simpa [mvLC] using ok1.flag
    · simpa [mvLC] using ok2.flag
  · intro k hk
    rcases cases3c k hk with rfl | rfl | rfl
    · simpa [mvLC, Proofs.LazySegCtor.VC] using i0
    · simpa [mvLC, Proofs.LazySegCtor.VC] using i1
    · simpa [mvLC, Proofs.LazySegCtor.VC] using i2
  · intro k hk
    rcases cases3c k hk with rfl | rfl | rfl
    · simpa [mvLC] using bv0
    · simpa [mvLC] using bv1
    · simpa [mvLC] using bv2
  · intro k hk
    rcases cases3c k hk with rfl | rfl | rfl
    · simpa [mvLC] using l0
    · simpa [mvLC] using l1
    · simpa [mvLC] using l2
  · intro k hk
    rcases cases3c k hk with rfl | rfl | rfl
    · simpa [mvLC] using o0
    · simpa [mvLC] using o1
    · simpa [mvLC] using o2
  · intro k hk
    rcases cases3c k hk with rfl | rfl | rfl
    · simp [Proofs.LazySegCtor.VC]; omega
    · simp [Proofs.LazySegCtor.VC]; omega
    · simp [Proofs.LazySegCtor.VC]; omega

open Proofs.LazySegCtor (szv EMIN)

set_option maxHeartbeats 64000000 in
/-- The constructor `LazySegmentTree(const vector<T>& v)` builds the tree in `node` (the vector `lazy` keeps its `id()` entries). -/
theorem lazy_ctor_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m2 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2)
    (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2) (Vin : List Int) (n : Nat) (hnv1 : Vin.length = n) (hn1 : 1 ≤ n)
    (hn29 : n ≤ 536870912) (hVin : AllV maxMon Vin) (k : Nat) (hk1 : n ≤ szv k) (hk2 : ∀ j, j < k → szv j < n)
    (i0 : vbuf0.items = (List.replicate (2 * szv k) EMIN).map Value.integer)
    (i1 : vbuf1.items = (List.replicate (szv k) 9223372036854775807).map Value.integer)
    (i2 : vbuf2.items = Vin.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (bv2 : vbuf2.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_new0.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2] = some Sinit ∧
      Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_new0.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, Rep chminMon (szv k) (Vin ++ List.replicate (szv k - n) EMIN) Vf
          (List.replicate (szv k) 9223372036854775807) ∧
        ScalarPostMB 1000 (mvLC V0 V1 V2 vsc0 vsc1 vsc2 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
          (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12)
          caller Sinit res 0 (3000 * (2 ^ k + 1) + 3300) caller.scalars.memory (2 ^ k + n)
          (Proofs.LazySegCtor.VC (List.replicate (szv k) 9223372036854775807) Vf Vin) := by
  have h29 : 2 ^ 29 = 536870912 := by norm_num
  have hk29 : k ≤ 29 := by
    apply Classical.byContradiction
    intro hh
    have := hk2 29 (by omega)
    have h2 : szv 29 = 536870912 := by unfold szv; rw [if_neg (by omega), h29]
    omega
  have hN29 : szv k ≤ 536870912 := by
    unfold szv; split
    · omega
    · rw [← h29]; exact Nat.pow_le_pow_right (by decide) hk29
  have hnodeLen : (List.replicate (2 * szv k) EMIN).length < 2147483647 := by simp; omega
  have hlzLen : (List.replicate (szv k) (9223372036854775807 : Int)).length < 2147483647 := by simp; omega
  have hVinLen : Vin.length < 2147483647 := by omega
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    Proofs.LazySegPrepare.prepare_ctor caller ok0 ok1 ok2
  have fwS := fwLC_init caller ok0 ok1 ok2 h01 h02 h12 _ _ Vin hnodeLen hlzLen hVinLen i0 i1 i2 bv0 bv1 bv2 l0 l1 l2 o0 o1 o2
  rw [← sFrame] at fwS
  have hp2k : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hTf,hVf,hlenf,hleafc,hleafe,hcost,hneed,hwk⟩ :=
    Proofs.LazySegCtor.body_execCtor (mvLC V0 V1 V2 vsc0 vsc1 vsc2 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12) rfl rfl rfl (callerP caller) Vin n hnv1 hn1 hn29 hVin k hk1 hk2
    (40 + n + 2 ^ k) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left
  have hch : (((caller.charge 1 1).charge 1 1).charge 1 1).scalars.work = caller.scalars.work + 3 := by
    simp [NState.charge, NState.observe, CppState.State.observe]
  have hpost := call_vecm_unitB 1000 (mvLC V0 V1 V2 vsc0 vsc1 vsc2 m2 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12)
    (fun k => decide (k < 2))
    (by intro k hk; have : k < 2 := by simpa using hk
        simp [mvLC, this])
    caller Proofs.LazySegTreeInstance.LazySegmentTree_cp__LazyChminMax_long_long__long_long_long_long_new0
    [.vectorReference s0,.vectorReference s1,.vectorReference s2] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by rw [takeM]) ok0.base (by rw [Proofs.LazySegCtor.body_eqCtor]; exact wr_bodyCtor)
    (40 + n + 2 ^ k) rr (by rw [hmk, Proofs.LazySegCtor.body_eqCtor]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    0 (3000 * (2 ^ k + 1) + 3300) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have hNpos : 0 < szv k := Nat.lt_of_lt_of_le (by omega) hk1
  have hRep := Proofs.LazySegCtorRep.rep_ctor n (szv k) Vin Vf hNpos hk1 hnv1 hVin hTf hVf hlenf hleafc hleafe
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hRep,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    exact List.take_left
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.LazySegCall
