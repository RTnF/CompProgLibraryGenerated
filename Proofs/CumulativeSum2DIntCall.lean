import Proofs.CumulativeSum2DIntExec
import Proofs.Vector2dSumCall
import Proofs.FenwickRangeCall

namespace Proofs.CumulativeSum2DIntCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.MultiVecCallN
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.NestedReadOnly
open Proofs.Vector2dSumCall (NOKG bindRootN_g resolve_nref)
open Proofs.CumulativeSum2DMath Proofs.CumulativeSum2DIntExec

open Proofs.Vector2dSumCall (bbV rowsVV rowsVV_row) in
def mvV2DI (V vsc : Nat) (m : Bool) (rows : List (List Int)) (L0 T0 sc N : Nat) : MV where
  nv := 1
  ty := fun _ => i32
  wV := fun _ => false
  flag := fun _ => m
  R := fun _ => V
  vsc := fun _ => vsc
  perm := by intro k hk; simp at hk
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; simp at hw
  flat := fun _ => false
  wflat := by intro k hk; simp at hk
  wN := fun _ => false
  permN := by intro k hk; simp at hk
  wNnest := by intro k hk; simp at hk
  wrows := fun _ => rows.length
  nvSmall := by decide
  rfree := by intro j k i hj hk hf; simp at hf
  nfree := by
    intro k k' i i' hk hk' hf hf' hi hi' hne
    have hk0 : k = 0 := by simpa using hk
    have hk1 : k' = 0 := by simpa using hk'
    subst hk0; subst hk1
    have : i ≠ i' := by rcases hne with h | h; exact absurd rfl h; exact h
    show V + 1 + i ≠ V + 1 + i'
    omega
  nroot := by intro k k' i hk hk' hf hf' hi; show V ≠ V + 1 + i; omega
  wfree := by intro j k hj hk hw; simp at hw

open Proofs.Vector2dSumCall (bbV rowsVV rowsVV_row) in
theorem fwV2D_initI (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)} {wb m : Bool}
    (ok : NOKG caller i32 vslot vb V vsc rows wb m) (hR : rows.length < 4294967296)
    (hs2 : ∀ i (h : i < rows.length), (rows[i]).length < 2^64) :
    FWM (mvV2DI V vsc m rows caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (rowsVV rows) bbV 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V,.vector (.integer i32),false,.root vsc⟩]⟩ : Frame) := by
  refine ⟨ok.valid, ok.lengths, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok.strict owner k h
    show k < caller.scope + 1
    omega
  · simp [bindOf, mvV2DI]
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hn
    have hk0 : k = 0 := by simp [mvV2DI] at hk; omega
    subst hk0
    refine ⟨by simp [mvV2DI]; omega, ?_, ok.graph, ok.flag, ?_⟩
    · intro i hi
      simp only [mvV2DI] at hi
      rw [rowsVV_row rows hR i hi]; exact hs2 i hi
    · intro i hi
      simp only [mvV2DI] at hi
      rw [rowsVV_row rows hR i hi]; exact ok.rowsStore i hi


theorem prepare_cs2 (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)} {wb m : Bool}
    (ok : NOKG caller i32 vslot vb V vsc rows wb m) (e1 e2 : NExpr) (v1 v2 : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (hty1 : e1.resultType = i32) (hty2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some v1) (value2 : e2.denote (envOf caller) = some v2)
    (hv1 : i32.valid v1 = true) (hv2 : i32.valid v2 = true) :
    ∃ t, Good (caller.charge 1 1) t (e1.nodes+e2.nodes) (max e1.nodes e2.nodes) ∧
      ∃ Sinit, prepare caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_2.parameters
          [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.vector (.integer i32),false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_nref caller i32 false ok.slot ok.binding ok.graph ok.lengths ok.flag ok.perm (fun h => absurd h (by decide))
  obtain ⟨t1,ran1,good1⟩ := scalar_eval e1 (caller.charge 1 1) v1 hs1
    (by rw [envOf_core (core_charge caller 1 1)]; exact value1)
  obtain ⟨t,ran2,good2⟩ := scalar_eval e2 t1 v2 hs2
    (by rw [envOf_core good1.1, envOf_core (core_charge caller 1 1)]; exact value2)
  have good := good1.trans good2
  refine ⟨t,good,?_⟩
  have res1 : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,hty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t,.scalar i32 true v2) := by
    simp [resolve,hty2,ran2]
  have frameT : t.frame = caller.frame := by rw [good.1.1]; rfl
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := by rw [good.1.2.2.2.1]; rfl
  have hbind : t.scalars.bindings = caller.scalars.bindings := by rw [good.1.2.2.2.2.1]; rfl
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := by rw [good.1.2.2.2.2.2]; rfl
  have b0 := bindRootN_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V) (vsc := vsc) (m := m) i32 false
    ok.graph ok.lengths ok.flag (fun h => absurd h (by decide))
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0
  have hp : Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_2.parameters =
      [.nested i32 false,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rv0,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,b0,bindAll,bindOne,CppState.bindArgument,hv1,hv2,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega

/-- The rows of the finished table of `V` (`V.length + 1` rows of `m + 1` entries). -/
def csRows (V : List (List Int)) (m : Nat) : List (List Int) := (List.range (V.length + 1)).map (csRow V m V.length 0)

theorem csRows_length (V : List (List Int)) (m : Nat) : (csRows V m).length = V.length + 1 := by simp [csRows]

theorem csRows_get (V : List (List Int)) (m i : Nat) (h : i < (csRows V m).length) :
    (csRows V m)[i] = csRow V m V.length 0 i := by
  simp [csRows]

theorem VCS_final_row (V : List (List Int)) (m : Nat) (hn : V.length + 1 < 4294967296) (i : Nat)
    (h : i < (csRows V m).length) : VCS V m V.length 0 (rowKey 0 i) = (csRows V m)[i] := by
  rw [csRows_get V m i h, rowKey_eq_rk, VCS_cs V m V.length 0 i (by rw [csRows_length] at h; omega)]

theorem fwCS_init (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)} {wb m : Bool}
    (ok : NOKG caller i32 vslot vb V vsc rows wb m) (hR : rows.length < 4294967296) (vv : Nat → List Int)
    (hvv : ∀ i (h : i < rows.length), vv (rowKey 0 i) = rows[i])
    (hs2 : ∀ i (h : i < rows.length), (rows[i]).length < 2^64) :
    FWM (mvV2DI V vsc m rows caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) vv Proofs.Vector2dSumCall.bbV 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V,.vector (.integer i32),false,.root vsc⟩]⟩ : Frame) := by
  have := fwV2D_initI caller ok hR hs2
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := this
  refine ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,?_,a12,a13,a14,?_,?_⟩
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hf; simp [mvV2DI] at hf
  · intro k hk hn
    obtain ⟨b1,b2,b3,b4,b5⟩ := a16 k hk hn
    have hk0 : k = 0 := by simp [mvV2DI] at hk; omega
    subst hk0
    refine ⟨b1,?_,b3,b4,?_⟩
    · intro i hi; rw [hvv i hi]; exact hs2 i hi
    · intro i hi
      obtain ⟨buf,hb,hit⟩ := b5 i hi
      exact ⟨buf,hb,by rw [hvv i hi]; rw [Proofs.Vector2dSumCall.rowsVV_row rows hR i hi] at hit; exact hit⟩

theorem csRows_len_small (T : List (List Int)) (mm : Nat) (hM : mm + 1 < 4294967296) :
    ∀ i (h : i < (csRows T mm).length), ((csRows T mm)[i]).length < 2^64 := by
  intro i h
  rw [csRows_get T mm i h, csRow_length]
  have : (4294967296 : Nat) ≤ 2^64 := by norm_num
  omega

theorem take_P_ext (caller : NState) (extra : List Cell) :
    (callerP caller ++ extra).take caller.scalars.memory.length = caller.scalars.memory := by
  rw [List.take_append_of_le_length (by simp [callerP])]
  simp only [callerP, List.append_assoc]
  rw [List.take_append_of_le_length (by simp)]
  exact List.take_length

set_option maxHeartbeats 4000000 in
/-- `CumulativeSum2D<int>::sum(a, b)` on the finished table of the matrix `T` returns the sum of `T[0, a) x [0, b)`. -/
theorem cs2_sum2_correct (caller : NState) {vslot vb V vsc : Nat} {T : List (List Int)} {mm : Nat} {wb mf : Bool}
    (ok : NOKG caller i32 vslot vb V vsc (csRows T mm) wb mf) (e1 e2 : NExpr) (a b : Nat)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (a : Int)) (value2 : e2.denote (envOf caller) = some (b : Int))
    (ha : a ≤ T.length) (hb : b ≤ mm) (hn : T.length + 1 < 2147483648) (hM : mm + 1 < 2147483648)
    (hv : i32.valid (P2 T a b) = true) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_2.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_2.callFuel fuel caller
        [.vectorReference vslot,.value e1,.value e2] = .finished (res,.scalar (P2 T a b)) ∧
      ScalarPostM (mvV2DI V vsc mf (csRows T mm) caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes + e2.nodes) 120 caller.scalars.memory 0 (VCS T mm T.length 0) := by
  have hR' : (csRows T mm).length < 4294967296 := by rw [csRows_length]; omega
  have haM : a < 2147483648 := by omega
  have hbM : b < 2147483648 := by omega
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_cs2 caller ok e1 e2 (a : Int) (b : Int) hs1 hs2 ht1 ht2 value1 value2
      (BellmanFordExec.i32_valid_nat a haM) (BellmanFordExec.i32_valid_nat b hbM)
  have fwS := fwCS_init caller ok hR' (VCS T mm T.length 0)
    (fun i h => VCS_final_row T mm (by omega) i h) (csRows_len_small T mm (by omega))
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,hrps,hcost,hneed,hwk⟩ :=
    sum2_exec (mvV2DI V vsc mf (csRows T mm) caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl rfl T mm
      (by simp [mvV2DI, csRows_length]) 1 (callerP caller) a b ha hb hn hM hv
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell),⟨i32,(b : Int)⟩],
      [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]⟩ : PS) =
      gS (callerP caller) [Proofs.ForLoop.ci a, Proofs.ForLoop.ci b] := by
    simp [gS, Proofs.ForLoop.ci, List.range_succ]
  have hpost := call_vecm (mvV2DI V vsc mf (csRows T mm) caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_2 [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell),⟨i32,(b : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    sPeak (by simp [hlenP]; omega) (by simp [take_P_ext]) ok.base
    (by rw [body_eq_s2]; simp [WrM]) 1 rr (by rw [hmk, body_eq_s2]; exact hexec) _ hret i32 rfl hv
    (by omega) (by simp [hlenP]) (e1.nodes + e2.nodes) 120 (by have g := good.2.2.1; simp [NState.charge, NState.observe, CppState.State.observe] at g; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

theorem prepare_cs4 (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)} {wb m : Bool}
    (ok : NOKG caller i32 vslot vb V vsc rows wb m) (e1 e2 e3 e4 : NExpr) (v1 v2 v3 v4 : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (hty1 : e1.resultType = i32) (hty2 : e2.resultType = i32) (hty3 : e3.resultType = i32) (hty4 : e4.resultType = i32)
    (value1 : e1.denote (envOf caller) = some v1) (value2 : e2.denote (envOf caller) = some v2)
    (value3 : e3.denote (envOf caller) = some v3) (value4 : e4.denote (envOf caller) = some v4)
    (hv1 : i32.valid v1 = true) (hv2 : i32.valid v2 = true) (hv3 : i32.valid v3 = true) (hv4 : i32.valid v4 = true) :
    ∃ t, Good (caller.charge 1 1) t (e1.nodes+e2.nodes+e3.nodes+e4.nodes) (max (max (max e1.nodes e2.nodes) e3.nodes) e4.nodes) ∧
      ∃ Sinit, prepare caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_4.parameters
          [.vectorReference vslot,.value e1,.value e2,.value e3,.value e4] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1,.scalar 2,.scalar 3] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩,⟨i32,v3⟩,⟨i32,v4⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,
          ⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.vector (.integer i32),false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+6 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_nref caller i32 false ok.slot ok.binding ok.graph ok.lengths ok.flag ok.perm (fun h => absurd h (by decide))
  obtain ⟨t1,ran1,good1⟩ := scalar_eval e1 (caller.charge 1 1) v1 hs1
    (by rw [envOf_core (core_charge caller 1 1)]; exact value1)
  obtain ⟨t2,ran2,good2⟩ := scalar_eval e2 t1 v2 hs2
    (by rw [envOf_core good1.1, envOf_core (core_charge caller 1 1)]; exact value2)
  obtain ⟨t3,ran3,good3⟩ := scalar_eval e3 t2 v3 hs3
    (by rw [envOf_core good2.1, envOf_core good1.1, envOf_core (core_charge caller 1 1)]; exact value3)
  obtain ⟨t,ran4,good4⟩ := scalar_eval e4 t3 v4 hs4
    (by rw [envOf_core good3.1, envOf_core good2.1, envOf_core good1.1, envOf_core (core_charge caller 1 1)]; exact value4)
  have good := ((good1.trans good2).trans good3).trans good4
  refine ⟨t,good,?_⟩
  have res1 : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,hty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,hty2,ran2]
  have res3 : resolve t2 (.scalar i32 false true) (.value e3) = some (t3,.scalar i32 true v3) := by
    simp [resolve,hty3,ran3]
  have res4 : resolve t3 (.scalar i32 false true) (.value e4) = some (t,.scalar i32 true v4) := by
    simp [resolve,hty4,ran4]
  have frameT : t.frame = caller.frame := by rw [good.1.1]; rfl
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := by rw [good.1.2.2.2.1]; rfl
  have hbind : t.scalars.bindings = caller.scalars.bindings := by rw [good.1.2.2.2.2.1]; rfl
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := by rw [good.1.2.2.2.2.2]; rfl
  have b0 := bindRootN_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V) (vsc := vsc) (m := m) i32 false
    ok.graph ok.lengths ok.flag (fun h => absurd h (by decide))
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0
  have hp : Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_4.parameters =
      [.nested i32 false,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rv0,res1,res2,res3,res4]
  simp [fs,fr,fb,hmem,hbind,hbase,b0,bindAll,bindOne,CppState.bindArgument,hv1,hv2,hv3,hv4,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega

set_option maxHeartbeats 4000000 in
/-- `CumulativeSum2D<int>::sum(a1, b1, a2, b2)` on the finished table of the matrix `T` returns the sum of the block
`T[a1, a2) x [b1, b2)`. -/
theorem cs2_sum4_correct (caller : NState) {vslot vb V vsc : Nat} {T : List (List Int)} {mm : Nat} {wb mf : Bool}
    (ok : NOKG caller i32 vslot vb V vsc (csRows T mm) wb mf) (e1 e2 e3 e4 : NExpr) (a1 b1 a2 b2 : Nat)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32) (ht3 : e3.resultType = i32) (ht4 : e4.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (a1 : Int)) (value2 : e2.denote (envOf caller) = some (b1 : Int))
    (value3 : e3.denote (envOf caller) = some (a2 : Int)) (value4 : e4.denote (envOf caller) = some (b2 : Int))
    (h1 : a1 ≤ a2) (h2 : a2 ≤ T.length) (h3 : b1 ≤ b2) (h4 : b2 ≤ mm) (hn : T.length + 1 < 2147483648)
    (hM : mm + 1 < 2147483648)
    (hp : i32.valid (P2 T a2 b2) = true) (hq : i32.valid (P2 T a1 b2) = true) (hr : i32.valid (P2 T a2 b1) = true)
    (hs : i32.valid (P2 T a1 b1) = true) (hv1 : i32.valid (P2 T a2 b2 - P2 T a1 b2) = true)
    (hv2 : i32.valid (P2 T a2 b2 - P2 T a1 b2 - P2 T a2 b1) = true)
    (hv3 : i32.valid (P2 T a2 b2 - P2 T a1 b2 - P2 T a2 b1 + P2 T a1 b1) = true) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_4.parameters
        [.vectorReference vslot,.value e1,.value e2,.value e3,.value e4] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_4.callFuel fuel caller
        [.vectorReference vslot,.value e1,.value e2,.value e3,.value e4] =
        .finished (res,.scalar (P2 T a2 b2 - P2 T a1 b2 - P2 T a2 b1 + P2 T a1 b1)) ∧
      ScalarPostM (mvV2DI V vsc mf (csRows T mm) caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes) 250 caller.scalars.memory 0 (VCS T mm T.length 0) := by
  have hR' : (csRows T mm).length < 4294967296 := by rw [csRows_length]; omega
  have ha1 : a1 < 2147483648 := by omega
  have hb1 : b1 < 2147483648 := by omega
  have ha2 : a2 < 2147483648 := by omega
  have hb2 : b2 < 2147483648 := by omega
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_cs4 caller ok e1 e2 e3 e4 (a1 : Int) (b1 : Int) (a2 : Int) (b2 : Int) hs1 hs2 hs3 hs4 ht1 ht2 ht3 ht4
      value1 value2 value3 value4 (BellmanFordExec.i32_valid_nat a1 ha1) (BellmanFordExec.i32_valid_nat b1 hb1)
      (BellmanFordExec.i32_valid_nat a2 ha2) (BellmanFordExec.i32_valid_nat b2 hb2)
  have fwS := fwCS_init caller ok hR' (VCS T mm T.length 0)
    (fun i h => VCS_final_row T mm (by omega) i h) (csRows_len_small T mm (by omega))
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,hrps,hcost,hneed,hwk⟩ :=
    sum4_exec (mvV2DI V vsc mf (csRows T mm) caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl rfl T mm
      (by simp [mvV2DI, csRows_length]) 1 (callerP caller) a1 b1 a2 b2 h1 h2 h3 h4 hn hM hp hq hr hs hv1 hv2 hv3
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller ++ [(⟨i32,(a1 : Int)⟩ : Cell),⟨i32,(b1 : Int)⟩,⟨i32,(a2 : Int)⟩,⟨i32,(b2 : Int)⟩],
      [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩,
        ⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩]⟩ : PS) =
      gS (callerP caller) [Proofs.ForLoop.ci a1, Proofs.ForLoop.ci b1, Proofs.ForLoop.ci a2, Proofs.ForLoop.ci b2] := by
    simp [gS, Proofs.ForLoop.ci, List.range_succ]
  have hpost := call_vecm (mvV2DI V vsc mf (csRows T mm) caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_sum_4
    [.vectorReference vslot,.value e1,.value e2,.value e3,.value e4] Sinit
    (callerP caller ++ [(⟨i32,(a1 : Int)⟩ : Cell),⟨i32,(b1 : Int)⟩,⟨i32,(a2 : Int)⟩,⟨i32,(b2 : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩,
        ⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    sPeak (by simp [hlenP]; omega) (by simp [take_P_ext]) ok.base
    (by rw [body_eq_s4]; simp [WrM]) 1 rr (by rw [hmk, body_eq_s4]; exact hexec) _ hret i32 rfl hv3
    (by omega) (by simp [hlenP]) (e1.nodes + e2.nodes + e3.nodes + e4.nodes) 250
    (by have g := good.2.2.1; simp [NState.charge, NState.observe, CppState.State.observe] at g; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

/-! ### The constructor: slot 0 = `cs` (writable nested, `n + 1` rows of `m + 1` zeros), slot 1 = `v` (const nested, `n` rows) -/

def zeroRows (n m : Nat) : List (List Int) := List.replicate (n + 1) (List.replicate (m + 1) 0)

theorem zeroRows_length (n m : Nat) : (zeroRows n m).length = n + 1 := by simp [zeroRows]

def mvCS (V0 vsc0 V1 vsc1 : Nat) (m1 : Bool) (n : Nat) (L0 T0 sc N : Nat)
    (hd0 : ∀ i i', i < n + 1 → i' < n → V0 + 1 + i ≠ V1 + 1 + i') (hd1 : ∀ i, i < n + 1 → V1 ≠ V0 + 1 + i)
    (hd2 : ∀ i, i < n → V0 ≠ V1 + 1 + i) : MV where
  nv := 2
  ty := fun _ => i32
  wV := fun _ => false
  flag := fun k => if k = 0 then true else m1
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by intro k hk; simp at hk
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; simp at hw
  flat := fun _ => false
  wflat := by intro k hk; simp at hk
  wN := fun k => decide (k = 0)
  permN := by intro k hk; have : k = 0 := by simpa using hk
              subst this; simp
  wNnest := by intro k hk; simp
  wrows := fun k => if k = 0 then n + 1 else n
  nvSmall := by decide
  rfree := by intro j k i hj hk hf; simp at hf
  nfree := by
    intro k k' i i' hk hk' hf hf' hi hi' hne
    have hk2 : k < 2 := hk
    have hk2' : k' < 2 := hk'
    show (if k = 0 then V0 else V1) + 1 + i ≠ (if k' = 0 then V0 else V1) + 1 + i'
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rcases (by omega : k' = 0 ∨ k' = 1) with rfl | rfl
    · simp at hi hi' ⊢
      have : i ≠ i' := by rcases hne with h | h; exact absurd rfl h; exact h
      omega
    · simp at hi hi' ⊢; exact hd0 i i' hi hi'
    · simp at hi hi' ⊢; exact fun h => hd0 i' i hi' hi h.symm
    · simp at hi hi' ⊢
      have : i ≠ i' := by rcases hne with h | h; exact absurd rfl h; exact h
      omega
  nroot := by
    intro k k' i hk hk' hf hf' hi
    have hk2 : k < 2 := hk
    have hk2' : k' < 2 := hk'
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rcases (by omega : k' = 0 ∨ k' = 1) with rfl | rfl
    · simp at hi ⊢; omega
    · simp at hi ⊢; exact hd1 i hi
    · simp at hi ⊢; exact hd2 i hi
    · simp at hi ⊢; omega
  wfree := by intro j k hj hk hw; simp at hw

theorem prepare_cs_ctor (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {rows0 rows1 : List (List Int)} {m1 : Bool}
    (ok0 : NOKG caller i32 s0 vb0 V0 vsc0 rows0 true true) (ok1 : NOKG caller i32 s1 vb1 V1 vsc1 rows1 false m1) :
    ∃ Sinit, prepare caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_new0.parameters
          [.vectorReference s0,.vectorReference s1] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1] ∧ Sinit.scalars.memory = callerP caller ∧ Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope + 1 ∧
        Sinit.frame = ⟨caller.frame.state, caller.frame.rootWritable,
          [⟨V0,.vector (.integer i32),true,.root vsc0⟩, ⟨V1,.vector (.integer i32),false,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work + 5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_nref caller i32 true ok0.slot ok0.binding ok0.graph ok0.lengths ok0.flag ok0.perm (fun h => rfl)
  have rv1 := resolve_nref (caller.charge 1 1) i32 false ok1.slot ok1.binding ok1.graph ok1.lengths ok1.flag ok1.perm (fun h => absurd h (by decide))
  have b0 := bindRootN_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true) i32 true
    ok0.graph ok0.lengths ok0.flag ok0.perm
  have b1 := bindRootN_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.vector (.integer i32),true,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := m1) i32 false ok1.graph ok1.lengths ok1.flag (fun h => absurd h (by decide))
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons, List.length_singleton] at b0 b1
  have hp : Proofs.CumulativeSumInstance.CumulativeSum2D_int_new0.parameters = [.nested i32 true,.nested i32 false] := rfl
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1]
  simp [b0, b1, bindAll, bindOne, CppState.bindArgument, callerP, NState.observe, CppState.State.observe, NState.charge]

theorem fwCS_ctor_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {T : List (List Int)} {mm : Nat}
    (ok0 : NOKG caller i32 s0 vb0 V0 vsc0 (zeroRows T.length mm) true true)
    (ok1 : NOKG caller i32 s1 vb1 V1 vsc1 T false m1) (hn : T.length + 1 < 4294967296) (hm : mm + 1 < 4294967296)
    (hd0 : ∀ i i', i < T.length + 1 → i' < T.length → V0 + 1 + i ≠ V1 + 1 + i')
    (hd1 : ∀ i, i < T.length + 1 → V1 ≠ V0 + 1 + i) (hd2 : ∀ i, i < T.length → V0 ≠ V1 + 1 + i)
    (hsmall : ∀ i (h : i < T.length), (T[i]).length < 2^64) :
    FWM (mvCS V0 vsc0 V1 vsc1 m1 T.length caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length hd0 hd1 hd2) (VCS T mm 0 0) Proofs.Vector2dSumCall.bbV 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.vector (.integer i32),true,.root vsc0⟩, ⟨V1,.vector (.integer i32),false,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · simp [bindOf, mvCS, List.range_succ]
  · intro k hk hf; simp [mvCS] at hf
  · intro k hk hf; simp [mvCS] at hf
  · intro k hk hf; simp [mvCS] at hf
  · intro k hk hf; simp [mvCS] at hf
  · intro k hk hf; simp [mvCS] at hf
  · intro k hk hf; simp [mvCS] at hf
  · intro k hk hf; simp [mvCS] at hf
  · intro k hk hf; simp [mvCS] at hf
  · intro k hk hn'
    have hk2 : k < 2 := hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · have hl : (zeroRows T.length mm).length = T.length + 1 := zeroRows_length _ _
      refine ⟨by simp [mvCS]; omega, ?_, by simpa [mvCS, hl] using ok0.graph, by simpa [mvCS] using ok0.flag, ?_⟩
      · intro i hi
        simp only [mvCS] at hi
        simp only [if_true] at hi
        rw [rowKey_eq_rk, VCS_cs T mm 0 0 i (by omega), csRow_length]
        have : (4294967296 : Nat) ≤ 2^64 := by norm_num
        omega
      · intro i hi
        simp only [mvCS, if_true] at hi
        obtain ⟨buf, hb, hit⟩ := ok0.rowsStore i (by omega)
        refine ⟨buf, by simpa [mvCS] using hb, ?_⟩
        rw [rowKey_eq_rk, VCS_cs T mm 0 0 i (by omega), csRow_zero]
        rw [hit]
        simp [zeroRows]
    · refine ⟨by simp [mvCS]; omega, ?_, by simpa [mvCS] using ok1.graph, by simpa [mvCS] using ok1.flag, ?_⟩
      · intro i hi
        simp only [mvCS] at hi
        simp at hi
        rw [rowKey_eq_rk, VCS_v T mm 0 0 i (by omega)]
        simpa [List.getElem?_eq_getElem hi] using hsmall i hi
      · intro i hi
        simp only [mvCS] at hi
        simp at hi
        obtain ⟨buf, hb, hit⟩ := ok1.rowsStore i hi
        refine ⟨buf, by simpa [mvCS] using hb, ?_⟩
        rw [rowKey_eq_rk, VCS_v T mm 0 0 i (by omega), hit]
        simp [List.getElem?_eq_getElem hi]

set_option maxHeartbeats 4000000 in
/-- `CumulativeSum2D<int>(v)` fills the field `cs` (already `v.size() + 1` rows of `v[0].size() + 1` zeros by the standard
constructor) with the two-dimensional prefix sums of `v`: afterwards `cs[a][b] = P2 v a b`. -/
theorem cs2_ctor_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {T : List (List Int)} {mm : Nat}
    (ok0 : NOKG caller i32 s0 vb0 V0 vsc0 (zeroRows T.length mm) true true)
    (ok1 : NOKG caller i32 s1 vb1 V1 vsc1 T false m1)
    (hd0 : ∀ i i', i < T.length + 1 → i' < T.length → V0 + 1 + i ≠ V1 + 1 + i')
    (hd1 : ∀ i, i < T.length + 1 → V1 ≠ V0 + 1 + i) (hd2 : ∀ i, i < T.length → V0 ≠ V1 + 1 + i)
    (hpos : 0 < T.length) (hm : 0 < mm) (hM : mm + 1 < 2147483648) (hn' : T.length + 1 < 2147483648)
    (hrect : ∀ r ∈ T, r.length = mm) (hvalid : ∀ r ∈ T, ∀ x ∈ r, i32.valid x = true)
    (hRun : ∀ (t j : Nat) (r : List Int), T[t]? = some r → j ≤ mm → i32.valid ((r.take j).sum) = true)
    (hP : ∀ a b, a ≤ T.length → b ≤ mm → i32.valid (P2 T a b) = true) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_new0.parameters
        [.vectorReference s0,.vectorReference s1] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum2D_int_new0.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1] = .finished (res,Ret.unit) ∧
      ScalarPostM (mvCS V0 vsc0 V1 vsc1 m1 T.length caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hd0 hd1 hd2)
        caller Sinit res 0 ((80 * mm + 100) * T.length + 110) caller.scalars.memory (mm * T.length) (VCS T mm T.length 0) := by
  have hn32 : T.length + 1 < 4294967296 := by omega
  have hm32 : mm + 1 < 4294967296 := by omega
  have hsmall : ∀ i (h : i < T.length), (T[i]).length < 2^64 := by
    intro i h
    rw [hrect _ (List.getElem_mem h)]
    have : (4294967296 : Nat) ≤ 2^64 := by norm_num
    omega
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_cs_ctor caller ok0 ok1
  have fwS := fwCS_ctor_init caller ok0 ok1 hn32 hm32 hd0 hd1 hd2 hsmall
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    ctor_exec (mvCS V0 vsc0 V1 vsc1 m1 T.length caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length hd0 hd1 hd2) rfl rfl rfl rfl rfl (by simp [mvCS]) T mm
      (by simp [mvCS]) (by simp [mvCS]) (mm + T.length + 2) (callerP caller) hpos hm hM hn' hrect hvalid hRun hP (by omega)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm_unit (mvCS V0 vsc0 V1 vsc1 m1 T.length caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hd0 hd1 hd2) (fun k => decide (k = 0))
    (by intro k hk; have : k = 0 := by simpa using hk
        subst this; simp [mvCS])
    caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_new0
    [.vectorReference s0,.vectorReference s1] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    sPeak (by simp [hlenP]) (by simp [callerP]) ok0.base
    (by rw [body_eq2]; simp [WrM]) (mm + T.length + 2) rr (by rw [hmk, body_eq2]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) 0 ((80 * mm + 100) * T.length + 110) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

/-- After the constructor, the row objects of `cs` hold exactly the rows of the finished table `csRows T mm`, which is the
ownership state that `cs2_sum2_correct` and `cs2_sum4_correct` take. -/
theorem cs2_ctor_table (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {T : List (List Int)} {mm : Nat}
    (ok0 : NOKG caller i32 s0 vb0 V0 vsc0 (zeroRows T.length mm) true true)
    (ok1 : NOKG caller i32 s1 vb1 V1 vsc1 T false m1)
    (hd0 : ∀ i i', i < T.length + 1 → i' < T.length → V0 + 1 + i ≠ V1 + 1 + i')
    (hd1 : ∀ i, i < T.length + 1 → V1 ≠ V0 + 1 + i) (hd2 : ∀ i, i < T.length → V0 ≠ V1 + 1 + i)
    (hpos : 0 < T.length) (hm : 0 < mm) (hM : mm + 1 < 2147483648) (hn' : T.length + 1 < 2147483648)
    (hrect : ∀ r ∈ T, r.length = mm) (hvalid : ∀ r ∈ T, ∀ x ∈ r, i32.valid x = true)
    (hRun : ∀ (t j : Nat) (r : List Int), T[t]? = some r → j ≤ mm → i32.valid ((r.take j).sum) = true)
    (hP : ∀ a b, a ≤ T.length → b ≤ mm → i32.valid (P2 T a b) = true) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.CumulativeSumInstance.CumulativeSum2D_int_new0.parameters
        [.vectorReference s0,.vectorReference s1] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum2D_int_new0.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1] = .finished (res,Ret.unit) ∧
      res.frame.state.wellFormed = true ∧
      (∀ i (h : i < (csRows T mm).length), ∃ buf, res.frame.state.storage.lookup (V0 + 1 + i) = some buf ∧
        buf.items = ((csRows T mm)[i]).map Value.integer) ∧
      res.scalars.work ≤ caller.scalars.work + ((80 * mm + 100) * T.length + 110) := by
  obtain ⟨S,f,r,h1,h2,post⟩ := cs2_ctor_correct caller ok0 ok1 hd0 hd1 hd2 hpos hm hM hn' hrect hvalid hRun hP
  refine ⟨S,f,r,h1,h2,post.valid,?_,by have := post.scalarWork; omega⟩
  intro i h
  have hn32 : T.length + 1 < 4294967296 := by omega
  obtain ⟨_,_,_,_,rows⟩ := post.nested 0 (by simp [mvCS]) (by simp [mvCS])
  obtain ⟨buf,hb,hit⟩ := rows i (by simp [mvCS]; rw [csRows_length] at h; omega)
  refine ⟨buf, by simpa [mvCS] using hb, ?_⟩
  rw [hit, VCS_final_row T mm hn32 i h]

end Proofs.CumulativeSum2DIntCall
