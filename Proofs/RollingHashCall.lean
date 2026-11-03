import Proofs.RollingHashMath
import Proofs.RollingHashGet
import Proofs.RollingHashExec
import Proofs.FenwickTreeVecCall

namespace Proofs.RollingHashCall
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

/-! ### `RollingHash<int>::hash(l, r)`: vectors `hs`, `pw` (`unsigned long long`, read-only) and the values `l`, `r` -/

theorem prepare_rhg (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (e1 e2 : NExpr) (v1 v2 : Int) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (n1 : i32.valid v1 = true) (n2 : i32.valid v2 = true) :
    ∃ t1 t2, Good ((caller.charge 1 1).charge 1 1) t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller Proofs.RollingHashInstance.RollingHash_int_hash_2.parameters
          [.vectorReference s0,.vectorReference s1,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer u64,false,.root vsc0⟩,⟨V1,.integer u64,false,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+5 ∧ t2.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller u64 false ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => absurd h (by decide))
  have rv1 := resolve_vref (caller.charge 1 1) u64 false ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound
    ok1.lengths ok1.flag ok1.perm (fun h => absurd h (by decide))
  have core2 : Core caller ((caller.charge 1 1).charge 1 1) := (core_charge caller 1 1).trans (core_charge _ 1 1)
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 ((caller.charge 1 1).charge 1 1) v1 hs1 (by rw [envOf_core core2]; exact d1)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 hs2 (by rw [envOf_core g1.1, envOf_core core2]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have res1 : resolve ((caller.charge 1 1).charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,ty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t2,.scalar i32 true v2) := by
    simp [resolve,ty2,ran2]
  have frameT : t2.frame = caller.frame := g2.1.1.trans g1.1.1
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := g2.1.2.2.2.1.trans g1.1.2.2.2.1
  have hbind : t2.scalars.bindings = caller.scalars.bindings := g2.1.2.2.2.2.1.trans g1.1.2.2.2.2.1
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := g2.1.2.2.2.2.2.trans g1.1.2.2.2.2.2
  have hp : Proofs.RollingHashInstance.RollingHash_int_hash_2.parameters =
      [.vector u64 false,.vector u64 false,.scalar i32 false true,.scalar i32 false true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := m0)
    (vbuf := vbuf0) u64 false ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer u64,false,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := m1) (vbuf := vbuf1) u64 false ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, res1, res2]
  simp [fs, fr, fb, hmem, hbind, hbase, b0, b1, bindAll, bindOne, CppState.bindArgument, n1, n2, callerP,
    NState.observe, CppState.State.observe]
  have a1 := g1.2.2.2.2.1
  have a2 := g2.2.2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at a1
  left
  omega

open Proofs.RollingHashBuild (HF PF Hs Ps HF_lt PF_lt Hs_len Ps_len) in
open Proofs.RollingHashGet (VG get_exec progG body_eqG) in
open Proofs.FenwickTreeVecCall (items_valid) in
def mvRH (V0 V1 vsc0 vsc1 : Nat) (m0 m1 : Bool) (L0 T0 sc N : Nat) : MV where
  nv := 2
  ty := fun _ => u64
  wV := fun _ => false
  flag := fun k => if k = 0 then m0 else m1
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by intro k hk; simp at hk
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; simp at hw

def bbRH (b0 b1 : Buffer Value) : Nat → Buffer Value := fun k => if k = 0 then b0 else b1

theorem wr_bodyRH : WrM (fun _ => false) (Proofs.RollingHashGet.progG 2) = true := by decide

open Proofs.RollingHashGet (VG) in
theorem fwRH_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (HS PW : List Nat) (hH : HS.length < 2147483647) (hP : PW.length < 2147483647)
    (i0 : vbuf0.items = (HS.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (PW.map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvRH V0 V1 vsc0 vsc1 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length)
      (VG HS PW) (bbRH vbuf0 vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer u64,false,.root vsc0⟩,⟨V1,.integer u64,false,.root vsc1⟩]⟩ : Frame) := by
  have cases2 : ∀ k, k < 2 → k = 0 ∨ k = 1 := fun k hk => by omega
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvRH] using ok0.vtag
    · simpa [mvRH] using ok1.vtag
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvRH, bbRH] using ok0.vfound
    · simpa [mvRH, bbRH] using ok1.vfound
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvRH] using ok0.flag
    · simpa [mvRH] using ok1.flag
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvRH, bbRH, VG] using i0
    · simpa [mvRH, bbRH, VG] using i1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvRH, bbRH] using bv0
    · simpa [mvRH, bbRH] using bv1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvRH, bbRH] using l0
    · simpa [mvRH, bbRH] using l1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvRH, bbRH] using o0
    · simpa [mvRH, bbRH] using o1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simp [VG]; omega
    · simp [VG]; omega

open Proofs.RollingHashBuild (HF PF Hs Ps HF_lt PF_lt Hs_len Ps_len) in
theorem Hs_getD (b : Nat) (S : List Nat) (n i : Nat) (hi : i ≤ n) : (Hs b S n).getD i 0 = HF b S i := by
  simp [Hs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, show i < n + 1 by omega]

open Proofs.RollingHashBuild (HF PF Hs Ps HF_lt PF_lt Hs_len Ps_len) in
theorem Ps_getD (b : Nat) (n i : Nat) (hi : i ≤ n) : (Ps b n).getD i 0 = PF b i := by
  simp [Ps, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, show i < n + 1 by omega]

open Proofs.RollingHashBuild (HF PF Hs Ps HF_lt PF_lt Hs_len Ps_len) in
open Proofs.RollingHashGet (VG get_exec progG body_eqG) in
open Proofs.RollingHashMath (polyHash sub_hash) in
open Proofs.FenwickTreeVecCall (items_valid) in
set_option maxHeartbeats 4000000 in
/-- `RollingHash<int>::hash(l, r)` on the vectors built by the constructor (`Hs 131 S n`, `Ps 131 n`) is the polynomial
hash of `S[l, r)`. -/
theorem rolling_hash_hash_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (S : List Nat) (n : Nat) (hn : n < 2147483646) (hS : S.length = n)
    (i0 : vbuf0.items = ((Hs 131 S n).map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = ((Ps 131 n).map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 e2 : NExpr) (l r : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (l : Int)) (value2 : e2.denote (envOf caller) = some (r : Int))
    (hl : l ≤ r) (hr : r ≤ n) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.RollingHashInstance.RollingHash_int_hash_2.parameters
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2] = some Sinit ∧
      Proofs.RollingHashInstance.RollingHash_int_hash_2.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1,.value e2] =
        .finished (res,.scalar ((polyHash 131 ((S.drop l).take (r - l)) : Nat) : Int)) ∧
      ScalarPostM (mvRH V0 V1 vsc0 vsc1 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes + e2.nodes) 1100 caller.scalars.memory 0 (VG (Hs 131 S n) (Ps 131 n)) := by
  have hb131 : (131 : Nat) < 2^61 := by decide
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_rhg caller ok0 ok1 e1 e2 (l : Int) (r : Int) hs1 hs2 ty1 ty2 value1 value2
      (validN l (by omega)) (validN r (by omega))
  have fwS := fwRH_init caller ok0 ok1 (Hs 131 S n) (Ps 131 n) (by simp [Hs_len]; omega) (by simp [Ps_len]; omega)
    i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  have hHl : (Hs 131 S n).length = n + 1 := Hs_len 131 S n
  have hPl : (Ps 131 n).length = n + 1 := Ps_len 131 n
  have hHS : ∀ x ∈ Hs 131 S n, x < 2^61 := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact HF_lt 131 S q
  have hPW : ∀ x ∈ Ps 131 n, x < 2^61 := by
    intro x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact PF_lt 131 q
  obtain ⟨rr,hexec,hret,⟨L,hrps⟩,hrvv,hcost,hneed,hwk⟩ :=
    get_exec (mvRH V0 V1 vsc0 vsc1 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length) rfl (by simp [mvRH]) (by simp [mvRH])
      1 (callerP caller) (Hs 131 S n) (Ps 131 n) l r hl (by omega) (by omega) (by omega) hHS hPW
  have hval : ((Hs 131 S n).getD r 0 + 4 * Proofs.Mod61Body.M61 - Proofs.Mul61Body.retOf ((Hs 131 S n).getD l 0)
      ((Ps 131 n).getD (r - l) 0)) % Proofs.Mod61Body.M61 = polyHash 131 ((S.drop l).take (r - l)) := by
    rw [Hs_getD 131 S n r hr, Hs_getD 131 S n l (by omega), Ps_getD 131 n (r - l) (by omega)]
    exact sub_hash 131 S hb131 l r hl (by omega)
  rw [hval] at hret
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hmk : (⟨callerP caller ++ [(⟨i32,(l : Int)⟩ : Cell),⟨i32,(r : Int)⟩],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [ci l, ci r] := by
    simp [gS, List.range_succ]
  have hres : u64.valid ((polyHash 131 ((S.drop l).take (r - l)) : Nat) : Int) = true :=
    u64_lt _ (by have := Proofs.RollingHashMath.polyHash_lt 131 ((S.drop l).take (r - l)); unfold Proofs.Mod61Body.M61 at this; omega)
  have hpost := call_vecm (mvRH V0 V1 vsc0 vsc1 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller Proofs.RollingHashInstance.RollingHash_int_hash_2
    [.vectorReference s0,.vectorReference s1,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(l : Int)⟩ : Cell),⟨i32,(r : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by simp [callerP, List.take_append_of_le_length]) ok0.base
    (by rw [body_eqG]; exact wr_bodyRH) 1 rr (by rw [hmk, body_eqG]; exact hexec) _ hret u64 rfl hres
    (by omega) (by simp [hlenP]) (e1.nodes + e2.nodes) 1100 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

/-! ### `RollingHash<int>::RollingHash(const std::vector<int> &)`: vectors `hs`, `pw` (writable) and `s` -/

theorem prepare_rhn (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m2 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 false m2 vbuf2) :
    ∃ Sinit, prepare caller Proofs.RollingHashInstance.RollingHash_int_new0.parameters
          [.vectorReference s0,.vectorReference s1,.vectorReference s2] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.vector 2] ∧ Sinit.scalars.memory = callerP caller ∧
        Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer u64,true,.root vsc0⟩,⟨V1,.integer u64,true,.root vsc1⟩,⟨V2,.integer i32,false,.root vsc2⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work+7 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller u64 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) u64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => rfl)
  have rv2 := resolve_vref ((caller.charge 1 1).charge 1 1) i32 false ok2.slot ok2.binding ok2.valid ok2.vtag ok2.vfound
    ok2.lengths ok2.flag ok2.perm (fun h => absurd h (by decide))
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true)
    (vbuf := vbuf0) u64 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer u64,true,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) u64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  have b2 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer u64,true,.root vsc0⟩,
    ⟨V1,.integer u64,true,.root vsc1⟩]⟩ : Frame)
    (V := V2) (vsc := vsc2) (m := m2) (vbuf := vbuf2) i32 false ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1 b2
  have hp : Proofs.RollingHashInstance.RollingHash_int_new0.parameters = [.vector u64 true,.vector u64 true,.vector i32 false] := rfl
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, rv2]
  simp [b0, b1, b2, bindAll, bindOne, CppState.bindArgument, callerP, NState.observe, CppState.State.observe,
    NState.charge]

def mvRHn (V0 V1 V2 vsc0 vsc1 vsc2 : Nat) (m2 : Bool) (L0 T0 sc N : Nat) (h10 : V1 ≠ V0) (h20 : V2 ≠ V0)
    (h21 : V2 ≠ V1) : MV where
  nv := 3
  ty := fun k => if k < 2 then u64 else i32
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
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    have hk3 : k = 0 ∨ k = 1 := by omega
    rcases hj3 with rfl | rfl | rfl <;> rcases hk3 with rfl | rfl <;> simp_all [Ne.symm]


def bbRHn (b0 b1 b2 : Buffer Value) : Nat → Buffer Value := fun k => if k = 0 then b0 else if k = 1 then b1 else b2

theorem wr_bodyRHn : WrM (fun k => decide (k < 2)) (Proofs.RollingHashBuild.progB 3) = true := by decide

open Proofs.RollingHashBuild (VR) in
theorem fwRHn_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m2 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 false m2 vbuf2)
    (h10 : V1 ≠ V0) (h20 : V2 ≠ V0) (h21 : V2 ≠ V1)
    (S HS PW : List Nat) (hH : HS.length < 2147483647) (hP : PW.length < 2147483647) (hS : S.length < 2147483647)
    (i0 : vbuf0.items = (HS.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (PW.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = (S.map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) :
    FWM (mvRHn V0 V1 V2 vsc0 vsc1 vsc2 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10 h20 h21)
      (VR S HS PW) (bbRHn vbuf0 vbuf1 vbuf2) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer u64,true,.root vsc0⟩,⟨V1,.integer u64,true,.root vsc1⟩,⟨V2,.integer i32,false,.root vsc2⟩]⟩ : Frame) := by
  have cases3 : ∀ k, k < 3 → k = 0 ∨ k = 1 ∨ k = 2 := fun k hk => by omega
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvRHn] using ok0.vtag
    · simpa [mvRHn] using ok1.vtag
    · simpa [mvRHn] using ok2.vtag
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvRHn, bbRHn] using ok0.vfound
    · simpa [mvRHn, bbRHn] using ok1.vfound
    · simpa [mvRHn, bbRHn] using ok2.vfound
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvRHn] using ok0.flag
    · simpa [mvRHn] using ok1.flag
    · simpa [mvRHn] using ok2.flag
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvRHn, bbRHn, VR] using i0
    · simpa [mvRHn, bbRHn, VR] using i1
    · simpa [mvRHn, bbRHn, VR] using i2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvRHn, bbRHn] using bv0
    · simpa [mvRHn, bbRHn] using bv1
    · simpa [mvRHn, bbRHn] using bv2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvRHn, bbRHn] using l0
    · simpa [mvRHn, bbRHn] using l1
    · simpa [mvRHn, bbRHn] using l2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvRHn, bbRHn] using o0
    · simpa [mvRHn, bbRHn] using o1
    · simpa [mvRHn, bbRHn] using o2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simp [VR]; omega
    · simp [VR]; omega
    · simp [VR]; omega

open Proofs.RollingHashBuild (VR HF PF Hs Ps progB body_eqRB) in
open Proofs.RollingHashExec (build_exec) in
open Proofs.FenwickTreeVecCall (items_valid) in
set_option maxHeartbeats 4000000 in
/-- `RollingHash<int>(s)` (the vectors `hs`, `pw` already `s.size() + 1` elements long by the standard constructor)
fills `hs` with the prefix hashes `Hs 131 S n` and `pw` with the powers `Ps 131 n`. -/
theorem rolling_hash_build_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m2 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 false m2 vbuf2)
    (h10 : V1 ≠ V0) (h20 : V2 ≠ V0) (h21 : V2 ≠ V1)
    (S HS0 PW0 : List Nat) (n : Nat) (hn : n < 2147483646) (hS : S.length = n) (hSv : ∀ x ∈ S, x < 2147483648)
    (hH : HS0.length = n + 1) (hW : PW0.length = n + 1)
    (i0 : vbuf0.items = (HS0.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (PW0.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = (S.map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.RollingHashInstance.RollingHash_int_new0.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2] = some Sinit ∧
      Proofs.RollingHashInstance.RollingHash_int_new0.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2] = .finished (res,Ret.unit) ∧
      ScalarPostM (mvRHn V0 V1 V2 vsc0 vsc1 vsc2 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10 h20 h21)
        caller Sinit res 0 (2120 * n + 400) caller.scalars.memory (2 * n + 2)
        (VR S (Hs 131 S n) (Ps 131 n)) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_rhn caller ok0 ok1 ok2
  have fwS := fwRHn_init caller ok0 ok1 ok2 h10 h20 h21 S HS0 PW0 (by omega) (by omega) (by omega)
    i0 i1 i2 bv0 bv1 bv2 l0 l1 l2 o0 o1 o2
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    build_exec (mvRHn V0 V1 V2 vsc0 vsc1 vsc2 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10 h20 h21) rfl (by simp [mvRHn])
      (by simp [mvRHn]) (by simp [mvRHn])
      (n + 1) (callerP caller) S HS0 PW0 131 n rfl (by omega) hS hSv hH hW (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm_unit (mvRHn V0 V1 V2 vsc0 vsc1 vsc2 m2 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h10 h20 h21)
    (fun k => decide (k < 2))
    (by intro k hk; have : k < 2 := by simpa using hk
        simp [mvRHn, this])
    caller Proofs.RollingHashInstance.RollingHash_int_new0
    [.vectorReference s0,.vectorReference s1,.vectorReference s2] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by simp [callerP]) ok0.base (by rw [body_eqRB]; exact wr_bodyRHn)
    (n + 1) rr (by rw [hmk, body_eqRB]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) 0 (2120 * n + 400) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  have hd0 : HS0.drop (n + 1) = [] := List.drop_of_length_le (by omega)
  have hd1 : PW0.drop (n + 1) = [] := List.drop_of_length_le (by omega)
  rw [hs', hrvv, hd0, hd1, List.append_nil, List.append_nil] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.RollingHashCall
