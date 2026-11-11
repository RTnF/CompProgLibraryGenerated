import Proofs.FenwickRangeCall
import Proofs.CumulativeSumIntExec
import Proofs.FenwickTreeVecCall
import Proofs.Generated.CumulativeSum
import Proofs.UfRootCall

namespace Proofs.CumulativeSumIntCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall Proofs.FenwickMath
open Proofs.VectorSumCall (conv_signed i32_valid)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk)
open Proofs.FenwickRangeCall (R0 LocT envT R0_loc0 R0_loc1)

theorem prepare_fsI (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.UfRootCall.VOKI caller vslot vb V vsc m vbuf) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v) (hv : i32.valid v = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.CumulativeSumInstance.CumulativeSum_int_sum_1.parameters [.vectorReference vslot,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector i32 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 false) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  obtain ⟨t,ran,good⟩ := scalar_eval e (caller.charge 1 1) v hs
    (by rw [envOf_core (core_charge caller 1 1)]; exact value)
  refine ⟨t,good,?_⟩
  have res : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e) = some (t,.scalar i32 true v) := by
    simp [resolve,hty,ran]
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc false =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,false,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some m :=
      maximum_runs _ V V m ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.CumulativeSumInstance.CumulativeSum_int_sum_1.parameters = [.vector i32 false,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega

theorem prepare_frrI (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.UfRootCall.VOKI caller vslot vb V vsc m vbuf) (e1 e2 : NExpr) (v1 v2 : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (hty1 : e1.resultType = i32) (hty2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some v1) (value2 : e2.denote (envOf caller) = some v2)
    (hv1 : i32.valid v1 = true) (hv2 : i32.valid v2 = true) :
    ∃ t, Good (caller.charge 1 1) t (e1.nodes+e2.nodes) (max e1.nodes e2.nodes) ∧
      ∃ Sinit, prepare caller Proofs.CumulativeSumInstance.CumulativeSum_int_sum_2.parameters
          [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector i32 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 false) := by
    simp [resolve,ok.slot,ok.binding,resolved]
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
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc false =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,false,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some m :=
      maximum_runs _ V V m ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.CumulativeSumInstance.CumulativeSum_int_sum_2.parameters =
      [.vector i32 false,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv1,hv2,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega

section FTI
open Proofs.MultiVec Proofs.MultiVecCall Proofs.MultiKit Proofs.MatMulPrepare Proofs.GenState Proofs.FenwickTreeVecCall Proofs.FenwickTreeExec

theorem prepare_ftI (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1) :
    ∃ Sinit, prepare caller Proofs.CumulativeSumInstance.CumulativeSum_int_new0.parameters
          [.vectorReference s0,.vectorReference s1] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1] ∧ Sinit.scalars.memory = callerP caller ∧
        Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer i32,true,.root vsc0⟩,⟨V1,.integer i32,false,.root vsc1⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller i32 true ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => rfl)
  have rv1 := resolve_vref (caller.charge 1 1) i32 false ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => absurd h (by decide))
  have fs : (caller.charge 1 1).frame.state = caller.frame.state := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := true)
    (vbuf := vbuf0) i32 true ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer i32,true,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := m1) (vbuf := vbuf1) i32 false ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons, List.length_singleton] at b0 b1
  have hp : Proofs.CumulativeSumInstance.CumulativeSum_int_new0.parameters = [.vector i32 true,.vector i32 false] := rfl
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1]
  simp [b0, b1, bindAll, bindOne, CppState.bindArgument, callerP, NState.observe, CppState.State.observe,
    NState.charge]


/-- The callee of the constructor: the flat vectors `tree` (writable) and `v` (`int`). -/
def mvFTI (V0 V1 vsc0 vsc1 : Nat) (m1 : Bool) (L0 T0 sc N : Nat) (h10 : V1 ≠ V0) : MV where
  nv := 2
  ty := fun _ => i32
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


/-- The frame facts at entry of the constructor body. -/
theorem fwFT_initI (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h10 : V1 ≠ V0) (T0 V : List Int) (hT : T0.length < 2147483647) (hV : V.length < 2147483647)
    (i0 : vbuf0.items = T0.map Value.integer) (i1 : vbuf1.items = V.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvFTI V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10)
      (VFT T0 V) (bbFT vbuf0 vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,true,.root vsc0⟩,⟨V1,.integer i32,false,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFTI] using ok0.vtag
    · simpa [mvFTI] using ok1.vtag
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFTI, bbFT] using ok0.vfound
    · simpa [mvFTI, bbFT] using ok1.vfound
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFTI] using ok0.flag
    · simpa [mvFTI] using ok1.flag
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFTI, bbFT, VFT] using i0
    · simpa [mvFTI, bbFT, VFT] using i1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFTI, bbFT] using bv0
    · simpa [mvFTI, bbFT] using bv1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFTI, bbFT] using l0
    · simpa [mvFTI, bbFT] using l1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvFTI, bbFT] using o0
    · simpa [mvFTI, bbFT] using o1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simp [VFT]; omega
    · simp [VFT]; omega


end FTI

-- Sum of the elements [a, b) from the prefix sums.
theorem pre_diff (A : List Int) (a b : Nat) (hab : a ≤ b) : pre A b - pre A a = ((A.drop a).take (b - a)).sum := by
  unfold pre
  have : b = a + (b - a) := by omega
  conv_lhs => rw [this, List.take_add, List.sum_append]
  omega


abbrev ck1 : NExpr := .binary bT .le (.literal i32 0) (.variable i32 1)
abbrev ck2 : NExpr := .binary bT .le (.variable i32 1) (.variable i32 2)
abbrev ckSz (k : Nat) : NExpr := .binary bT .lt (.variable i32 k) (.cast i32 (.size (.integer i32) (.local 0)))
abbrev retR : NExpr := .binary i32 .sub (.read i32 (.local 0) (.cast u64 (.variable i32 2)))
  (.read i32 (.local 0) (.cast u64 (.variable i32 1)))
abbrev retP : NExpr := .read i32 (.local 0) (.cast u64 (.variable i32 1))
abbrev bodyR : Command := .sequence (.primitive (.check ck1)) (.sequence (.primitive (.check ck2))
  (.sequence (.primitive (.check (ckSz 2))) (.sequence (.primitive (.ret retR)) Sk)))
abbrev bodyP : Command := .sequence (.primitive (.check ck1)) (.sequence (.primitive (.check (ckSz 1)))
  (.sequence (.primitive (.ret retP)) Sk))

theorem body_eqR : Proofs.CumulativeSumInstance.CumulativeSum_int_sum_2.body = bodyR := rfl
theorem body_eqP : Proofs.CumulativeSumInstance.CumulativeSum_int_sum_1.body = bodyP := rfl

theorem bool_one : bT.convert 1 = some 1 := by simp only [bT]; unfold Ty.convert; simp [Ty.valid]

theorem ck1_val (vec : List Int) (env : Nat → Ty → Option Int) (a : Nat) (e1 : env 1 i32 = some (a : Int)) :
    vdenL i32 vec env ck1 = some 1 := by
  rw [vdenL_scalar _ _ _ _ rfl, den_binary, den_literal, if_pos (show i32.valid 0 = true from rfl), den_variable, e1]
  simp only [Option.bind_some]
  have : binaryValue .le (0 : Int) (a : Int) = 1 := by simp [binaryValue]
  rw [this]; exact bool_one

theorem ck2_val (vec : List Int) (env : Nat → Ty → Option Int) (a b : Nat) (e1 : env 1 i32 = some (a : Int))
    (e2 : env 2 i32 = some (b : Int)) (hab : a ≤ b) : vdenL i32 vec env ck2 = some 1 := by
  rw [vdenL_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, e1, e2]
  simp only [Option.bind_some]
  have : binaryValue .le (a : Int) (b : Int) = 1 := by simp [binaryValue]; omega
  rw [this]; exact bool_one

theorem ckSz_val (vec : List Int) (env : Nat → Ty → Option Int) (k b : Nat) (hn : vec.length < 2147483648)
    (e : env k i32 = some (b : Int)) (hb : b < vec.length) : vdenL i32 vec env (ckSz k) = some 1 := by
  have hc : (ckSz k).scalarOnly = false := rfl
  have hr2 : (NExpr.cast i32 (.size (.integer i32) (.local 0))).scalarOnly = false := rfl
  have hn' : i32.convert (vec.length : Int) = some (vec.length : Int) :=
    conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))
  have hr : (NExpr.size (.integer i32) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenL i32 vec env (.size (.integer i32) (.local 0)) = some (vec.length : Int) := by
    simp [vdenL, hr]
  rw [vdenL_binary i32 vec env bT .lt (.variable i32 k) _ hc, vdenL_cast i32 vec _ _ _ hr2, hsz, Option.bind_some, hn',
    vdenL_scalar _ _ _ _ rfl, den_variable, e, Option.bind_some, Option.bind_some]
  have : binaryValue .lt (b : Int) (vec.length : Int) = 1 := by simp [binaryValue]; omega
  rw [this]; exact bool_one


theorem R0_envs (P : List Cell) (a b : Nat) (ha : a < 2147483648) (hb : b < 2147483648) :
    penv1 (R0 P a b) 1 i32 = some (a : Int) ∧ penv1 (R0 P a b) 2 i32 = some (b : Int) :=
  ⟨envT _ 0 _ i32 _ (R0_loc0 P a b) (i32_valid a (by omega) (by omega)),
   envT _ 1 _ i32 _ (R0_loc1 P a b) (i32_valid b (by omega) (by omega))⟩

theorem body_exec_range (P : List Cell) (vec : List Int) (a b : Nat) (hn : vec.length < 2147483648)
    (hab : a ≤ b) (hb : b < vec.length) (hel : ∀ y ∈ vec, i32.valid y = true)
    (hd : i32.valid (vec.getD b 0 - vec.getD a 0) = true) (fu : Nat) :
    ∃ r, pexecW i32 fu bodyR (R0 P a b) vec = some r ∧ r.ret = some (vec.getD b 0 - vec.getD a 0) ∧ r.vec = vec ∧
      r.cost ≤ 60 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 ∧ r.ps = R0 P a b := by
  have hA : a < vec.length := by omega
  obtain ⟨e1, e2⟩ := R0_envs P a b (by omega) (by omega)
  have c1 := pstmtW_check_ok i32 (R0 P a b) vec ck1 1 (ck1_val vec _ a e1) (by decide)
  have c2 := pstmtW_check_ok i32 (R0 P a b) vec ck2 1 (ck2_val vec _ a b e1 e2 hab) (by decide)
  have c3 := pstmtW_check_ok i32 (R0 P a b) vec (ckSz 2) 1 (ckSz_val vec _ 2 b hn e2 hb) (by decide)
  obtain ⟨xa, hxa⟩ : ∃ x, vec[a]? = some x := ⟨vec[a], by simp [hA]⟩
  obtain ⟨xb, hxb⟩ : ∃ x, vec[b]? = some x := ⟨vec[b], by simp [hb]⟩
  have ga := hel xa (List.mem_of_getElem? hxa)
  have gb := hel xb (List.mem_of_getElem? hxb)
  have hga : vec.getD a 0 = xa := by simp [List.getD_eq_getElem?_getD, hxa]
  have hgb : vec.getD b 0 = xb := by simp [List.getD_eq_getElem?_getD, hxb]
  rw [hga, hgb] at hd
  have ia := Proofs.FenwickRangeCall.envT (R0 P a b) 0 P.length i32 (a : Int) (R0_loc0 P a b)
    (i32_valid a (by omega) (by omega))
  have idxa : (NExpr.cast u64 (.variable i32 1)).denote (penv1 (R0 P a b)) = some (a : Int) := by
    rw [den_cast]
    show ((penv1 (R0 P a b)) 1 i32).bind u64.convert = _
    rw [e1, Option.bind_some, convert_u64]
    simp; exact Int.emod_eq_of_lt (by omega) (by omega)
  have idxb : (NExpr.cast u64 (.variable i32 2)).denote (penv1 (R0 P a b)) = some (b : Int) := by
    rw [den_cast]
    show ((penv1 (R0 P a b)) 2 i32).bind u64.convert = _
    rw [e2, Option.bind_some, convert_u64]
    simp; exact Int.emod_eq_of_lt (by omega) (by omega)
  have hbn : retR.scalarOnly = false := rfl
  have rda : vdenL i32 vec (penv1 (R0 P a b)) (.read i32 (.local 0) (.cast u64 (.variable i32 1))) = some xa := by
    rw [vdenL_read _ _ _ _ _ rfl, if_pos ⟨rfl, rfl⟩, idxa, Option.bind_some]
    simp [elemAtL, hxa, ga]
  have rdb : vdenL i32 vec (penv1 (R0 P a b)) (.read i32 (.local 0) (.cast u64 (.variable i32 2))) = some xb := by
    rw [vdenL_read _ _ _ _ _ rfl, if_pos ⟨rfl, rfl⟩, idxb, Option.bind_some]
    simp [elemAtL, hxb, gb]
  have rv : vdenL i32 vec (penv1 (R0 P a b)) retR = some (xb - xa) := by
    rw [vdenL_binary _ _ _ _ _ _ _ hbn, rdb, rda, Option.bind_some, Option.bind_some]
    have : binaryValue .sub xb xa = xb - xa := rfl
    rw [this]; exact Ty.convert_of_valid _ _ hd
  have rs := pstmtW_ret_ok i32 (R0 P a b) vec retR (xb - xa) rv
  have t4 := seqW_ret (b := Sk) ((pexecW_prim i32 fu (.ret retR) _ _).trans rs) rfl
  have t3 := seqW_some ((pexecW_prim i32 fu _ _ _).trans c3) rfl t4
  have t2 := seqW_some ((pexecW_prim i32 fu _ _ _).trans c2) rfl t3
  have t1 := seqW_some ((pexecW_prim i32 fu _ _ _).trans c1) rfl t2
  refine ⟨_, t1, ?_, rfl, ?_, ?_, rfl, rfl⟩
  · rw [hga, hgb]
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, R0]


theorem body_exec_prefix (P : List Cell) (vec : List Int) (a : Nat) (hn : vec.length < 2147483648)
    (ha : a < vec.length) (hel : ∀ y ∈ vec, i32.valid y = true) (fu : Nat) :
    ∃ r, pexecW i32 fu bodyP (stI P a) vec = some r ∧ r.ret = some (vec.getD a 0) ∧ r.vec = vec ∧
      r.cost ≤ 60 ∧ r.need ≤ P.length + 60 ∧ r.wk = 0 ∧ r.ps = stI P a := by
  have e1 := env_i1 P a (i32_valid a (by omega) (by omega))
  have c1 := pstmtW_check_ok i32 (stI P a) vec ck1 1 (ck1_val vec _ a e1) (by decide)
  have c2 := pstmtW_check_ok i32 (stI P a) vec (ckSz 1) 1 (ckSz_val vec _ 1 a hn e1 ha) (by decide)
  obtain ⟨xa, hxa⟩ : ∃ x, vec[a]? = some x := ⟨vec[a], by simp [ha]⟩
  have ga := hel xa (List.mem_of_getElem? hxa)
  have hga : vec.getD a 0 = xa := by simp [List.getD_eq_getElem?_getD, hxa]
  have rda : vdenL i32 vec (penv1 (stI P a)) retP = some xa := by
    rw [vdenL_read _ _ _ _ _ rfl, if_pos ⟨rfl, rfl⟩, idxcur vec P a (by omega), Option.bind_some]
    simp [elemAtL, hxa, ga]
  have rs := pstmtW_ret_ok i32 (stI P a) vec retP xa rda
  have t3 := seqW_ret (b := Sk) ((pexecW_prim i32 fu (.ret retP) _ _).trans rs) rfl
  have t2 := seqW_some ((pexecW_prim i32 fu _ _ _).trans c2) rfl t3
  have t1 := seqW_some ((pexecW_prim i32 fu _ _ _).trans c1) rfl t2
  refine ⟨_, t1, ?_, rfl, ?_, ?_, rfl, rfl⟩
  · rw [hga]
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, stI]


set_option maxHeartbeats 4000000 in
theorem cum_sum_range_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.UfRootCall.VOKI caller vslot vb V vsc m vbuf) (vec : List Int)
    (hitems : vbuf.items = vec.map Value.integer) (hn : vec.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V)
    (e1 e2 : NExpr) (a b : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (a : Int)) (value2 : e2.denote (envOf caller) = some (b : Int))
    (hab : a ≤ b) (hb : b < vec.length) (hel : ∀ y ∈ vec, i32.valid y = true)
    (hd : i32.valid (vec.getD b 0 - vec.getD a 0) = true) :
    ∃ Sinit fuel res, prepare caller Proofs.CumulativeSumInstance.CumulativeSum_int_sum_2.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum_int_sum_2.callFuel fuel caller [.vectorReference vslot,.value e1,.value e2] =
        .finished (res,.scalar (vec.getD b 0 - vec.getD a 0)) ∧
      ScalarPost3 caller Sinit res (e1.nodes+e2.nodes) 120 caller.scalars.memory 0 V vec := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_frrI caller ok e1 e2 (a : Int) (b : Int) hs1 hs2 ht1 ht2 value1 value2
      (i32_valid a (by omega) (by omega)) (i32_valid b (by omega) (by omega))
  let vc : VCtx := ⟨i32,false,m,V,vsc,vbuf,vec,hitems,fun h => absurd h (by decide),by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨rr,hexec,hret,hrvec,hcost,hneed,hwk,hps⟩ := body_exec_range (callerP caller) vec a b hn hab hb hel hd 1
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.CumulativeSumInstance.CumulativeSum_int_sum_2
    [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell),⟨i32,(b : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [VectorFillCall.take_P caller]) ok.base (by decide) 1 rr
    (by rw [body_eqR]; exact hexec) _ hret i32 rfl hd (by omega) (by simp) (e1.nodes+e2.nodes) 120 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hps]; exact VectorFillCall.take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post

set_option maxHeartbeats 4000000 in
theorem cum_sum_prefix_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.UfRootCall.VOKI caller vslot vb V vsc m vbuf) (vec : List Int)
    (hitems : vbuf.items = vec.map Value.integer) (hn : vec.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V)
    (e : NExpr) (a : Nat) (hs : e.scalarOnly = true) (ht : e.resultType = i32)
    (value : e.denote (envOf caller) = some (a : Int)) (ha : a < vec.length)
    (hel : ∀ y ∈ vec, i32.valid y = true) :
    ∃ Sinit fuel res, prepare caller Proofs.CumulativeSumInstance.CumulativeSum_int_sum_1.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum_int_sum_1.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,.scalar (vec.getD a 0)) ∧
      ScalarPost3 caller Sinit res e.nodes 120 caller.scalars.memory 0 V vec := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_fsI caller ok e (a : Int) hs ht value (i32_valid a (by omega) (by omega))
  let vc : VCtx := ⟨i32,false,m,V,vsc,vbuf,vec,hitems,fun h => absurd h (by decide),by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨rr,hexec,hret,hrvec,hcost,hneed,hwk,hps⟩ := body_exec_prefix (callerP caller) vec a hn ha hel 1
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  obtain ⟨xa, hxa⟩ : ∃ x, vec[a]? = some x := ⟨vec[a], by simp [ha]⟩
  have hga : vec.getD a 0 = xa := by simp [List.getD_eq_getElem?_getD, hxa]
  have hres : i32.valid (vec.getD a 0) = true := by rw [hga]; exact hel xa (List.mem_of_getElem? hxa)
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.CumulativeSumInstance.CumulativeSum_int_sum_1
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [VectorFillCall.take_P caller]) ok.base (by decide) 1 rr
    (by rw [body_eqP]; exact hexec) _ hret i32 rfl hres (by omega) (by simp) e.nodes 120 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hps]; simp only [stI]; exact VectorFillCall.take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post

-- With the prefix sums of `A` the result of `cum_sum_range` is the sum of `A[a, b)`.
theorem cum_sum_range_value (A cs : List Int) (hcs : ∀ i, i ≤ A.length → cs.getD i 0 = pre A i) (a b : Nat)
    (hab : a ≤ b) (hb : b ≤ A.length) : cs.getD b 0 - cs.getD a 0 = ((A.drop a).take (b - a)).sum := by
  rw [hcs b hb, hcs a (by omega)]
  exact pre_diff A a b hab

open Proofs.MultiVec Proofs.MultiVecCall Proofs.MultiKit Proofs.FenwickTreeVecCall Proofs.CumulativeSumIntExec Proofs.MatMulPrepare Proofs.FenwickTreeExec Proofs.GenState in
set_option maxHeartbeats 4000000 in
/-- `CumulativeSum<int>(v)` fills the field `cs` (already `v.size() + 1` elements long by the standard constructor)
with the prefix sums of `v`. -/
theorem cumulative_sum_from_vector_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h10 : V1 ≠ V0) (T0 V : List Int) (n : Nat) (hn : n < 2147483646) (hV : V.length = n) (hT : T0.length = n + 1)
    (hpre : ∀ q, q ≤ n → i32.valid (pre V q) = true)
    (i0 : vbuf0.items = T0.map Value.integer) (i1 : vbuf1.items = V.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (X : List Int),
      prepare caller Proofs.CumulativeSumInstance.CumulativeSum_int_new0.parameters
        [.vectorReference s0,.vectorReference s1] = some Sinit ∧
      Proofs.CumulativeSumInstance.CumulativeSum_int_new0.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1] = .finished (res,Ret.unit) ∧
      X.length = n + 1 ∧ (∀ q, q ≤ n → X.getD q 0 = pre V q) ∧
      ScalarPostM (mvFTI V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10)
        caller Sinit res 0 (220 * n + 200) caller.scalars.memory (n + 1) (VFT X V) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_ftI caller ok0 ok1
  have fwS := fwFT_initI caller ok0 ok1 h10 T0 V (by omega) (by omega) i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  have hVv := items_valid vbuf1 V i32 i1 bv1
  obtain ⟨rr,X,hexec,hret,hrps,hrvv,hXl,hXs,hcost,hneed,hwk⟩ :=
    body_execC (mvFTI V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h10) rfl (by simp [mvFTI]) (by simp [mvFTI])
      (n + 1) (callerP caller) T0 V n (by omega) hV hT hVv hpre (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm_unit (mvFTI V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h10)
    (fun k => decide (k = 0))
    (by intro k hk; have : k = 0 := by simpa using hk
        subst this; simp [mvFTI])
    caller Proofs.CumulativeSumInstance.CumulativeSum_int_new0
    [.vectorReference s0,.vectorReference s1] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by simp [callerP]) ok0.base (by decide)
    (n + 1) rr (by rw [hmk, body_eqC]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) 0 (220 * n + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,X,hprep,hrun,hXl,hXs,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.CumulativeSumIntCall
