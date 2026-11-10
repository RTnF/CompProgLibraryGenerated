import Proofs.GroupCall
import Proofs.Generated.MonoidLazy

/-! `Ty`-parametric versions of the per-type (`s64`/`i32`) caller lemmas.
Used to state the `monoid_lazy` results for an arbitrary scalar type `T`. -/

namespace Proofs.GenericCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.ModIntCall
open Proofs.PexecKit Proofs.GroupCall Proofs.DoublingCall Proofs.DoublingNested Proofs.DoublingPrologue Proofs.QuotientFrame Proofs.IntSim Proofs.ModIntExec Proofs.PowModStep Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCallCore
open Proofs.CppState (Cell)

/-- `refs2b_correct` for any scalar type `ty`. -/
theorem refs2b_gen (ty : Ty) (prog : NProgram)
    (hp : prog.parameters = [.scalar ty true false,.scalar ty true false])
    (hr : prog.result = ResultKind.scalar ty) (hbody : Scalar prog.body = true)
    (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,x⟩)) (cb : caller.scalarCell sb ty = some (bb,⟨ty,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : ty.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ = some r ∧ r.ret = some v ∧
        r.cost ≤ C ∧ r.need ≤ P.length+100 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa,.scalarReference sb] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ ty false false hp sa sb ba bb _ _ ca cb (by simp) (by simp) valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret ty hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post

theorem convG (ty : Ty) (v : Int) (h : ty.valid v = true) : ty.convert v = some v := by
  unfold Ty.convert
  by_cases hb : ty.boolean = true
  · simp only [hb, if_true]
    simp [Ty.valid, hb] at h
    rcases h with h | h <;> simp [h]
  · by_cases hs : ty.signed = true
    · simp [hb, hs, h]
    · have hb' : ty.boolean = false := by simpa using hb
      have hs' : ty.signed = false := by simpa using hs
      simp [Ty.valid, hb', hs'] at h
      simp [hb', hs']
      exact Int.emod_eq_of_lt h.1 h.2

/-- `T r = e; T t = r; return t;` after the references `R`, for any scalar type. -/
abbrev shapeG (ty : Ty) (k : Nat) (e : NExpr) : Command :=
  .sequence (.primitive (.declare ty true e))
    (.sequence (.primitive (.declare ty true (.variable ty k)))
      (.sequence (.primitive (.ret (.variable ty (k+1)))) Sk))

theorem shapeG_exec (ty : Ty) (P : List Cell) (R : List CppState.Binding) (e : NExpr) (v : Int)
    (hv : ty.valid v = true)
    (hd : e.denote (penv (ws P R [])) = some v) (hn : e.nodes ≤ 10) :
    ∃ r, pexec 1 (shapeG ty R.length e) (ws P R []) = some r ∧ r.ret = some v ∧ r.cost ≤ 20 ∧
      r.need ≤ P.length + R.length + 30 ∧ r.ps.mem = P ++ [⟨ty,v⟩,⟨ty,v⟩] := by
  have s1 := ws_declare P R [] ty e v hd (convG ty v hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e2 : penv (ws P R [⟨ty,v⟩]) (R.length + 0) ty = some v :=
    ws_env_loc P R [⟨ty,v⟩] 0 ⟨ty,v⟩ ty rfl rfl hv
  have s2 := ws_declare P R [⟨ty,v⟩] ty (.variable ty (R.length + 0)) v (by rw [den_variable]; exact e2) (convG ty v hv)
  have q2 := (pexec_prim 1 _ _).trans s2
  have e3 : penv (ws P R [⟨ty,v⟩, ⟨ty,v⟩]) (R.length + 1) ty = some v :=
    ws_env_loc P R [⟨ty,v⟩, ⟨ty,v⟩] 1 ⟨ty,v⟩ ty rfl rfl hv
  have q3 := exec_ret 1 (ws P R ([⟨ty,v⟩] ++ [⟨ty,v⟩])) (.variable ty (R.length + 1)) v (by rw [den_variable]; exact e3)
  have q23 := seq_some q2 rfl q3
  have q123 := seq_some q1 rfl q23
  refine ⟨_, q123, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]; omega
  · have := ws_size P R ([⟨ty,v⟩] ++ [⟨ty,v⟩])
    simp [NExpr.nodes, ws] at *; omega
  · simp [ws]

abbrev addG (ty : Ty) : NExpr := .binary ty .add (.variable ty 0) (.variable ty 1)

theorem addG_den (ty : Ty) (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 ty = some x) (h1 : env 1 ty = some y)
    (hxy : ty.valid (x+y) = true) : (addG ty).denote env = some (x+y) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some]
  exact convG ty _ hxy

theorem env2G (ty : Ty) (P : List Cell) (a b : Nat) (x y : Int) (hxv : ty.valid x = true) (hyv : ty.valid y = true)
    (ha : P[a]? = some ⟨ty,x⟩) (hb : P[b]? = some ⟨ty,y⟩) :
    penv (ws P [⟨a,false⟩,⟨b,false⟩] []) 0 ty = some x ∧ penv (ws P [⟨a,false⟩,⟨b,false⟩] []) 1 ty = some y :=
  ⟨ws_env_ref P _ [] 0 a false ty x rfl ha hxv, ws_env_ref P _ [] 1 b false ty y rfl hb hyv⟩

/-- `RangeAdd<T>::compose(f, g)` as a program family in the scalar type. -/
def composeAdd (ty : Ty) : NProgram :=
  ⟨[.scalar ty true false, .scalar ty true false], .scalar ty,
    (.sequence (.primitive (.declare ty true (.binary ty .add (.variable ty 0) (.variable ty 1))))
      (.sequence (.primitive (.declare ty true (.variable ty 2)))
        (.sequence (.primitive (.ret (.variable ty 3))) (.primitive .skip))))⟩

theorem composeAdd_s64 : composeAdd s64 = Proofs.MonoidLazyInstance.compose_RangeAdd_long_long := rfl

theorem composeAdd_body (ty : Ty) : (composeAdd ty).body = shapeG ty 2 (addG ty) := rfl

theorem P_cellG (ty : Ty) (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,x⟩)) : (callerP caller)[ba.address]? = some ⟨ty,x⟩ := by
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma

theorem composeAdd_scalar (ty : Ty) : Scalar (composeAdd ty).body = true := by
  simp [composeAdd, Scalar, NExpr.scalarOnly]

/-- `RangeAdd<T>::compose` for any scalar type `T` whose sum stays representable. -/
theorem rangeadd_compose_gen (ty : Ty) (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (hxv : ty.valid x = true) (hyv : ty.valid y = true) (hxy : ty.valid (x+y) = true)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,x⟩)) (cb : caller.scalarCell sb ty = some (bb,⟨ty,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (composeAdd ty).parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      (composeAdd ty).callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (x+y)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  refine refs2b_gen ty _ rfl rfl (composeAdd_scalar ty) caller sa sb ba bb x y ca cb valid lengths strict base 1 (x+y) hxy 20 ?_
  intro P hP
  subst hP
  have ⟨e0, e1⟩ := env2G ty (callerP caller) ba.address bb.address x y hxv hyv (P_cellG ty caller sa ba x ca) (P_cellG ty caller sb bb y cb)
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeG_exec ty (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] (addG ty) (x+y) hxy
    (addG_den ty _ x y e0 e1 hxy) (by simp [NExpr.nodes])
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

/-- The result of a representation conversion is representable. -/
theorem convert_valid (ty : Ty) (z w : Int) (h : ty.convert z = some w) : ty.valid w = true := by
  by_cases hb : ty.boolean = true
  · simp [Ty.convert, hb] at h
    subst h
    split <;> simp [Ty.valid, hb]
  · by_cases hs : ty.signed = true
    · simp [Ty.convert, hb, hs] at h
      obtain ⟨hz, rfl⟩ := h
      exact hz
    · simp [Ty.convert, hb, hs] at h
      subst h
      have pos : (0 : Int) < 2 ^ ty.width := Int.pow_pos (by decide)
      have h0 : 0 ≤ z % 2 ^ ty.width := Int.emod_nonneg _ (by omega)
      have h1 : z % 2 ^ ty.width < 2 ^ ty.width := Int.emod_lt_of_pos _ pos
      simp [Ty.valid, hb, hs, h0, h1]

/-- Unsigned arithmetic wraps modulo `2^width`. -/
theorem convert_wrap (ty : Ty) (z : Int) (hb : ty.boolean = false) (hu : ty.signed = false) :
    ty.convert z = some (z % 2 ^ ty.width) := by
  simp [Ty.convert, hb, hu]

theorem addG_den_conv (ty : Ty) (env : Nat → Ty → Option Int) (x y s : Int) (h0 : env 0 ty = some x)
    (h1 : env 1 ty = some y) (hc : ty.convert (x+y) = some s) : (addG ty).denote env = some s := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simpa [binaryValue] using hc

/-- `RangeAdd<T>::compose` with the sum converted to `T` (wraps for unsigned `T`). -/
theorem rangeadd_compose_conv_gen (ty : Ty) (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y s : Int)
    (hxv : ty.valid x = true) (hyv : ty.valid y = true) (hc : ty.convert (x+y) = some s)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,x⟩)) (cb : caller.scalarCell sb ty = some (bb,⟨ty,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (composeAdd ty).parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      (composeAdd ty).callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar s) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  have hs := convert_valid ty _ _ hc
  refine refs2b_gen ty _ rfl rfl (composeAdd_scalar ty) caller sa sb ba bb x y ca cb valid lengths strict base 1 s hs 20 ?_
  intro P hP
  subst hP
  have ⟨e0, e1⟩ := env2G ty (callerP caller) ba.address bb.address x y hxv hyv (P_cellG ty caller sa ba x ca) (P_cellG ty caller sb bb y cb)
  obtain ⟨r,h1,h2,h3,h4,h5⟩ := shapeG_exec ty (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] (addG ty) s hs
    (addG_den_conv ty _ x y s e0 e1 hc) (by simp [NExpr.nodes])
  rw [ws_nil] at h1
  exact ⟨r,h1,h2,h3,by simp at h4; omega,by rw [h5]; exact take_P caller _⟩

/-- Signed overflow of the sum is refused: the callee body faults. -/
theorem addG_den_overflow (ty : Ty) (env : Nat → Ty → Option Int) (x y : Int) (h0 : env 0 ty = some x)
    (h1 : env 1 ty = some y) (hb : ty.boolean = false) (hsg : ty.signed = true)
    (hbad : ty.valid (x+y) = false) : (addG ty).denote env = none := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp [binaryValue, Ty.convert, hb, hsg, hbad]

end Proofs.GenericCall
