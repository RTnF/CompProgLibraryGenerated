import Proofs.Generated.Xorshift
import Proofs.ExtremaCall
import Proofs.StraightLine
import Proofs.ScalarStraight
import Proofs.ModIntCall

namespace Proofs.XorshiftCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.StraightLine
open Proofs.QuotientSearch Proofs.Mod61Body Proofs.DoublingNested
open Proofs.CppState (Cell)

def sh7 (x : Nat) : Nat := x * 128 % 2^64
def step1 (s : Nat) : Nat := s ^^^ sh7 s
def xnext (s : Nat) : Nat := step1 s ^^^ (step1 s >>> 9)

abbrev xE1 : NExpr := .binary u64 .bxor (.variable u64 1) (.binary u64 .shl (.variable u64 1) (.literal i32 7))
abbrev xE2 : NExpr := .binary u64 .bxor (.variable u64 1) (.binary u64 .shr (.variable u64 1) (.literal i32 9))

theorem sh7_lt (x : Nat) : sh7 x < 2^64 := Nat.mod_lt _ (by decide)

theorem step1_lt (s : Nat) (hs : s < 2^64) : step1 s < 2^64 := Nat.xor_lt_two_pow hs (sh7_lt s)

theorem xnext_lt (s : Nat) (hs : s < 2^64) : xnext s < 2^64 :=
  Nat.xor_lt_two_pow (step1_lt s hs) (by
    have : step1 s >>> 9 ≤ step1 s := Nat.shiftRight_le _ _
    have := step1_lt s hs
    omega)

theorem xE1_value (env : Nat → Ty → Option Int) (x : Nat) (hx : x < 2^64)
    (h : env 1 u64 = some (x : Int)) : xE1.denote env = some ((step1 x : Nat) : Int) := by
  have l7 : i32.valid 7 = true := by simp [Ty.valid]
  have v1 : u64.valid ((step1 x : Nat) : Int) = true := u64_lt _ (by have := step1_lt x hx; omega)
  have v2 : u64.valid ((sh7 x : Nat) : Int) = true := u64_lt _ (by have := sh7_lt x; omega)
  rw [den_binary,den_variable,den_binary,den_variable,h]
  simp only [NExpr.denote,l7,if_true,Option.bind_some,binaryValue]
  have c1 : u64.convert ((x : Int) * 2 ^ Int.toNat 7) = some ((sh7 x : Nat) : Int) := by
    have : ((x : Int) * 2 ^ Int.toNat 7) = ((x * 128 : Nat) : Int) := by simp
    rw [this]
    simp only [Ty.convert, sh7]
    simp
  rw [c1]
  simp only [Option.bind_some, Int.toNat_natCast]
  exact Ty.convert_of_valid _ _ (by simpa [step1] using v1)


theorem xE2_value (env : Nat → Ty → Option Int) (x : Nat) (hx : x < 2^64)
    (h : env 1 u64 = some (x : Int)) : xE2.denote env = some ((x ^^^ (x >>> 9) : Nat) : Int) := by
  have l9 : i32.valid 9 = true := by simp [Ty.valid]
  have v1 : u64.valid ((x >>> 9 : Nat) : Int) = true := u64_lt _ (by have := Nat.shiftRight_le x 9; omega)
  have v2 : u64.valid ((x ^^^ (x >>> 9) : Nat) : Int) = true := u64_lt _ (by
    have := Nat.xor_lt_two_pow hx (show x >>> 9 < 2^64 by have := Nat.shiftRight_le x 9; omega); omega)
  rw [den_binary,den_variable,den_binary,den_variable,h]
  simp only [NExpr.denote,l9,if_true,Option.bind_some,binaryValue]
  have c1 : u64.convert ((((x : Nat) : Int).toNat >>> (Int.toNat 9) : Nat) : Int) = some ((x >>> 9 : Nat) : Int) := by
    simpa using Ty.convert_of_valid _ _ v1
  rw [c1]
  simp only [Option.bind_some, Int.toNat_natCast]
  exact Ty.convert_of_valid _ _ v2

theorem penv_at (ps : PS) (i : Nat) (ty : Ty) (b : CppState.Binding) (c : Cell) (hb : ps.bs[i]? = some b)
    (hc : ps.mem[b.address]? = some c) (ht : c.type = ty) (hv : ty.valid c.value = true) :
    penv ps i ty = some c.value := by
  simp [penv, hb, hc, ht, hv]


abbrev XSk : Command := .primitive .skip

theorem body_eq : Proofs.XorshiftInstance.Xor64_get.body =
    .sequence (.primitive (.declare u64 true (.variable u64 0))) (.sequence (.primitive (.assign 1 u64 xE1))
      (.sequence (.primitive (.assign 0 u64 xE2)) (.sequence (.primitive (.ret (.variable u64 0))) XSk))) := rfl

theorem pexec_prim (fu : Nat) (st : NStmt) (ps : PS) : pexec fu (.primitive st) ps = pstmt st ps := by
  rw [pexec]

theorem pexec_seq (fu : Nat) (a b : Command) (ps : PS) : pexec fu (.sequence a b) ps = (do
      let r ← pexec fu a ps
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexec fu b r.ps
          some ⟨r2.ps,r2.ret,r.cost+r2.cost,max r.need r2.need⟩) := by
  rw [pexec]
  congr

theorem seq_some {fu : Nat} {a b : Command} {ps : PS} {r r2 : PR} (h1 : pexec fu a ps = some r) (hr : r.ret = none)
    (h2 : pexec fu b r.ps = some r2) :
    pexec fu (.sequence a b) ps = some ⟨r2.ps,r2.ret,r.cost+r2.cost,max r.need r2.need⟩ := by
  rw [pexec_seq, h1]
  simp only [Bind.bind, Option.bind, hr, h2]

theorem seq_ret {fu : Nat} {a b : Command} {ps : PS} {r : PR} {v : Int} (h1 : pexec fu a ps = some r)
    (hr : r.ret = some v) : pexec fu (.sequence a b) ps = some r := by
  rw [pexec_seq, h1]
  simp only [Bind.bind, Option.bind, hr]

theorem set_last (P : List Cell) (c v : Cell) : (P ++ [c]).set P.length v = P ++ [v] := by
  rw [List.set_append_right _ _ (Nat.le_refl _)]
  simp

theorem xor_exec (P : List Cell) (a s : Nat) (hs : s < 2^64) (ha : a < P.length) (hPa : P[a]? = some ⟨u64,(s : Int)⟩) :
    ∃ r, pexec 1 Proofs.XorshiftInstance.Xor64_get.body ⟨P,[⟨a,true⟩]⟩ = some r ∧
      r.ret = some ((xnext s : Nat) : Int) ∧ r.cost ≤ 60 ∧ r.need ≤ P.length+12 ∧
      r.ps = ⟨(P.set a ⟨u64,((xnext s : Nat) : Int)⟩) ++ [⟨u64,((step1 s : Nat) : Int)⟩],
        [⟨a,true⟩,⟨P.length,true⟩]⟩ := by
  have hs' : u64.valid (s : Int) = true := u64_lt s (by omega)
  have e0 : penv ⟨P,[⟨a,true⟩]⟩ 0 u64 = some (s : Int) :=
    penv_at _ 0 u64 ⟨a,true⟩ ⟨u64,(s : Int)⟩ rfl hPa rfl hs'
  have p1 : pstmt (.declare u64 true (.variable u64 0)) ⟨P,[⟨a,true⟩]⟩ =
      some ⟨⟨P ++ [⟨u64,(s : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩,none,2,P.length+1+1+4⟩ := by
    simp only [pstmt,Bind.bind,Option.bind,den_variable,e0,Ty.convert_of_valid _ _ hs']
    simp [NExpr.nodes]
  have hx1 : step1 s < 2^64 := step1_lt s hs
  have hx2 : u64.valid ((step1 s : Nat) : Int) = true := u64_lt _ (by omega)
  have hxn : xnext s < 2^64 := xnext_lt s hs
  have hx3 : u64.valid ((xnext s : Nat) : Int) = true := u64_lt _ (by omega)
  have cellS : (P ++ [(⟨u64,(s : Int)⟩ : Cell)])[P.length]? = some ⟨u64,(s : Int)⟩ := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  have e1 : penv ⟨P ++ [⟨u64,(s : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩ 1 u64 = some (s : Int) :=
    penv_at _ 1 u64 ⟨P.length,true⟩ ⟨u64,(s : Int)⟩ rfl cellS rfl hs'
  have d1 := xE1_value (penv ⟨P ++ [⟨u64,(s : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩) s hs e1
  have p2 : pstmt (.assign 1 u64 xE1) ⟨P ++ [⟨u64,(s : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩ =
      some ⟨⟨P ++ [⟨u64,((step1 s : Nat) : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩,none,xE1.nodes+1,
        (P.length+1)+2+xE1.nodes+2⟩ := by
    simp only [pstmt,Bind.bind,Option.bind,d1]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, cellS, Ty.convert_of_valid _ _ hx2, set_last]
    simp [hs']
  have cellA : (P ++ [(⟨u64,((step1 s : Nat) : Int)⟩ : Cell)])[a]? = some ⟨u64,(s : Int)⟩ := by
    rw [List.getElem?_append_left ha]; exact hPa
  have cellB : (P ++ [(⟨u64,((step1 s : Nat) : Int)⟩ : Cell)])[P.length]? = some ⟨u64,((step1 s : Nat) : Int)⟩ := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  have e2 : penv ⟨P ++ [⟨u64,((step1 s : Nat) : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩ 1 u64 =
      some ((step1 s : Nat) : Int) :=
    penv_at _ 1 u64 ⟨P.length,true⟩ ⟨u64,((step1 s : Nat) : Int)⟩ rfl cellB rfl hx2
  have d2 := xE2_value (penv ⟨P ++ [⟨u64,((step1 s : Nat) : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩) (step1 s) hx1 e2
  have p3 : pstmt (.assign 0 u64 xE2) ⟨P ++ [⟨u64,((step1 s : Nat) : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩ =
      some ⟨⟨(P.set a ⟨u64,((xnext s : Nat) : Int)⟩) ++ [⟨u64,((step1 s : Nat) : Int)⟩],
        [⟨a,true⟩,⟨P.length,true⟩]⟩,none,xE2.nodes+1,(P.length+1)+2+xE2.nodes+2⟩ := by
    simp only [pstmt,Bind.bind,Option.bind,d2]
    have hx3' : u64.valid ((step1 s ^^^ (step1 s >>> 9) : Nat) : Int) = true := hx3
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, cellA, Ty.convert_of_valid _ _ hx3',
      List.set_append_left a _ ha]
    simp [hs', xnext]
  have cellR : ((P.set a ⟨u64,((xnext s : Nat) : Int)⟩) ++ [(⟨u64,((step1 s : Nat) : Int)⟩ : Cell)])[a]? =
      some ⟨u64,((xnext s : Nat) : Int)⟩ := by
    rw [List.getElem?_append_left (by simpa using ha)]
    simp [List.getElem?_set_self ha]
  have e3 : penv ⟨(P.set a ⟨u64,((xnext s : Nat) : Int)⟩) ++ [⟨u64,((step1 s : Nat) : Int)⟩],
      [⟨a,true⟩,⟨P.length,true⟩]⟩ 0 u64 = some ((xnext s : Nat) : Int) :=
    penv_at _ 0 u64 ⟨a,true⟩ ⟨u64,((xnext s : Nat) : Int)⟩ rfl cellR rfl hx3
  have p4 : pstmt (.ret (.variable u64 0)) ⟨(P.set a ⟨u64,((xnext s : Nat) : Int)⟩) ++ [⟨u64,((step1 s : Nat) : Int)⟩],
      [⟨a,true⟩,⟨P.length,true⟩]⟩ = some ⟨⟨(P.set a ⟨u64,((xnext s : Nat) : Int)⟩) ++ [⟨u64,((step1 s : Nat) : Int)⟩],
      [⟨a,true⟩,⟨P.length,true⟩]⟩,some ((xnext s : Nat) : Int),2,(P.length+1)+2+1+2⟩ := by
    simp only [pstmt,Bind.bind,Option.bind,den_variable,e3]
    simp [NExpr.nodes]
  have q4 := seq_ret (fu := 1) (b := XSk) (a := .primitive (.ret (.variable u64 0)))
    (by rw [pexec_prim]; exact p4) rfl
  have h3 := pexec_prim 1 (.assign 0 u64 xE2) ⟨P ++ [⟨u64,((step1 s : Nat) : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩
  rw [p3] at h3
  have q3 := seq_some h3 rfl q4
  have h2 := pexec_prim 1 (.assign 1 u64 xE1) ⟨P ++ [⟨u64,(s : Int)⟩],[⟨a,true⟩,⟨P.length,true⟩]⟩
  rw [p2] at h2
  have q2 := seq_some h2 rfl q3
  have h1 := pexec_prim 1 (.declare u64 true (.variable u64 0)) ⟨P,[⟨a,true⟩]⟩
  rw [p1] at h1
  have q1 := seq_some h1 rfl q2
  rw [← body_eq] at q1
  refine ⟨_,q1,rfl,?_,?_,rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]


open Proofs.ExtremaCall Proofs.ScalarCall Proofs.ScalarStraight Proofs.DoublingCall Proofs.CppNestedSim in
theorem prepare_xor (caller : NState) (sa : Nat) (ba : CppState.Binding) (va : Int)
    (ca : caller.scalarCell sa u64 = some (ba,⟨u64,va⟩)) (wa : ba.writable = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller Proofs.XorshiftInstance.Xor64_get.parameters [.scalarReference sa] = some Sinit ∧
      Sinit.slots = [.scalar 0] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [ba] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨ia,_,_,hma,_,vva⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hma' : (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell))[ba.address]? = some ⟨u64,va⟩ := by rw [List.getElem?_append_left lta]; exact hma
  have hparams : Proofs.XorshiftInstance.Xor64_get.parameters = [.scalar u64 true true] := rfl
  rw [hparams]
  simp [prepare,valid,resolveAll,resolve,ca,wa]
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,hma',vva]
  refine ⟨?_,rfl,?_⟩
  · cases ba; simp at wa ⊢; exact wa
  · simp only [charge_scalar_peak]
    omega


open Proofs.ExtremaCall Proofs.ScalarCall Proofs.ScalarStraight Proofs.DoublingCall Proofs.CppNestedSim in
theorem xor64_get_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (va : Nat) (hva : va < 2^64)
    (ca : caller.scalarCell sa u64 = some (ba,⟨u64,(va : Int)⟩)) (wa : ba.writable = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.XorshiftInstance.Xor64_get.parameters [.scalarReference sa] = some Sinit ∧
      Proofs.XorshiftInstance.Xor64_get.callFuel fuel caller [.scalarReference sa] =
        .finished (res,.scalar ((xnext va : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70 (caller.scalars.memory.set ba.address ⟨u64,((xnext va : Nat) : Int)⟩) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_xor caller sa ba _ ca wa valid
  obtain ⟨ia,_,_,hma,_,vva⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u64,(va : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := xor_exec (callerP caller) ba.address va hva hlt hPa
  have hba : ba = ⟨ba.address,true⟩ := by cases ba; simp at wa ⊢; exact wa
  have hxn : xnext va < 2^64 := xnext_lt va hva
  have spC : caller.scalars.peak ≤ Sinit.scalars.peak := sPeak
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have hpost := call_scalar caller Proofs.XorshiftInstance.Xor64_get [.scalarReference sa] Sinit (callerP caller) [ba]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame spC (by omega) (by rw [takeM])
    valid lengths strict base (by decide) 1 r (by rw [hba] at *; exact hexec) ((xnext va : Nat) : Int) hret u64 rfl
    (u64_lt _ (by omega)) (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length =
      caller.scalars.memory.set ba.address ⟨u64,((xnext va : Nat) : Int)⟩ := by
    rw [hrps]
    exact take_set_memory _ _ _ _ _ lta
  rw [hs] at post; exact post


open Proofs.ModIntCall Proofs.ModIntExec Proofs.PexecKit Proofs.ScalarCall Proofs.ScalarStraight Proofs.DoublingCall Proofs.CppNestedEval Proofs.PowModStep in
-- The constructor `Xor64(s)`: the new object holds exactly `s`.
theorem xor64_new_correct (caller : NState) (e : NExpr) (s : Nat) (hs : e.scalarOnly = true) (hty : e.resultType = u64)
    (value : e.denote (envOf caller) = some (s : Int)) (hv : s < 18446744073709551616)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.XorshiftInstance.Xor64_new0.parameters [.value e] = some Sinit ∧
      Proofs.XorshiftInstance.Xor64_new0.callFuel fuel caller [.value e] = .finished (res,.scalar (s : Int)) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeak0⟩ :=
    prep_val caller _ u64 rfl e (s : Int) hs hty value valid (u64_valid_nat s hv)
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have e0 : penv ⟨callerP caller ++ [⟨u64,(s : Int)⟩],[⟨(callerP caller).length,true⟩]⟩ 0 u64 = some (s : Int) :=
    penv_ok _ 0 u64 ⟨(callerP caller).length,true⟩ ⟨u64,(s : Int)⟩ rfl (by simpa using get_tail (callerP caller) [⟨u64,(s : Int)⟩] 0) rfl
      (u64_valid_nat s hv)
  have q := exec_ret 1 _ (.variable u64 0) _ (by rw [den_variable]; exact e0)
  have body_eq : Proofs.XorshiftInstance.Xor64_new0.body = .sequence (.primitive (.ret (.variable u64 0))) Sk := rfl
  have gw := good.2.2.1
  have takeM2 : (callerP caller ++ [(⟨u64,(s : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    rw [List.take_append_of_le_length (by omega)]; exact takeM
  have hpost := call_scalar caller Proofs.XorshiftInstance.Xor64_new0 [.value e] Sinit
    (callerP caller ++ [⟨u64,(s : Int)⟩]) [⟨(callerP caller).length,true⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame
    (by omega) (by simp; omega) (by rw [takeM2]) valid lengths strict base (by rw [body_eq]; rfl) 1 _ (by rw [body_eq]; exact q) _ rfl
    u64 rfl (u64_valid_nat s hv) (by simp [NExpr.nodes]) (by simp) e.nodes 70 (by simp [NExpr.nodes]; omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simpa [takeM2] using post

end Proofs.XorshiftCall
