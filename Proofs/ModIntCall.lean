import Proofs.ModIntPow
import Proofs.ScalarStraight
import Proofs.ExtremaCall
import Proofs.Fermat
import Proofs.ShiftState

namespace Proofs.ModIntCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.ExtremaCall Proofs.IntSim
open Proofs.CppState (Cell)

theorem prep_ref1 (caller : NState) (params : List CppVectorBindings.Parameter) (ty : Ty) (w : Bool)
    (hp : params = [.scalar ty true w]) (sa : Nat) (ba : CppState.Binding) (va : Int)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,va⟩)) (wa : w = true → ba.writable = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference sa] = some Sinit ∧
      Sinit.slots = [.scalar 0] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨ba.address,w⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨ia,_,_,hma,hct,vva⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hma' : (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell))[ba.address]? = some ⟨ty,va⟩ := by rw [List.getElem?_append_left lta]; exact hma
  rw [hp]
  have wa' : (w = true → ba.writable = true) = True := eq_true wa
  simp [prepare,valid,resolveAll,resolve,ca,wa']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,hma',vva]
  refine ⟨rfl,?_⟩
  simp only [charge_scalar_peak]
  omega


theorem prep_ref2 (caller : NState) (params : List CppVectorBindings.Parameter) (ty : Ty) (w1 w2 : Bool)
    (hp : params = [.scalar ty true w1,.scalar ty true w2]) (sa sb : Nat) (ba bb : CppState.Binding) (va vb : Int)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,va⟩)) (cb : caller.scalarCell sb ty = some (bb,⟨ty,vb⟩))
    (wa : w1 = true → ba.writable = true) (wb : w2 = true → bb.writable = true)
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨ba.address,w1⟩,⟨bb.address,w2⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+5 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have cb' : (caller.charge 1 1).scalarCell sb ty = some (bb,⟨ty,vb⟩) := cb
  obtain ⟨ia,_,_,hma,_,vva⟩ := scalarCell_facts ca
  obtain ⟨ib,_,_,hmb,_,vvb⟩ := scalarCell_facts cb
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hma' : (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell))[ba.address]? = some ⟨ty,va⟩ := by rw [List.getElem?_append_left lta]; exact hma
  have hmb' : (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell))[bb.address]? = some ⟨ty,vb⟩ := by rw [List.getElem?_append_left ltb]; exact hmb
  have wa' : (w1 = true → ba.writable = true) = True := eq_true wa
  have wb' : (w2 = true → bb.writable = true) = True := eq_true wb
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,ca,cb',wa',wb']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,hma',hmb',vva,vvb]
  refine ⟨rfl,?_⟩
  simp only [charge_scalar_peak]
  omega


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem add_assign_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (caller : NState) (sa sb : Nat)
    (ba bb : CppState.Binding) (x y : Nat) (hx : x < m) (hy : y < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩)) (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_add_assign m).parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_add_assign m).callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (((x + y) % m : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70
        (caller.scalars.memory.set ba.address ⟨u32,(((x + y) % m : Nat) : Int)⟩) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ u32 true false rfl sa sb ba bb _ _ ca cb (fun _ => wa) (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  obtain ⟨ib,_,_,hmb,_,_⟩ := scalarCell_facts cb
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hPb : (callerP caller)[bb.address]? = some ⟨u32,(y : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left ltb]; exact hmb
  have hlt : ba.address < (callerP caller).length := by omega
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := add_assign_exec m hm hm2 (callerP caller) ba.address bb.address x y hx hy hPa hPb hlt
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have hres : (x + y) % m < 4294967296 := by have := Nat.mod_lt (x + y) (show 0 < m by omega); omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_add_assign m) [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,true⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length =
      caller.scalars.memory.set ba.address ⟨u32,(((x + y) % m : Nat) : Int)⟩ := by
    rw [hrps]
    have := take_set_memory caller.scalars.memory (List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell)) [] ba.address ⟨u32,(((x + y) % m : Nat) : Int)⟩ lta
    simpa [callerP] using this
  rw [hs] at post
  exact post


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem sub_assign_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (caller : NState) (sa sb : Nat)
    (ba bb : CppState.Binding) (x y : Nat) (hx : x < m) (hy : y < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩)) (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_sub_assign m).parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_sub_assign m).callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((((x + m - y) % m) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70
        (caller.scalars.memory.set ba.address ⟨u32,((((x + m - y) % m) : Nat) : Int)⟩) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ u32 true false rfl sa sb ba bb _ _ ca cb (fun _ => wa) (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨ib,_,_,hmb,_,_⟩ := scalarCell_facts cb
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hPb : (callerP caller)[bb.address]? = some ⟨u32,(y : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left ltb]; exact hmb
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := sub_assign_exec m hm (by omega) (callerP caller) ba.address bb.address x y hx hy hPa hPb hlt
  have hres : ((x + m - y) % m) < 4294967296 := by have := Nat.mod_lt (x + m - y) (show 0 < m by omega); omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_sub_assign m) [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,true⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length =
      caller.scalars.memory.set ba.address ⟨u32,((((x + m - y) % m) : Nat) : Int)⟩ := by
    rw [hrps]
    have := take_set_memory caller.scalars.memory (List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell)) [] ba.address ⟨u32,((((x + m - y) % m) : Nat) : Int)⟩ lta
    simpa [callerP] using this
  rw [hs] at post
  exact post

open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem mul_assign_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (sa sb : Nat)
    (ba bb : CppState.Binding) (x y : Nat) (hx : x < m) (hy : y < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩)) (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_mul_assign m).parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_mul_assign m).callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar (((x * y % m) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70
        (caller.scalars.memory.set ba.address ⟨u32,(((x * y % m) : Nat) : Int)⟩) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ u32 true false rfl sa sb ba bb _ _ ca cb (fun _ => wa) (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨ib,_,_,hmb,_,_⟩ := scalarCell_facts cb
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hPb : (callerP caller)[bb.address]? = some ⟨u32,(y : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left ltb]; exact hmb
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := mul_assign_exec m hm hm2 (callerP caller) ba.address bb.address x y hx hy hPa hPb hlt
  have hres : (x * y % m) < 4294967296 := by have := Nat.mod_lt (x * y) (show 0 < m by omega); omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_mul_assign m) [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,true⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length =
      caller.scalars.memory.set ba.address ⟨u32,(((x * y % m) : Nat) : Int)⟩ := by
    rw [hrps]
    have := take_set_memory caller.scalars.memory (List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell)) [] ba.address ⟨u32,(((x * y % m) : Nat) : Int)⟩ lta
    simpa [callerP] using this
  rw [hs] at post
  exact post


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem increment_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (sa : Nat)
    (ba : CppState.Binding) (x : Nat) (hx : x < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_increment m).parameters
        [.scalarReference sa] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_increment m).callFuel fuel caller [.scalarReference sa] =
        .finished (res,.scalar ((((x + 1) % m) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70
        (caller.scalars.memory.set ba.address ⟨u32,((((x + 1) % m) : Nat) : Int)⟩) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref1 caller _ u32 true rfl sa ba _ ca (fun _ => wa) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := increment_exec m hm hm2 (callerP caller) ba.address x hx hPa hlt
  have hres : ((x + 1) % m) < 4294967296 := by have := Nat.mod_lt (x + 1) (show 0 < m by omega); omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_increment m) [.scalarReference sa] Sinit
    (callerP caller) [⟨ba.address,true⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length =
      caller.scalars.memory.set ba.address ⟨u32,((((x + 1) % m) : Nat) : Int)⟩ := by
    rw [hrps]
    have := take_set_memory caller.scalars.memory (List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell)) [] ba.address ⟨u32,((((x + 1) % m) : Nat) : Int)⟩ lta
    simpa [callerP] using this
  rw [hs] at post
  exact post

open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem decrement_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (sa : Nat)
    (ba : CppState.Binding) (x : Nat) (hx : x < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_decrement m).parameters
        [.scalarReference sa] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_decrement m).callFuel fuel caller [.scalarReference sa] =
        .finished (res,.scalar ((((x + m - 1) % m) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70
        (caller.scalars.memory.set ba.address ⟨u32,((((x + m - 1) % m) : Nat) : Int)⟩) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref1 caller _ u32 true rfl sa ba _ ca (fun _ => wa) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := decrement_exec m hm hm2 (callerP caller) ba.address x hx hPa hlt
  have hres : ((x + m - 1) % m) < 4294967296 := by have := Nat.mod_lt (x + m - 1) (show 0 < m by omega); omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_decrement m) [.scalarReference sa] Sinit
    (callerP caller) [⟨ba.address,true⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length =
      caller.scalars.memory.set ba.address ⟨u32,((((x + m - 1) % m) : Nat) : Int)⟩ := by
    rw [hrps]
    have := take_set_memory caller.scalars.memory (List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell)) [] ba.address ⟨u32,((((x + m - 1) % m) : Nat) : Int)⟩ lta
    simpa [callerP] using this
  rw [hs] at post
  exact post


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem get_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (sa : Nat)
    (ba : CppState.Binding) (x : Nat) (hx : x < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_get m).parameters
        [.scalarReference sa] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_get m).callFuel fuel caller [.scalarReference sa] =
        .finished (res,.scalar ((x : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref1 caller _ u32 false rfl sa ba _ ca (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := get_exec m (callerP caller) ba.address x hx hm2 hPa
  have hres : x < 4294967296 := by omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_get m) [.scalarReference sa] Sinit
    (callerP caller) [⟨ba.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]; exact takeM
  rw [hs] at post
  exact post

open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem sub_unary_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (sa : Nat)
    (ba : CppState.Binding) (x : Nat) (hx : x < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_sub_unary m).parameters
        [.scalarReference sa] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_sub_unary m).callFuel fuel caller [.scalarReference sa] =
        .finished (res,.scalar (((if x = 0 then 0 else m - x) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref1 caller _ u32 false rfl sa ba _ ca (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hL⟩ := neg_exec m hm hm2 (callerP caller) ba.address x hx hPa hlt
  have hres : (if x = 0 then 0 else m - x) < 4294967296 := by split <;> omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_sub_unary m) [.scalarReference sa] Sinit
    (callerP caller) [⟨ba.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    obtain ⟨L,hL'⟩ := hL
    rw [hL', List.take_append_of_le_length (by omega)]; exact takeM
  rw [hs] at post
  exact post


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem eq_correct (m : Nat) (hm2 : m < 4294967296) (caller : NState) (sa sb : Nat)
    (ba bb : CppState.Binding) (x y : Nat) (hx : x < m) (hy : y < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩)) (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_eq m).parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_eq m).callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((if x = y then 1 else 0) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ u32 false false rfl sa sb ba bb _ _ ca cb (by simp) (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨ib,_,_,hmb,_,_⟩ := scalarCell_facts cb
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hPb : (callerP caller)[bb.address]? = some ⟨u32,(y : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left ltb]; exact hmb
  have hlen' : ba.address < (callerP caller).length := by omega
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := eq_exec m (callerP caller) ba.address bb.address x y hx hy hm2 hPa hPb
  have hres : bl.valid ((if x = y then 1 else 0) : Int) = true := by split <;> simp [Ty.valid]
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_eq m) [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret bl rfl hres
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]; exact takeM
  rw [hs] at post
  exact post

open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem ne_correct (m : Nat) (hm2 : m < 4294967296) (caller : NState) (sa sb : Nat)
    (ba bb : CppState.Binding) (x y : Nat) (hx : x < m) (hy : y < m)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩)) (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_ne m).parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_ne m).callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((if x = y then 0 else 1) : Int)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ u32 false false rfl sa sb ba bb _ _ ca cb (by simp) (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨ib,_,_,hmb,_,_⟩ := scalarCell_facts cb
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hPb : (callerP caller)[bb.address]? = some ⟨u32,(y : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left ltb]; exact hmb
  have hlen' : ba.address < (callerP caller).length := by omega
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := ne_exec m (callerP caller) ba.address bb.address x y hx hy hm2 hPa hPb
  have hres : bl.valid ((if x = y then 0 else 1) : Int) = true := by split <;> simp [Ty.valid]
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_ne m) [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,false⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret bl rfl hres
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]; exact takeM
  rw [hs] at post
  exact post


theorem prep_none (caller : NState) (params : List CppVectorBindings.Parameter) (hp : params = [])
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [] = some Sinit ∧
      Sinit.slots = [] ∧ Sinit.scalars.memory = callerP caller ∧ Sinit.scalars.bindings = [] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+1 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  rw [hp]
  simp [prepare,valid,resolveAll,bindAll,callerP,NState.observe]


theorem prep_val (caller : NState) (params : List CppVectorBindings.Parameter) (ty : Ty)
    (hp : params = [.scalar ty false true]) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = ty) (value : e.denote (envOf caller) = some v)
    (valid : caller.frame.state.wellFormed = true) (nv : ty.valid v = true) :
    ∃ t, Good caller t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller params [.value e] = some Sinit ∧
        Sinit.slots = [.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨ty,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+2 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ t.scalars.peak := by
  obtain ⟨t,ran,good⟩ := scalar_eval e caller v hs value
  refine ⟨t,good,?_⟩
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have res : resolve caller (.scalar ty false true) (.value e) = some (t,.scalar ty true v) := by
    simp [resolve,hty,ran]
  rw [hp]
  simp [prepare,valid,resolveAll,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,nv,callerP,
    NState.observe,CppState.State.observe]
  refine ⟨Nat.le_max_left _ _,?_⟩
  have := good.2.2.2.2.1
  omega


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem new0_correct (m : Nat) (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_new0 m).parameters [] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_new0 m).callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prep_none caller _ rfl valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := new0_exec m (callerP caller)
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_new0 m) [] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl (u32_valid_nat 0 (by omega))
    (by omega) (by simp) 0 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]; exact takeM
  rw [hs] at post
  exact post

open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine in
theorem new1_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_new1 m).parameters [.value e] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_new1 m).callFuel fuel caller [.value e] = .finished (res,.scalar (v % (m : Int))) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeak0⟩ :=
    prep_val caller _ s64 rfl e v hs hty value valid hv
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := new1_exec m (by omega) hm2 (callerP caller) v hv
  have hres : u32.valid (v % (m : Int)) = true := by
    have h1 := Int.emod_nonneg v (show (m : Int) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos v (show (0 : Int) < (m : Int) by omega)
    rw [valid_u32]; exact decide_eq_true ⟨h1, by omega⟩
  have gw := good.2.2.1
  have takeM2 : (callerP caller ++ [(⟨s64,v⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    rw [List.take_append_of_le_length (by omega)]; exact takeM
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_new1 m) [.value e] Sinit
    (callerP caller ++ [⟨s64,v⟩]) [⟨(callerP caller).length,true⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame
    (by omega) (by simp; omega) (by rw [takeM2]) valid lengths strict base rfl 1 r hexec _ hret u32 rfl hres
    (by omega) (by simp) e.nodes 70 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs2 : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]; exact takeM2
  rw [hs2] at post
  exact post


theorem prep_ref_val (caller : NState) (params : List CppVectorBindings.Parameter) (ty tn : Ty)
    (hp : params = [.scalar ty true false,.scalar tn false true]) (sa : Nat) (ba : CppState.Binding) (va : Int)
    (ca : caller.scalarCell sa ty = some (ba,⟨ty,va⟩)) (e : NExpr) (n : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = tn) (value : e.denote (envOf caller) = some n)
    (valid : caller.frame.state.wellFormed = true) (nv : tn.valid n = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller params [.scalarReference sa,.value e] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ++ [⟨tn,n⟩] ∧
        Sinit.scalars.bindings = [⟨ba.address,false⟩,⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have core1 := core_charge caller 1 1
  obtain ⟨t,ran,good⟩ := scalar_eval e (caller.charge 1 1) n hs (by rw [envOf_core core1]; exact value)
  refine ⟨t,good,?_⟩
  obtain ⟨ia,_,_,hma,_,vva⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have frameT : t.frame = caller.frame := by rw [good.1.1]; rfl
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := by rw [good.1.2.2.2.1]; rfl
  have hbind : t.scalars.bindings = caller.scalars.bindings := by rw [good.1.2.2.2.2.1]; rfl
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := by rw [good.1.2.2.2.2.2]; rfl
  have res1 : resolve caller (.scalar ty true false) (.scalarReference sa) =
      some (caller.charge 1 1,.scalarAddress ty ba.address false) := by simp [resolve,ca]
  have res2 : resolve (caller.charge 1 1) (.scalar tn false true) (.value e) = some (t,.scalar tn true n) := by
    simp [resolve,hty,ran]
  rw [hp]
  simp [prepare,valid,resolveAll,res1,res2]
  have hma' : (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell))[ba.address]? = some ⟨ty,va⟩ := by rw [List.getElem?_append_left lta]; exact hma
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,nv,callerP,NState.observe,CppState.State.observe,
    hma',vva]
  have h1 := good.2.2.2.2.1
  simp only [charge_scalar_peak] at h1
  omega


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine Proofs.ModIntPow in
theorem pow_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (sa : Nat)
    (ba : CppState.Binding) (x : Nat) (hx : x < m) (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩))
    (e : NExpr) (n : Nat) (hs : e.scalarOnly = true) (hty : e.resultType = u64)
    (value : e.denote (envOf caller) = some (n : Int)) (hn : n < 18446744073709551616)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_pow m).parameters
        [.scalarReference sa,.value e] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_pow m).callFuel fuel caller [.scalarReference sa,.value e] =
        .finished (res,.scalar (((x ^ n) % m : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res (e.nodes + 1) 6000 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref_val caller _ u32 u64 rfl sa ba _ ca e (n : Int) hs hty value valid (u64_valid_nat n hn)
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,yF,hexec,hret,hcost,hneed,hrps⟩ := pow_exec m hm hm2 (callerP caller) ba.address x n hx hn hPa hlt
  have hres : (x ^ n) % m < 4294967296 := by have := Nat.mod_lt (x ^ n) (show 0 < m by omega); omega
  have gw := good.2.2.1
  have cw : (caller.charge 1 1).scalars.work = caller.scalars.work + 1 := rfl
  have takeM2 : (callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    rw [List.take_append_of_le_length (by omega)]; exact takeM
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_pow m) [.scalarReference sa,.value e] Sinit
    (callerP caller ++ [⟨u64,(n : Int)⟩]) [⟨ba.address,false⟩,⟨(callerP caller).length,true⟩] hprep (by rw [sSlots]; rfl)
    sMem sBind sBase sScope sFrame sPeak (by simp; omega) (by rw [takeM2]) valid lengths strict base rfl 70 r hexec _ hret u32 rfl
    (u32_valid_nat _ hres) (by omega) (by simp) (e.nodes + 1) 6000 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs2 : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [pstate, cells]
    rw [List.take_append_of_le_length (by omega)]; exact takeM
  rw [hs2] at post
  exact post


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine Proofs.ModIntPow in
theorem inv_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (sa : Nat)
    (ba : CppState.Binding) (x : Nat) (hx : x < m) (hx0 : x ≠ 0)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_inv m).parameters
        [.scalarReference sa] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_inv m).callFuel fuel caller [.scalarReference sa] =
        .finished (res,.scalar ((((x ^ (m - 2)) % m) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 6000 caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref1 caller _ u32 false rfl sa ba _ ca (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hL⟩ := inv_exec m hm hm2 (callerP caller) ba.address x hx hx0 hPa hlt
  have hres : ((x ^ (m - 2)) % m) < 4294967296 := by have := Nat.mod_lt (x ^ (m - 2)) (show 0 < m by omega); omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_inv m) [.scalarReference sa] Sinit
    (callerP caller) [⟨ba.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 70 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 6000 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    obtain ⟨L,hL'⟩ := hL
    rw [hL', List.take_append_of_le_length (by omega)]; exact takeM
  rw [hs] at post
  exact post


open Proofs.ModIntExec Proofs.PowModStep Proofs.StraightLine Proofs.ModIntPow in
-- For a prime modulus the value `inv` returns is the multiplicative inverse (Fermat's little theorem).
theorem inv_correct_prime (m : Nat) (hp : Proofs.Fermat.IsPrime m) (hm2 : m < 4294967296) (caller : NState) (sa : Nat)
    (ba : CppState.Binding) (x : Nat) (hx : x < m) (hx0 : x ≠ 0)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, ∃ v : Nat, prepare caller (Proofs.ModIntInstance.ModInt_inv m).parameters [.scalarReference sa] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_inv m).callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar (v : Int)) ∧
      ScalarPost2 caller Sinit res 0 6000 caller.scalars.memory ∧ v < m ∧ x * v % m = 1 := by
  obtain ⟨Sinit,fuel,res,h1,h2,h3⟩ := inv_correct m hp.1 hm2 caller sa ba x hx hx0 ca valid lengths strict base
  refine ⟨Sinit,fuel,res,(x ^ (m - 2)) % m,h1,h2,h3,?_,?_⟩
  · exact Nat.mod_lt _ (by have h2m := hp.1; omega)
  
  · exact Proofs.Fermat.inv_mul_eq_one m x hp (by omega) hx

end Proofs.ModIntCall

namespace Proofs.ModIntDiv
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.StraightLine Proofs.PowModStep Proofs.ShiftState
open Proofs.IntSim Proofs.PexecKit Proofs.QuotientSearch Proofs.DoublingNested Proofs.Mod61Body Proofs.ModIntExec Proofs.ModIntPow
open Proofs.CppState (Cell)

/-- The inverse of the divisor: `inv`'s body up to the copy of the result, in the numbering of `inv`. -/
abbrev divA (m : Nat) : Command :=
  .sequence (.primitive (.check neZero)) (.sequence (.primitive (.declare u64 true (expE m)))
    (powPre m (.primitive (.declare u32 true (.variable u32 5)))))

abbrev mulD (m : Nat) : NExpr := .cast u32 (.divrem u64 true (.binary u64 .mul (.cast u64 (.variable u32 0))
  (.cast u64 (.variable u32 9))) (.cast u64 (.literal u32 (m : Int))))

/-- Discarded nested multiplication returns are evaluated before the final return. -/
abbrev divBody (m copies : Nat) : Command := (divA m).sh.snoc
  (.sequence (.primitive (.declare u32 true (.variable u32 7)))
    (.sequence (.primitive (.declare u32 true (.variable u32 8)))
      (.sequence (.primitive (.assign 0 u32 (mulD m))) (returnedCopies copies))))
abbrev divZ (m : Nat) : Command :=
  .sequence (.primitive (.declare u32 true (.variable u32 7)))
    (.sequence (.primitive (.declare u32 true (.variable u32 8)))
      (.sequence (.primitive (.assign 0 u32 (mulD m))) (returnedCopies 1)))

theorem div_body_eq (m : Nat) : (Proofs.ModIntInstance.ModInt_div_assign m).body = divBody m 1 := rfl

theorem divA_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x : Nat) (hx : x < m) (hx0 : x ≠ 0)
    (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    ∃ (r1 : PR) (L : List Cell), pexec 70 (divA m) ⟨P,[⟨a,false⟩]⟩ = some r1 ∧ r1.ret = none ∧
      r1.cost ≤ 80 * 64 + 100 ∧ r1.need ≤ P.length + 60 ∧
      r1.ps = stK P a (L ++ [⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩]) ∧ L.length = 5 ∧
      L[4]? = some ⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩ := by
  have hxv : x < 4294967296 := by omega
  have hS0 : (⟨P,[⟨a,false⟩]⟩ : PS) = stK P a [] := by simp [stK, bsK]
  rw [hS0]
  have e0 := stK_env0 P [] a x hxv ha hlt
  have dz := neZero_value (penv (stK P a [])) x hxv e0
  have d1 : neZero.denote (penv (stK P a [])) = some 1 := by rw [dz]; simp [hx0]
  have pc : pstmt (.check neZero) (stK P a []) =
      some ⟨stK P a [],none,neZero.nodes+1,(stK P a []).mem.length+(stK P a []).bs.length+neZero.nodes+2⟩ := by
    simp only [pstmt, Bind.bind, Option.bind, d1]
    simp
  have q1 : pexec 70 (.primitive (.check neZero)) (stK P a []) =
      some ⟨stK P a [],none,neZero.nodes+1,(stK P a []).mem.length+(stK P a []).bs.length+neZero.nodes+2⟩ := by
    rw [pexec_prim, pc]
  have dn := expE_value (penv (stK P a [])) m hm hm2
  have s2 := stK_declare P [] a u64 (expE m) ((m - 2 : Nat) : Int) dn (Ty.convert_of_valid _ _ (u64_lt _ (by omega)))
  have q2 : pexec 70 (.primitive (.declare u64 true (expE m))) (stK P a []) =
      some ⟨stK P a [⟨u64,((m - 2 : Nat) : Int)⟩],none,(expE m).nodes+1,P.length+2*([] : List Cell).length+1+(expE m).nodes+4⟩ := by
    rw [pexec_prim, s2]
    rfl
  have hrlt : (x ^ (m - 2)) % m < m := Nat.mod_lt _ (by omega)
  have hrlt2 : (x ^ (m - 2)) % m < 4294967296 := by omega
  have htfull : ∀ yF, yF < m → ∃ rt, pexec 70 (.primitive (.declare u32 true (.variable u32 5)))
      (pstate P a 0 yF ((x ^ (m - 2)) % m) 1) = some rt ∧
      rt.ps = stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1 ++ [⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩]) ∧
      rt.ret = none ∧ rt.cost ≤ 20 ∧ rt.need ≤ P.length + 40 := by
    intro yF hy
    have hst : pstate P a 0 yF ((x ^ (m - 2)) % m) 1 = stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1) := pstate_eq _ _ _ _ _ _
    rw [hst]
    have e5 : penv (stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1)) 5 u32 = some (((x ^ (m - 2)) % m : Nat) : Int) :=
      stK_envL P _ a 4 ⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩ u32 rfl rfl (u32_valid_nat _ hrlt2)
    have s3 := stK_declare P (cells 0 yF ((x ^ (m - 2)) % m) 1) a u32 (.variable u32 5) (((x ^ (m - 2)) % m : Nat) : Int)
      (by rw [den_variable]; exact e5) (convert32 _ hrlt2)
    refine ⟨_, by rw [pexec_prim, s3], rfl, rfl, ?_, ?_⟩
    · simp [NExpr.nodes]
    · simp [NExpr.nodes, stK_size, cells]
  have ht : ∀ yF, yF < m → ∃ rt, pexec 70 (.primitive (.declare u32 true (.variable u32 5)))
      (pstate P a 0 yF ((x ^ (m - 2)) % m) 1) = some rt := by
    intro yF hy
    obtain ⟨rt,h,_⟩ := htfull yF hy
    exact ⟨rt,h⟩
  have hn : m - 2 < 18446744073709551616 := by omega
  obtain ⟨yF,r1,rt,hyF,hrt,hr1,hps,hret,hcost,hneed⟩ :=
    pow_pre_exec m hm hm2 P a x (m - 2) hx hn ha hlt (.primitive (.declare u32 true (.variable u32 5))) ht
  obtain ⟨rt',hrt',hrtps,hrtret,hrtcost,hrtneed⟩ := htfull yF hyF
  rw [hrt'] at hrt
  cases hrt
  have q5 := seq_some q2 rfl hr1
  have q6 := seq_some q1 rfl q5
  refine ⟨_, cells 0 yF ((x ^ (m - 2)) % m) 1, q6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hret, hrtret]
  · simp [NExpr.nodes, stK, bsK] at *; omega
  · simp [NExpr.nodes, stK, bsK] at *; omega
  · simp [hps, hrtps]
  · simp [cells]
  · simp [cells]

theorem mulD_value (env : Nat → Ty → Option Int) (m x y : Nat) (hm : 0 < m) (hm2 : m < 4294967296)
    (hx : x < m) (hy : y < m) (h0 : env 0 u32 = some (x : Int)) (h9 : env 9 u32 = some (y : Int)) :
    (mulD m).denote env = some ((x * y % m : Nat) : Int) := by
  have hxy : x * y < 18446744073709551616 := by
    have : x * y < m * m := Nat.mul_lt_mul'' hx hy
    have : m * m ≤ 4294967296 * 4294967296 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hxv : u64.valid (x : Int) = true := u64_lt x (by omega)
  have hyv : u64.valid (y : Int) = true := u64_lt y (by omega)
  have hmv : u64.valid (m : Int) = true := u64_lt m (by omega)
  have lit : u32.valid (m : Int) = true := u32_valid_nat m (by omega)
  have rem := rem_value (x * y) m hm hxy
  simp only [NExpr.denote, h0, h9, lit, ite_true, Option.bind_some, binaryValue]
  rw [Ty.convert_of_valid _ _ hxv, Ty.convert_of_valid _ _ hyv, Ty.convert_of_valid _ _ hmv]
  simp only [Option.bind_some]
  have e1 : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by omega
  rw [e1, Ty.convert_of_valid _ _ (u64_lt _ hxy)]
  simp only [Option.bind_some]
  rw [rem]
  simp only [Option.bind_some]
  exact convert32 _ (by have := Nat.mod_lt (x * y) hm; omega)

/-- A copy declaration `T v = <variable k>` in the shifted numbering (one extra leading binding `b0`). -/
theorem shDecl (P L : List Cell) (a : Nat) (b0 : CppState.Binding) (ty : Ty) (k : Nat) (v : Int)
    (hv : (NExpr.variable ty k).denote (penv (stK P a L)) = some v) (hc : ty.convert v = some v) :
    pstmt (.declare ty true (.variable ty (k + 1))) ⟨P ++ L, b0 :: bsK a P.length L.length⟩ =
      some (⟨⟨P ++ (L ++ [(⟨ty,v⟩ : Cell)]), b0 :: bsK a P.length (L ++ [(⟨ty,v⟩ : Cell)]).length⟩, none, 2,
        P.length + 2 * L.length + 1 + 1 + 4 + 1⟩ : PR) := by
  have h := pstmt_sh (.declare ty true (.variable ty k)) (P ++ L) (bsK a P.length L.length) b0
  have d := stK_declare P L a ty (.variable ty k) v hv hc
  have e : (⟨P ++ L, bsK a P.length L.length⟩ : PS) = stK P a L := rfl
  simp only [NStmt.sh, NExpr.sh] at h
  rw [h, e, d]
  simp [shR, NExpr.nodes, stK]

theorem div_exec_copies (copies : Nat) (small : copies ≤ 2) (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (ax ay x y : Nat) (hx : x < m) (hy : y < m)
    (hy0 : y ≠ 0) (hPx : P[ax]? = some ⟨u32,(x : Int)⟩) (hPy : P[ay]? = some ⟨u32,(y : Int)⟩)
    (hltx : ax < P.length) (hlty : ay < P.length) :
    ∃ (r : PR) (L2 : List Cell), pexec 70 (divBody m copies)
        ⟨P,[⟨ax,true⟩,⟨ay,false⟩]⟩ = some r ∧
      r.ret = some ((x * ((y ^ (m - 2)) % m) % m : Nat) : Int) ∧ r.cost ≤ 80 * 64 + 200 ∧ r.need ≤ P.length + 80 ∧
      r.ps.mem = P.set ax ⟨u32,((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)⟩ ++ L2 := by
  obtain ⟨r1, L, hA, hret1, hcost1, hneed1, hps1, hL5, hL4⟩ := divA_exec m hm hm2 P ay y hy hy0 hPy hlty
  have hrlt : (y ^ (m - 2)) % m < m := Nat.mod_lt _ (by omega)
  generalize hrr : (y ^ (m - 2)) % m = rr at hps1 hL4 hrlt ⊢
  let c : Cell := ⟨u32,(rr : Int)⟩
  let L' : List Cell := L ++ [c]
  let L3 : List Cell := L' ++ [c] ++ [c]
  have hcv : u32.valid (rr : Int) = true := u32_valid_nat _ (by omega)
  have hL'5 : L'[5]? = some c := by simp [L', hL5]
  have hL'len : L'.length = 6 := by simp [L', hL5]
  have hL2 : (L' ++ [c])[6]? = some c := by simp [hL'len]
  have hL3 : L3[7]? = some c := by simp [L3, hL'len]
  have hL3len : L3.length = 8 := by simp [L3, hL'len]
  have hsh := pexec_sh 70 (divA m) ⟨P,[⟨ay,false⟩]⟩ ⟨ax,true⟩
  rw [hA] at hsh
  simp only [Option.map_some] at hsh
  have hsnoc := pexec_snoc 70 (Command.sequence (.primitive (.declare u32 true (.variable u32 7)))
    (.sequence (.primitive (.declare u32 true (.variable u32 8)))
      (.sequence (.primitive (.assign 0 u32 (mulD m))) (returnedCopies copies))))
    (divA m).sh _ (shR ⟨ax,true⟩ r1) hsh hret1
  -- the state after `inv` in the shifted numbering
  have hS1 : (shR ⟨ax,true⟩ r1).ps = ⟨P ++ L', ⟨ax,true⟩ :: bsK ay P.length L'.length⟩ := by
    show (⟨r1.ps.mem, ⟨ax,true⟩ :: r1.ps.bs⟩ : PS) = _
    rw [hps1]; rfl
  -- the two copies, via the shift of the unshifted declarations
  have z1 := shDecl P L' ay ⟨ax,true⟩ u32 6 (rr : Int)
    (by rw [den_variable]; exact stK_envL P L' ay 5 c u32 hL'5 rfl hcv) (convert32 _ (by omega))
  have z2 := shDecl P (L' ++ [c]) ay ⟨ax,true⟩ u32 7 (rr : Int)
    (by rw [den_variable]; exact stK_envL P (L' ++ [c]) ay 6 c u32 hL2 rfl hcv) (convert32 _ (by omega))
  -- the product into `x`
  have hmem3 : (P ++ (L' ++ [c] ++ [c]))[ax]? = some ⟨u32,(x : Int)⟩ := by
    rw [List.getElem?_append_left hltx]; exact hPx
  have e0 : penv ⟨P ++ (L' ++ [c] ++ [c]), ⟨ax,true⟩ :: bsK ay P.length (L' ++ [c] ++ [c]).length⟩ 0 u32 = some (x : Int) :=
    penv_ok _ 0 u32 ⟨ax,true⟩ ⟨u32,(x : Int)⟩ rfl hmem3 rfl (u32_valid_nat x (by omega))
  have e9 : penv ⟨P ++ (L' ++ [c] ++ [c]), ⟨ax,true⟩ :: bsK ay P.length (L' ++ [c] ++ [c]).length⟩ 9 u32 = some (rr : Int) := by
    rw [penv_sh (P ++ (L' ++ [c] ++ [c])) (bsK ay P.length (L' ++ [c] ++ [c]).length) ⟨ax,true⟩ 8 u32]
    exact stK_envL P (L' ++ [c] ++ [c]) ay 7 c u32 hL3 rfl hcv
  have hval := mulD_value _ m x rr (by omega) hm2 hx hrlt e0 e9
  have z3 := pstmt_assign_ok ⟨P ++ (L' ++ [c] ++ [c]), ⟨ax,true⟩ :: bsK ay P.length (L' ++ [c] ++ [c]).length⟩ 0 u32
    (mulD m) ((x * rr % m : Nat) : Int) hval ⟨ax,true⟩ ⟨u32,(x : Int)⟩ rfl hmem3 rfl (u32_valid_nat x (by omega)) rfl _
    (convert32 _ (by have := Nat.mod_lt (x * rr) (show 0 < m by omega); omega))
  have hlt3 : ax < (P ++ (L' ++ [c] ++ [c])).length := by simp; omega
  have cellV : ((P ++ (L' ++ [c] ++ [c])).set ax (⟨u32,((x * rr % m : Nat) : Int)⟩ : Cell))[ax]? =
      some ⟨u32,((x * rr % m : Nat) : Int)⟩ := List.getElem?_set_self hlt3
  have hx' : x * rr % m < 4294967296 := by have := Nat.mod_lt (x * rr) (show 0 < m by omega); omega
  have ev : penv ⟨(P ++ (L' ++ [c] ++ [c])).set ax ⟨u32,((x * rr % m : Nat) : Int)⟩,
      ⟨ax,true⟩ :: bsK ay P.length (L' ++ [c] ++ [c]).length⟩ 0 u32 = some ((x * rr % m : Nat) : Int) :=
    penv_ok _ 0 u32 ⟨ax,true⟩ ⟨u32,((x * rr % m : Nat) : Int)⟩ rfl cellV rfl (u32_valid_nat _ hx')
  have p4 := returnedCopies_exec copies 70
    ⟨(P ++ (L' ++ [c] ++ [c])).set ax ⟨u32,((x*rr%m : Nat) : Int)⟩,
      ⟨ax,true⟩ :: bsK ay P.length (L' ++ [c] ++ [c]).length⟩ ((x*rr%m : Nat) : Int)
    ev (u32_valid_nat _ hx')
  have p3 := seq_some ((pexec_prim 70 (.assign 0 u32 (mulD m)) _).trans z3) rfl p4
  have p2 := seq_some ((pexec_prim 70 (.declare u32 true (.variable u32 8)) _).trans z2) rfl p3
  have p1 := seq_some ((pexec_prim 70 (.declare u32 true (.variable u32 7)) _).trans z1) rfl p2
  rw [divBody, hsnoc, hS1, p1]
  simp only [Option.map_some]
  refine ⟨_, L' ++ [c] ++ [c] ++ List.replicate copies ⟨u32,((x*rr%m : Nat) : Int)⟩, rfl, rfl, ?_, ?_, ?_⟩
  · simp [shR, NExpr.nodes, mulD] at *
    omega
  · simp [shR, NExpr.nodes, mulD, stK, bsK] at *
    omega
  · simp [pushedCopies_memory,List.set_append_left,hltx,List.append_assoc]

theorem div_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (ax ay x y : Nat) (hx : x < m) (hy : y < m)
    (hy0 : y ≠ 0) (hPx : P[ax]? = some ⟨u32,(x : Int)⟩) (hPy : P[ay]? = some ⟨u32,(y : Int)⟩)
    (hltx : ax < P.length) (hlty : ay < P.length) :
    ∃ (r : PR) (L2 : List Cell), pexec 70 (Proofs.ModIntInstance.ModInt_div_assign m).body
        ⟨P,[⟨ax,true⟩,⟨ay,false⟩]⟩ = some r ∧
      r.ret = some ((x * ((y ^ (m - 2)) % m) % m : Nat) : Int) ∧ r.cost ≤ 80 * 64 + 200 ∧ r.need ≤ P.length + 80 ∧
      r.ps.mem = P.set ax ⟨u32,((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)⟩ ++ L2 := by
  rw [div_body_eq]
  exact div_exec_copies 1 (by decide) m hm hm2 P ax ay x y hx hy hy0 hPx hPy hltx hlty

open Proofs.ModIntCall Proofs.ScalarCall Proofs.ScalarStraight Proofs.ExtremaCall Proofs.DoublingCall in
theorem div_assign_correct (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (caller : NState) (sa sb : Nat)
    (ba bb : CppState.Binding) (x y : Nat) (hx : x < m) (hy : y < m) (hy0 : y ≠ 0)
    (ca : caller.scalarCell sa u32 = some (ba,⟨u32,(x : Int)⟩)) (cb : caller.scalarCell sb u32 = some (bb,⟨u32,(y : Int)⟩))
    (wa : ba.writable = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller (Proofs.ModIntInstance.ModInt_div_assign m).parameters
        [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      (Proofs.ModIntInstance.ModInt_div_assign m).callFuel fuel caller [.scalarReference sa,.scalarReference sb] =
        .finished (res,.scalar ((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 5400
        (caller.scalars.memory.set ba.address ⟨u32,((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)⟩) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_ref2 caller _ u32 true false rfl sa sb ba bb _ _ ca cb (fun _ => wa) (by simp) valid
  obtain ⟨ia,_,_,hma,_,_⟩ := scalarCell_facts ca
  have lta : ba.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hma).1
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hPa : (callerP caller)[ba.address]? = some ⟨u32,(x : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left lta]; exact hma
  have hlt : ba.address < (callerP caller).length := by omega
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨ib,_,_,hmb,_,_⟩ := scalarCell_facts cb
  have ltb : bb.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hPb : (callerP caller)[bb.address]? = some ⟨u32,(y : Int)⟩ := by
    simp only [callerP]; rw [List.getElem?_append_left ltb]; exact hmb
  obtain ⟨r,L2,hexec,hret,hcost,hneed,hrps⟩ :=
    div_exec m hm hm2 (callerP caller) ba.address bb.address x y hx hy hy0 hPa hPb hlt (by omega)
  have hres : (x * ((y ^ (m - 2)) % m) % m) < 4294967296 := by
    have := Nat.mod_lt (x * ((y ^ (m - 2)) % m)) (show 0 < m by omega); omega
  have hpost := call_scalar caller (Proofs.ModIntInstance.ModInt_div_assign m) [.scalarReference sa,.scalarReference sb] Sinit
    (callerP caller) [⟨ba.address,true⟩,⟨bb.address,false⟩] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base rfl 70 r hexec _ hret u32 rfl (u32_valid_nat _ hres)
    (by omega) (by simp) 0 5400 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length =
      caller.scalars.memory.set ba.address ⟨u32,((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)⟩ := by
    rw [hrps]
    have := take_set_memory caller.scalars.memory (List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
      (⟨bl,0⟩ : Cell)) L2 ba.address ⟨u32,((x * ((y ^ (m - 2)) % m) % m : Nat) : Int)⟩ lta
    simpa [callerP] using this
  rw [hs] at post
  exact post

/-- For a prime modulus the value stored by `x /= y` is the quotient: it times `y` is `x` (modulo `m`). -/
theorem div_value_prime (m x y : Nat) (hp : Proofs.Fermat.IsPrime m) (hx : x < m) (hy : y < m) (hy0 : y ≠ 0) :
    (x * ((y ^ (m - 2)) % m) % m) < m ∧ (x * ((y ^ (m - 2)) % m) % m) * y % m = x := by
  have hm := hp.1
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  have h1 := Proofs.Fermat.inv_mul_eq_one m y hp (by omega) hy
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  have e : x * (y ^ (m - 2) % m) * y = x * (y * (y ^ (m - 2) % m)) := by
    rw [Nat.mul_assoc, Nat.mul_comm (y ^ (m - 2) % m) y]
  rw [e, Nat.mul_mod, h1]
  simp [Nat.mod_eq_of_lt hx]

end Proofs.ModIntDiv
