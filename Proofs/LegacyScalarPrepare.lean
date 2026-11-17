import Proofs.PexecKit
import Proofs.ScalarStraight
import Proofs.ExtremaCall

/-! Shared scalar preparation and evaluation facts for the remaining legacy
components. Compatibility namespaces preserve the reviewed declarations;
no ModInt program or ModInt API proof remains in this module. -/

namespace Proofs.ModIntExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.StraightLine Proofs.PowModStep
open Proofs.IntSim Proofs.PexecKit Proofs.QuotientSearch Proofs.DoublingNested Proofs.Mod61Body
open Proofs.CppState (Cell)

theorem u32_valid_of (v : Int) (h0 : 0 ≤ v) (h1 : v < 4294967296) : u32.valid v = true := by
  rw [valid_u32]; simp; omega

theorem u32_valid_nat (n : Nat) (h : n < 4294967296) : u32.valid (n : Int) = true :=
  u32_valid_of _ (by omega) (by omega)

theorem convert32 (n : Nat) (h : n < 4294967296) : u32.convert (n : Int) = some (n : Int) :=
  Ty.convert_of_valid _ _ (u32_valid_nat n h)

theorem get_tail (P L : List Cell) (j : Nat) : (P ++ L)[P.length + j]? = L[j]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem s64_valid_of (v : Int) (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) : s64.valid v = true := by
  rw [valid_s64]; exact decide_eq_true ⟨h0, h1⟩

theorem s64_valid_nat (n : Nat) (h : n < 4294967296) : s64.valid (n : Int) = true := by
  rw [valid_s64]; exact decide_eq_true ⟨by omega, by omega⟩

theorem exec_ret (fu : Nat) (ps : PS) (e : NExpr) (v : Int) (hv : e.denote (penv ps) = some v) :
    pexec fu (.sequence (.primitive (.ret e)) Sk) ps = some ⟨ps,some v,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+2⟩ := by
  have pr := pstmt_ret_ok ps e v hv
  exact seq_ret (v := v) (by rw [pexec_prim, pr]) rfl

end Proofs.ModIntExec

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

end Proofs.ModIntCall
