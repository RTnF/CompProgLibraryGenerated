import Proofs.MonoidCallCore
import Proofs.LegacyScalarCallCore
import Proofs.MonoidCallCoreInt

namespace Proofs.MonoidCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall

theorem s64_valid_int (v : Int) (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) : s64.valid v = true :=
  Proofs.MonoidCallCore.s64_valid_int v h0 h1

theorem const_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.ret e)) Sk) (hr : prog.result = ResultKind.scalar s64)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : s64.valid v = true)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  Proofs.MonoidCallCore.const_correct prog e v hp hb hr he hs hn hv caller valid lengths strict base

theorem ctor_correct (prog : NProgram) (hp : prog.parameters = [.scalar s64 false true])
    (hb : prog.body = .sequence (.primitive (.ret (.variable s64 0))) Sk) (hr : prog.result = ResultKind.scalar s64)
    (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v)
    (hv : s64.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e] = some Sinit ∧
      prog.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  Proofs.MonoidCallCore.ctor_correct prog hp hb hr caller e v hs hty value hv valid lengths strict base

theorem refs2_correct (prog : NProgram) (hp : prog.parameters = [.scalar s64 true false,.scalar s64 true false])
    (hr : prog.result = ResultKind.scalar s64) (hbody : Scalar prog.body = true)
    (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : s64.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ = some r ∧ r.ret = some v ∧
        r.cost ≤ C ∧ r.need ≤ P.length+16 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa,.scalarReference sb] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory :=
  Proofs.MonoidCallCore.refs2_correct prog hp hr hbody caller sa sb ba bb x y ca cb valid lengths strict base fu v hv C hex

theorem convS (v : Int) (h : s64.valid v = true) : s64.convert v = some v :=
  Proofs.MonoidCallCore.convS v h

abbrev bT := @Proofs.MonoidCallCore.bT
abbrev selBody := @Proofs.MonoidCallCore.selBody
theorem sel_exec (i j : Nat) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (P : List Cell) (a b : Nat) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 (selBody i j) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x) ∧
      r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩] :=
  Proofs.MonoidCallCore.sel_exec i j hij P a b x y hxv hyv ha hb

theorem P_cell (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩)) : (callerP caller)[ba.address]? = some ⟨s64,x⟩ :=
  Proofs.MonoidCallCore.P_cell caller sa ba x ca

theorem take_P (caller : NState) (L : List Cell) :
    (callerP caller ++ L).take caller.scalars.memory.length = caller.scalars.memory :=
  Proofs.MonoidCallCore.take_P caller L

theorem e_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.declare s64 true e))
      (.sequence (.primitive (.declare s64 true (.variable s64 0))) (.sequence (.primitive (.ret (.variable s64 1))) Sk)))
    (hr : prog.result = ResultKind.scalar s64)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : s64.valid v = true)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  Proofs.MonoidCallCore.e_correct prog e v hp hb hr he hs hn hv caller valid lengths strict base
end Proofs.MonoidCall

namespace Proofs.MonoidCallInt
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCallInt

theorem i32_valid_int (v : Int) (h0 : -2147483648 ≤ v) (h1 : v < 2147483648) : i32.valid v = true :=
  Proofs.MonoidCallCoreInt.i32_valid_int v h0 h1

theorem const_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.ret e)) Sk) (hr : prog.result = ResultKind.scalar i32)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : i32.valid v = true)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  Proofs.MonoidCallCoreInt.const_correct prog e v hp hb hr he hs hn hv caller valid lengths strict base

theorem ctor_correct (prog : NProgram) (hp : prog.parameters = [.scalar i32 false true])
    (hb : prog.body = .sequence (.primitive (.ret (.variable i32 0))) Sk) (hr : prog.result = ResultKind.scalar i32)
    (caller : NState) (e : NExpr) (v : Int)
    (hs : e.scalarOnly = true) (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v)
    (hv : i32.valid v = true) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e] = some Sinit ∧
      prog.callFuel fuel caller [.value e] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res e.nodes 70 caller.scalars.memory :=
  Proofs.MonoidCallCoreInt.ctor_correct prog hp hb hr caller e v hs hty value hv valid lengths strict base

theorem refs2_correct (prog : NProgram) (hp : prog.parameters = [.scalar i32 true false,.scalar i32 true false])
    (hr : prog.result = ResultKind.scalar i32) (hbody : Scalar prog.body = true)
    (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (x y : Int)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) (cb : caller.scalarCell sb i32 = some (bb,⟨i32,y⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : i32.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨ba.address,false⟩,⟨bb.address,false⟩]⟩ = some r ∧ r.ret = some v ∧
        r.cost ≤ C ∧ r.need ≤ P.length+16 ∧ r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference sa,.scalarReference sb] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference sa,.scalarReference sb] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory :=
  Proofs.MonoidCallCoreInt.refs2_correct prog hp hr hbody caller sa sb ba bb x y ca cb valid lengths strict base fu v hv C hex

theorem convI (v : Int) (h : i32.valid v = true) : i32.convert v = some v :=
  Proofs.MonoidCallCoreInt.convI v h

abbrev bT := @Proofs.MonoidCallCoreInt.bT
abbrev selBody := @Proofs.MonoidCallCoreInt.selBody
theorem sel_exec (i j : Nat) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (P : List Cell) (a b : Nat) (x y : Int)
    (hxv : i32.valid x = true) (hyv : i32.valid y = true) (ha : P[a]? = some ⟨i32,x⟩) (hb : P[b]? = some ⟨i32,y⟩) :
    ∃ r, pexec 1 (selBody i j) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x) ∧
      r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧ r.ps.mem = P ++ [⟨i32,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩] :=
  Proofs.MonoidCallCoreInt.sel_exec i j hij P a b x y hxv hyv ha hb

theorem P_cell (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (ca : caller.scalarCell sa i32 = some (ba,⟨i32,x⟩)) : (callerP caller)[ba.address]? = some ⟨i32,x⟩ :=
  Proofs.MonoidCallCoreInt.P_cell caller sa ba x ca

theorem take_P (caller : NState) (L : List Cell) :
    (callerP caller ++ L).take caller.scalars.memory.length = caller.scalars.memory :=
  Proofs.MonoidCallCoreInt.take_P caller L

theorem e_correct (prog : NProgram) (e : NExpr) (v : Int) (hp : prog.parameters = [])
    (hb : prog.body = .sequence (.primitive (.declare i32 true e))
      (.sequence (.primitive (.declare i32 true (.variable i32 0))) (.sequence (.primitive (.ret (.variable i32 1))) Sk)))
    (hr : prog.result = ResultKind.scalar i32)
    (he : ∀ env, e.denote env = some v) (hs : e.scalarOnly = true) (hn : e.nodes ≤ 10) (hv : i32.valid v = true)
    (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory :=
  Proofs.MonoidCallCoreInt.e_correct prog e v hp hb hr he hs hn hv caller valid lengths strict base
end Proofs.MonoidCallInt
