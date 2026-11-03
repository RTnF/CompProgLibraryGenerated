import Proofs.Mul61Body
import Proofs.ScalarCall

namespace Proofs.Mod61Call
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.QuotientSearch Proofs.Mod61Body Proofs.Mul61Body Proofs.ScalarCall
open Proofs.CppState (Cell)

theorem prepare_mod61_int (caller : NState) (xExpr : NExpr) (v : Int) (hs : xExpr.scalarOnly = true)
    (ty : xExpr.resultType = u64) (value : xExpr.denote (envOf caller) = some v)
    (valid : caller.frame.state.wellFormed = true) (nv : u64.valid v = true) :
    ∃ t, Good caller t xExpr.nodes xExpr.nodes ∧
      ∃ Sinit, prepare caller Proofs.Mod61Instance.mod61.parameters [.value xExpr] = some Sinit ∧
        Sinit.slots = [.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u64,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+2 ∧ t.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t,ran,good⟩ := scalar_eval xExpr caller v hs value
  refine ⟨t,good,?_⟩
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have res : resolve caller (.scalar u64 false true) (.value xExpr) = some (t,.scalar u64 true v) := by
    simp [resolve,ty,ran]
  have hparams : Proofs.Mod61Instance.mod61.parameters = [.scalar u64 false true] := rfl
  rw [hparams]
  simp [prepare,valid,resolveAll,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,nv,callerP,
    NState.observe,CppState.State.observe]
  exact Nat.le_max_left _ _


theorem prepare_mod61 (caller : NState) (xExpr : NExpr) (x : Nat) (hs : xExpr.scalarOnly = true)
    (ty : xExpr.resultType = u64) (value : xExpr.denote (envOf caller) = some (x : Int))
    (valid : caller.frame.state.wellFormed = true) (hx : x < 18446744073709551616) :
    ∃ t, Good caller t xExpr.nodes xExpr.nodes ∧
      ∃ Sinit, prepare caller Proofs.Mod61Instance.mod61.parameters [.value xExpr] = some Sinit ∧
        Sinit.slots = [.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u64,(x : Int)⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t.scalars.work+2 ∧ t.scalars.peak ≤ Sinit.scalars.peak :=
  prepare_mod61_int caller xExpr (x : Int) hs ty value valid (u64_lt x hx)


set_option maxHeartbeats 4000000 in
theorem mod61_correct (caller : NState) (xExpr : NExpr) (x : Nat) (hs : xExpr.scalarOnly = true)
    (ty : xExpr.resultType = u64) (value : xExpr.denote (envOf caller) = some (x : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (hx : x < 18446744073709551616) :
    ∃ Sinit fuel res, prepare caller Proofs.Mod61Instance.mod61.parameters [.value xExpr] = some Sinit ∧
      Proofs.Mod61Instance.mod61.callFuel fuel caller [.value xExpr] = .finished (res,.scalar ((x % M61 : Nat) : Int)) ∧
      ScalarPost caller Sinit res xExpr.nodes 120 := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_mod61 caller xExpr x hs ty value valid hx
  have sState : Sinit.frame.state = caller.frame.state := by rw [sFrame]
  have sRw : Sinit.frame.rootWritable = caller.frame.rootWritable := by rw [sFrame]
  have sFb : Sinit.frame.bindings = [] := by rw [sFrame]
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak caller.frame.state.liveSpace := ⟨_,rfl⟩
  have qs : QS Sinit (callerP caller) caller.scalars.baseMemory (caller.scope+1) (cm [(x : Int)]) (bmd (callerP caller) 1 wm)
      (ssl 1) := ⟨by rw [sSlots]; rfl,by rw [sMem]; simp [cm],by rw [sBind]; simp [bmd,wm],sBase,sScope⟩
  have fa : FA Sinit.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1)
      caller.frame.state.storage.objects.length := by
    refine ⟨by rw [sState]; exact valid,by rw [sState,sRw]; exact lengths,by rw [sState],by rw [sState],?_,sFb,by rw [sState]⟩
    intro owner c h
    rw [sState] at h
    have := strict owner c h
    omega
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    omega
  have cq : Cq SPB TPB Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sState]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := mod61_run (L0 := caller.frame.state.liveSpace) (T0 := caller.frame.state.storage.work)
    (N := caller.frame.state.storage.objects.length) (scq := caller.scope+1) (W := Sinit.scalars.work) Sinit x hx qs fa cq
    (by show (callerP caller).length+5-caller.scalars.baseMemory+5+60 ≤ SPB; rw [hSPB]; omega) (Nat.le_refl _)
    (by rw [hTPB]; omega)
  obtain ⟨fuel,step,hrun,ret,brk,D,stepEq,qsD,faD,cqD⟩ := run
  have hv : u64.valid ((x % M61 : Nat) : Int) = true := u64_lt _ (by unfold M61; omega)
  have memD : D.scalars.memory = callerP caller ++ cm [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),
      ((x % 2^61 : Nat) : Int),((x % M61 : Nat) : Int)] := qsD.memory
  have cond : caller.scalars.memory.length ≤ (D.charge 1 0).scalars.memory.length ∧
      ((D.charge 1 0).scalars.memory.take caller.scalars.memory.length).map Cell.type =
        caller.scalars.memory.map Cell.type := by
    have take : D.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [memD]; simp only [callerP,List.append_assoc]; exact List.take_left
    show caller.scalars.memory.length ≤ D.scalars.memory.length ∧
      (D.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type
    rw [take]
    refine ⟨?_,rfl⟩
    rw [memD]; simp [callerP]
  have scopeD : D.scope = caller.scope+1 := qsD.scope
  have fresh : ∀ owner, (D.charge 1 0).frame.state.forest.context owner ≠ some (D.charge 1 0).scope := by
    intro owner h
    have := faD.strict owner _ h
    show False
    have e : (D.charge 1 0).scope = caller.scope+1 := scopeD
    omega
  have fin := finish_scalar caller (D.charge 1 0) u64 _ hv cond faD.valid fresh
  refine ⟨Sinit,fuel,finS caller (D.charge 1 0),hprep,?_,?_⟩
  · unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have hrun' : runFuel fuel Proofs.Mod61Instance.mod61.body Sinit = .finished step := hrun
    have res : Proofs.Mod61Instance.mod61.result = ResultKind.scalar u64 := rfl
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun',brk,res,ret,stepEq,fin]
    simp
  · have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
      have := good.2.2.2.2.1
      omega
    have gw := good.2.2.1
    have cqR : Cq SPB TPB (Sinit.scalars.work+100+1) (D.charge 1 0) := by
      have := cqD.good (Good.charge D 1 0) (by
        have e : (fx SPB TPB).SPB = SPB := rfl
        have : liveS D = (callerP caller).length+5-caller.scalars.baseMemory+5 := by
          have := live_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
            ((x % M61 : Nat) : Int)]) (w := wm) qsD; simpa using this
        show liveS D + 0 ≤ SPB
        rw [this,hSPB]; omega)
      exact this.mono (by omega)
    exact scalar_post caller Sinit (D.charge 1 0) xExpr.nodes 120 _ hSPB hTPB (cells := cm [(x : Int),(M61 : Int),
      ((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),((x % M61 : Nat) : Int)]) (nb := 5) memD
      (by simp [qsD.bindings,bmd]) (by omega) (by simp [cm]) qsD.base base spC faD cqR (by
      have := cqD.work
      have c1 : (D.charge 1 0).scalars.work = D.scalars.work+1 := rfl
      omega)


theorem prepare_mul61_int (caller : NState) (e1 e2 : NExpr) (v1 v2 : Int) (h1 : e1.scalarOnly = true)
    (h2 : e2.scalarOnly = true) (t1ty : e1.resultType = u64) (t2ty : e2.resultType = u64)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (valid : caller.frame.state.wellFormed = true) (n1 : u64.valid v1 = true) (n2 : u64.valid v2 = true) :
    ∃ t1 t2, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller Proofs.Mod61Instance.mul61.parameters [.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧ Sinit.scalars.memory = callerP caller ++ [⟨u64,v1⟩,⟨u64,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+3 ∧ t2.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 h1 d1
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have frameT : t2.frame = caller.frame := by rw [g2.1.1,g1.1.1]
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have a := g2.1.2.2.2.1; have b := g1.1.2.2.2.1; rw [a,b]
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have a := g2.1.2.2.2.2.1; have b := g1.1.2.2.2.2.1; rw [a,b]
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have a := g2.1.2.2.2.2.2; have b := g1.1.2.2.2.2.2; rw [a,b]
  have res1 : resolve caller (.scalar u64 false true) (.value e1) = some (t1,.scalar u64 true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar u64 false true) (.value e2) = some (t2,.scalar u64 true v2) := by
    simp [resolve,t2ty,ran2]
  have hparams : Proofs.Mod61Instance.mul61.parameters = [.scalar u64 false true,.scalar u64 false true] := rfl
  rw [hparams]
  simp [prepare,valid,resolveAll,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,n1,n2,callerP,
    NState.observe,CppState.State.observe]
  exact ⟨by omega,Nat.le_max_left _ _⟩


theorem mul61_spec (a b : Nat) (ha : a < 2^61) (hb : b < 2^61) :
    retOf a b < 2^64 ∧ retOf a b % M61 = (a * b) % M61 := by
  have m := Proofs.Mod61Math.mul61_math a b (a / 2^31) (a % 2^31) (b / 2^31) (b % 2^31) (midOf a b)
    (midOf a b / 2^30) (midOf a b % 2^30) ha hb rfl rfl rfl rfl rfl rfl rfl
  exact m

set_option maxHeartbeats 4000000 in
theorem mul61_correct (caller : NState) (aE bE : NExpr) (a b : Nat) (hs1 : aE.scalarOnly = true)
    (hs2 : bE.scalarOnly = true) (ty1 : aE.resultType = u64) (ty2 : bE.resultType = u64)
    (d1 : aE.denote (envOf caller) = some (a : Int)) (d2 : bE.denote (envOf caller) = some (b : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (ha : a < 2^61) (hb : b < 2^61) :
    ∃ Sinit fuel res, prepare caller Proofs.Mod61Instance.mul61.parameters [.value aE,.value bE] = some Sinit ∧
      Proofs.Mod61Instance.mul61.callFuel fuel caller [.value aE,.value bE] =
        .finished (res,.scalar ((retOf a b : Nat) : Int)) ∧
      ScalarPost caller Sinit res (aE.nodes+bE.nodes) 300 := by
  have a64 : a < 18446744073709551616 := by omega
  have b64 : b < 18446744073709551616 := by omega
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_mul61_int caller aE bE (a : Int) (b : Int) hs1 hs2 ty1 ty2 d1 d2 valid (u64_lt a a64) (u64_lt b b64)
  have sState : Sinit.frame.state = caller.frame.state := by rw [sFrame]
  have sRw : Sinit.frame.rootWritable = caller.frame.rootWritable := by rw [sFrame]
  have sFb : Sinit.frame.bindings = [] := by rw [sFrame]
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak caller.frame.state.liveSpace := ⟨_,rfl⟩
  have qs : QSk Sinit (callerP caller) caller.scalars.baseMemory (caller.scope+1) a b 2 :=
    ⟨by rw [sSlots]; rfl,by rw [sMem]; simp [cm,full],by rw [sBind]; simp [bmd,w2,List.range_succ],sBase,sScope⟩
  have fa : FA Sinit.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1)
      caller.frame.state.storage.objects.length := by
    refine ⟨by rw [sState]; exact valid,by rw [sState,sRw]; exact lengths,by rw [sState],by rw [sState],?_,sFb,by rw [sState]⟩
    intro owner c h
    rw [sState] at h
    have := strict owner c h
    omega
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    omega
  have cq : Cq SPB TPB Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sState]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := mul61_run (L0 := caller.frame.state.liveSpace) (T0 := caller.frame.state.storage.work)
    (N := caller.frame.state.storage.objects.length) (scq := caller.scope+1) (W := Sinit.scalars.work) Sinit a b ha hb
    qs fa cq (by show (callerP caller).length+11-caller.scalars.baseMemory+11+60 ≤ SPB; rw [hSPB]; omega)
  obtain ⟨fuel,step,hrun,ret,brk,D,stepEq,qsD,faD,cqD⟩ := run
  have hv : u64.valid ((retOf a b : Nat) : Int) = true := u64_lt _ (mul61_spec a b ha hb).1
  have memD : D.scalars.memory = callerP caller ++ cm ((full a b).take 11) := qsD.memory
  have cond : caller.scalars.memory.length ≤ (D.charge 1 0).scalars.memory.length ∧
      ((D.charge 1 0).scalars.memory.take caller.scalars.memory.length).map Cell.type =
        caller.scalars.memory.map Cell.type := by
    have take : D.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [memD]; simp only [callerP,List.append_assoc]; exact List.take_left
    show caller.scalars.memory.length ≤ D.scalars.memory.length ∧
      (D.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type
    rw [take]
    refine ⟨?_,rfl⟩
    rw [memD]; simp [callerP]
  have scopeD : D.scope = caller.scope+1 := qsD.scope
  have fresh : ∀ owner, (D.charge 1 0).frame.state.forest.context owner ≠ some (D.charge 1 0).scope := by
    intro owner h
    have := faD.strict owner _ h
    show False
    have e : (D.charge 1 0).scope = caller.scope+1 := scopeD
    omega
  have fin := finish_scalar caller (D.charge 1 0) u64 _ hv cond faD.valid fresh
  refine ⟨Sinit,fuel,finS caller (D.charge 1 0),hprep,?_,?_⟩
  · unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have hrun' : runFuel fuel Proofs.Mod61Instance.mul61.body Sinit = .finished step := hrun
    have res : Proofs.Mod61Instance.mul61.result = ResultKind.scalar u64 := rfl
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun',brk,res,ret,stepEq,fin]
    simp
  · have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
      have a1 := g1.2.2.2.2.1
      have a2 := g2.2.2.2.2.1
      omega
    have gw1 := g1.2.2.1
    have gw2 := g2.2.2.1
    have liveD : liveS D = (callerP caller).length+11-caller.scalars.baseMemory+11 := by
      have := live_k qsD (by omega)
      simpa using this
    have cqR : Cq SPB TPB (Sinit.scalars.work+200+1) (D.charge 1 0) := by
      have := cqD.good (Good.charge D 1 0) (by
        show liveS D + 0 ≤ SPB
        rw [liveD,hSPB]; omega)
      exact this.mono (by omega)
    exact scalar_post caller Sinit (D.charge 1 0) (aE.nodes+bE.nodes) 300 _ hSPB hTPB
      (cells := cm ((full a b).take 11)) (nb := 11) memD (by simp [qsD.bindings,bmd]) (by omega)
      (by simp [cm,full]) qsD.base base spC faD cqR (by
      have := cqD.work
      have c1 : (D.charge 1 0).scalars.work = D.scalars.work+1 := rfl
      have cw : (caller.charge 1 1).scalars.work = caller.scalars.work+1 := rfl
      omega)

end Proofs.Mod61Call
