import Proofs.CppScalarComponents
import Proofs.UfConstructionFootprint
import Proofs.UfTraceWork

namespace Proofs.UfConstructionPeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedEval
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState Proofs.MultiVecDynamic
open Proofs.UfConstructionStage Proofs.CppConstructionFootprint Proofs.UfConstructionFootprint
open Proofs.CppConstructorWork Proofs.CppConstructorPeak Proofs.CppScalarComponents
open Proofs.CppRootModel Proofs.UfConstructionExport Proofs.CppConstructorFinish
open Proofs.UfBalancedReceiver (Strong)
open Proofs.DoublingNested (i32)

private theorem scalar_envelope (origin bound before live temp after : Nat)
    (prior : before ≤ max origin bound) (space : live+temp ≤ bound)
    (step : after ≤ max before (live+temp)) : after ≤ max origin bound :=
  step.trans (max_le prior (space.trans (Nat.le_max_right _ _)))

private theorem outer_envelope (origin scalar bound storage before live temp inner after : Nat)
    (prior : before ≤ max origin (max scalar bound+storage))
    (scalarBound : inner ≤ max scalar bound) (space : live+temp ≤ bound)
    (step : after ≤ max before (max inner (live+temp)+storage)) :
    after ≤ max origin (max scalar bound+storage) :=
  step.trans (max_le prior ((Nat.add_le_add_right
    (max_le scalarBound (space.trans (Nat.le_max_right _ _))) storage).trans (Nat.le_max_right _ _)))

theorem sized_stage_peak (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) (s : NState)
    (real : Realizes (entry P h params owner binding scope n) s) :
    ∃ t, CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct1.body s =
        .finished ⟨t,none,false⟩ ∧
      Realizes (final P h params owner binding scope n) t ∧
      t.frame = installed s.frame (filledState s.frame.state i32 s.scope n (-1)) i32 true s.scope ∧
      t.scalars.baseMemory = s.scalars.baseMemory ∧
      t.scalars.memory.length = s.scalars.memory.length+2 ∧
      t.scalars.bindings.length = s.scalars.bindings.length+2 ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+7) ∧
      t.peak ≤ max s.peak (max s.scalars.peak (liveS s+10)+
        max s.frame.state.storage.peak (s.frame.state.liveSpace+(n+2)-s.frame.state.storage.baseSpace)) := by
  let st := entry P h params owner binding scope n
  let vs := vectorState P h params owner binding scope n
  let cs := countState P h params owner binding scope n
  let fs := final P h params owner binding scope n
  have fill := fill_step P h params owner binding scope n small
  obtain ⟨a,ra,reala⟩ := execute st vs s real (.fillVector i32 true countExpr valueExpr) fill
  have countPure : denote st.params st.core.locals st.core.contents countExpr = some (n : Int) := by
    simpa [st,entry,argLocals] using eval_count P [] (n : Int) [] [] (nat_i32 n small) (nat_u64 n small) st.params st.core.contents
  have countActual : countExpr.denote (Proofs.CppNestedEval.envOf s) = some (n : Int) := by
    rw [← Proofs.DynamicRealizes.scalar_denote _ _ _ s real.data countExpr rfl]
    exact countPure
  have valueActual : valueExpr.denote (Proofs.CppNestedEval.envOf s) = some (-1) := rfl
  have framea := fill_layout s i32 true countExpr valueExpr n (-1) rfl rfl countActual valueActual _ ra
  obtain ⟨b,rb,realb,frameb⟩ := execute_scalar vs cs a reala (.declare i32 true argument) (by trivial)
    (count_step P h params owner binding scope n small)
  obtain ⟨c,rc,realc,framec⟩ := execute_scalar cs fs b realb (.declare i32 true argument) (by trivial)
    (n_step P h params owner binding scope n small)
  obtain ⟨d,rd,reald,framed⟩ := execute_scalar fs fs c realc (.check checkExpr) (by trivial)
    (check_step P h params owner binding scope n small)
  have valuePure : denote st.params st.core.locals st.core.contents valueExpr = some (-1) := by
    rw [denote_scalar _ _ _ _ rfl]
    rfl
  have pa := fill_peak st s a real i32 true countExpr valueExpr n (-1) countPure valuePure
    (Int.natCast_nonneg n) (by decide) (by simpa using nat_limit n small) rfl ra
  obtain ⟨ka,ma,ba,sa⟩ := fill_components s a i32 true countExpr valueExpr n (-1)
    rfl rfl countActual valueActual (Int.natCast_nonneg n) ra
  obtain ⟨_,kb,mb,bb,sb⟩ := declare_owned_components vs cs a b reala i32 true argument rfl
    (count_step P h params owner binding scope n small) rb
  obtain ⟨_,kc,mc,bc,sc⟩ := declare_owned_components cs fs b c realb i32 true argument rfl
    (n_step P h params owner binding scope n small) rc
  obtain ⟨core,sd⟩ := check_owned_components fs fs c d realc checkExpr rfl
    (check_step P h params owner binding scope n small) rd
  obtain ⟨_,_,_,md,bd,kd⟩ := core
  have pb := scalar_peak vs cs a b reala (.declare i32 true argument) (by trivial)
    (count_step P h params owner binding scope n small) rb
  have pc := scalar_peak cs fs b c realb (.declare i32 true argument) (by trivial)
    (n_step P h params owner binding scope n small) rc
  have pd := scalar_peak fs fs c d realc (.check checkExpr) (by trivial)
    (check_step P h params owner binding scope n small) rd
  have la : liveS a = liveS s := by simp [liveS,ma,ba,ka]
  have lb : liveS b ≤ liveS s+2 := by
    simp only [liveS,mb,bb,kb]
    unfold liveS at la
    omega
  have lc : liveS c ≤ liveS s+4 := by
    simp only [liveS,mc,bc,kc]
    unfold liveS at lb
    omega
  have storageA : a.frame.state.storage.peak = max s.frame.state.storage.peak
      (s.frame.state.liveSpace+(n+2)-s.frame.state.storage.baseSpace) := by rw [framea]; rfl
  have storageB : b.frame.state.storage.peak = a.frame.state.storage.peak := by rw [frameb]
  have storageC : c.frame.state.storage.peak = a.frame.state.storage.peak := by rw [framec,frameb]
  rw [storageA] at storageB storageC
  rw [storageA] at pb
  rw [storageB] at pc
  rw [storageC] at pd
  simp only [countExpr,valueExpr,argument,checkExpr,NExpr.nodes,Proofs.DynamicScalarSound.tempBound,
    Int.toNat_natCast] at pa pb pc pd sa sb sc sd
  have last : CppNestedProgram.runFuel 4 (.primitive .skip) d = .finished ⟨d,none,false⟩ := rfl
  refine ⟨d,?_,reald,?_,kd.trans (kc.trans (kb.trans ka)),?_,?_,?_,?_⟩
  · change CppNestedProgram.runFuel 8
      (.sequence (.primitive (.fillVector i32 true countExpr valueExpr))
        (.sequence (.primitive (.declare i32 true argument))
          (.sequence (.primitive (.declare i32 true argument))
            (.sequence (.primitive (.check checkExpr)) (.primitive .skip))))) s = _
    exact cons_actual 6 _ _ _ _ _ ra
      (cons_actual 5 _ _ _ _ _ rb (cons_actual 4 _ _ _ _ _ rc (cons_actual 3 _ _ _ _ _ rd last)))
  · rw [framed,framec,frameb]
    simpa using framea
  · rw [md,mc,mb,ma]
  · rw [bd,bc,bb,ba]
  · have a7 : a.scalars.peak ≤ max s.scalars.peak (liveS s+7) :=
      scalar_envelope _ _ _ _ _ _ (Nat.le_max_left _ _) (by omega) sa
    have b7 := scalar_envelope _ _ _ _ _ _ a7 (by rw [la]; omega) sb
    have c7 := scalar_envelope _ _ _ _ _ _ b7 (by omega) sc
    exact scalar_envelope _ _ _ _ _ _ c7 (by omega) sd
  · have a10 : a.scalars.peak ≤ max s.scalars.peak (liveS s+10) :=
      scalar_envelope _ _ _ _ _ _ (Nat.le_max_left _ _) (by omega) sa
    have b10 := scalar_envelope _ _ _ _ _ _ a10 (by rw [la]; omega) sb
    have c10 := scalar_envelope _ _ _ _ _ _ b10 (by omega) sc
    have pa10 := outer_envelope s.peak s.scalars.peak (liveS s+10) _ s.peak (liveS s) 8 s.scalars.peak a.peak
      (Nat.le_max_left _ _) (Nat.le_max_left _ _) (by omega) pa
    have pb10 := outer_envelope _ _ _ _ _ _ _ _ _ pa10 a10 (by rw [la]; omega) pb
    have pc10 := outer_envelope _ _ _ _ _ _ _ _ _ pb10 b10 (by omega) pc
    exact outer_envelope _ _ _ _ _ _ _ _ _ pc10 c10 (by omega) pd

theorem default_stage_peak (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope : Nat) (s : NState)
    (real : Realizes (defaultEntry P h params owner binding scope) s) :
    ∃ t, CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct0.body s =
        .finished ⟨t,none,false⟩ ∧
      Realizes (defaultFinal P h params owner binding scope) t ∧
      t.frame = installed s.frame (emptyState s.frame.state i32 s.scope) i32 true s.scope ∧
      t.scalars.baseMemory = s.scalars.baseMemory ∧
      t.scalars.memory.length = s.scalars.memory.length+2 ∧
      t.scalars.bindings.length = s.scalars.bindings.length+2 ∧
      t.scalars.peak ≤ max s.scalars.peak (liveS s+5) ∧
      t.peak ≤ max s.peak (max s.scalars.peak (liveS s+6)+
        max s.frame.state.storage.peak (s.frame.state.liveSpace+1-s.frame.state.storage.baseSpace)) := by
  let st := defaultEntry P h params owner binding scope
  let vs := allocated st (.integer i32) true (.flat i32 scope []) 1
  let cs := {vs with core := ⟨DynamicStmt.declared vs.core.locals i32 true 0,vs.core.contents⟩}
  let fs := defaultFinal P h params owner binding scope
  have alloc : Proofs.DynamicOwnedControl.primitive (.declareVector i32 true) st = some ⟨vs,none,false⟩ := by
    simp [Proofs.DynamicOwnedControl.primitive,runConstruct,Proofs.CppVectorBindings.supported,vs,st,defaultEntry,i32]
  obtain ⟨a,ra,reala⟩ := execute st vs s real (.declareVector i32 true) alloc
  have framea := empty_layout s i32 true _ ra
  have dc : Proofs.DynamicOwnedControl.primitive (.declare i32 true (.literal i32 0)) vs = some ⟨cs,none,false⟩ := by
    apply declare_value vs i32 true (.literal i32 0) 0 0 <;> rfl
  obtain ⟨b,rb,realb,frameb⟩ := execute_scalar vs cs a reala (.declare i32 true (.literal i32 0)) (by trivial) dc
  have dn : Proofs.DynamicOwnedControl.primitive (.declare i32 true (.literal i32 0)) cs = some ⟨fs,none,false⟩ := by
    have step := declare_value cs i32 true (.literal i32 0) 0 0 rfl rfl
    simpa [cs,vs,st,fs,defaultEntry,defaultFinal,allocated,newParameter,
      DynamicConstructCore.appended,DynamicStmt.declared,List.append_assoc] using step
  obtain ⟨c,rc,realc,framec⟩ := execute_scalar cs fs b realb (.declare i32 true (.literal i32 0)) (by trivial) dn
  have pa := empty_peak s a i32 true ra
  obtain ⟨ka,ma,ba,sa⟩ := empty_components s a i32 true ra
  obtain ⟨_,kb,mb,bb,sb⟩ := declare_owned_components vs cs a b reala i32 true (.literal i32 0) rfl dc rb
  obtain ⟨_,kc,mc,bc,sc⟩ := declare_owned_components cs fs b c realb i32 true (.literal i32 0) rfl dn rc
  have pb := scalar_peak vs cs a b reala (.declare i32 true (.literal i32 0)) (by trivial) dc rb
  have pc := scalar_peak cs fs b c realb (.declare i32 true (.literal i32 0)) (by trivial) dn rc
  have la : liveS a = liveS s := by simp [liveS,ma,ba,ka]
  have lb : liveS b ≤ liveS s+2 := by
    simp only [liveS,mb,bb,kb]
    unfold liveS at la
    omega
  have storageA : a.frame.state.storage.peak = max s.frame.state.storage.peak
      (s.frame.state.liveSpace+1-s.frame.state.storage.baseSpace) := by rw [framea]; rfl
  have storageB : b.frame.state.storage.peak = a.frame.state.storage.peak := by rw [frameb]
  rw [storageA] at storageB
  rw [storageA] at pb
  rw [storageB] at pc
  simp only [NExpr.nodes,Proofs.DynamicScalarSound.tempBound] at pb pc sb sc
  have last : CppNestedProgram.runFuel 5 (.primitive .skip) c = .finished ⟨c,none,false⟩ := rfl
  refine ⟨c,?_,realc,?_,kc.trans (kb.trans ka),?_,?_,?_,?_⟩
  · exact cons_actual 6 _ _ _ _ _ ra (cons_actual 5 _ _ _ _ _ rb (cons_actual 4 _ _ _ _ _ rc last))
  · rw [framec,frameb,framea]

  · rw [mc,mb,ma]
  · rw [bc,bb,ba]
  · have a5 : a.scalars.peak ≤ max s.scalars.peak (liveS s+5) := by
      rw [sa]
      exact max_le_max (Nat.le_refl _) (by omega)
    have b5 := scalar_envelope _ _ _ _ _ _ a5 (by rw [la]; omega) sb
    exact scalar_envelope _ _ _ _ _ _ b5 (by omega) sc
  · have a6 : a.scalars.peak ≤ max s.scalars.peak (liveS s+6) := by
      rw [sa]
      exact max_le_max (Nat.le_refl _) (by omega)
    have b6 := scalar_envelope _ _ _ _ _ _ a6 (by rw [la]; omega) sb
    have pa6 := outer_envelope s.peak s.scalars.peak (liveS s+6) _ s.peak (liveS s) 0 s.scalars.peak a.peak
      (Nat.le_max_left _ _) (Nat.le_max_left _ _) (by omega) (le_of_eq pa)
    have pb6 := outer_envelope _ _ _ _ _ _ _ _ _ pa6 a6 (by rw [la]; omega) pb
    exact outer_envelope _ _ _ _ _ _ _ _ _ pb6 b6 (by omega) pc

end Proofs.UfConstructionPeak
