import Proofs.CppConstructionFootprint
import Proofs.UfConstructionExport

namespace Proofs.UfConstructionFootprint
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState Proofs.MultiVecDynamic
open Proofs.UfConstructionStage Proofs.CppConstructionFootprint
open Proofs.DoublingNested (i32)
open Proofs.CppLoop (Outcome liftChecked)

-- Refine the existing successful simulation with exact frame information.
theorem execute (st next : State) (s : NState) (real : Realizes st s) (stmt : NStmt)
    (pureRun : Proofs.DynamicOwnedControl.primitive stmt st = some ⟨next,none,false⟩) :
    ∃ t, stmt.run s = some ⟨t,none,false⟩ ∧ Realizes next t := by
  obtain ⟨a,ran,matched⟩ := Proofs.DynamicOwnedControl.primitive_sound st s real stmt _ pureRun
  have eq : a = ⟨a.state,none,false⟩ := by
    have ret := matched.returned
    have br := matched.breaking
    cases a
    simp_all
  exact ⟨a.state,ran.trans (congrArg some eq),matched.state⟩

theorem scalar_layout (st next : State) (s t : NState) (real : Realizes st s) (stmt : NStmt)
    (form : Proofs.DynamicStmtAuto.ScalarForm stmt)
    (pureRun : Proofs.DynamicOwnedControl.primitive stmt st = some ⟨next,none,false⟩)
    (actual : stmt.run s = some ⟨t,none,false⟩) : t.frame = s.frame := by
  cases stmt <;> try {simp [Proofs.DynamicStmtAuto.ScalarForm] at form}
  all_goals
    simp only [Proofs.DynamicOwnedControl.primitive] at pureRun
    obtain ⟨result,scalar,_⟩ := Proofs.DynamicResultValid.bind_some _ _ _ pureRun
    exact (Proofs.DynamicOwnedScalar.layout st s real _ form result scalar _ actual).1

theorem execute_scalar (st next : State) (s : NState) (real : Realizes st s) (stmt : NStmt)
    (form : Proofs.DynamicStmtAuto.ScalarForm stmt)
    (pureRun : Proofs.DynamicOwnedControl.primitive stmt st = some ⟨next,none,false⟩) :
    ∃ t, stmt.run s = some ⟨t,none,false⟩ ∧ Realizes next t ∧ t.frame = s.frame := by
  obtain ⟨t,ran,after⟩ := execute st next s real stmt pureRun
  exact ⟨t,ran,after,scalar_layout st next s t real stmt form pureRun ran⟩

theorem cons_actual (k : Nat) (stmt : NStmt) (rest : Command) (s t : NState) (out : NStep)
    (head : stmt.run s = some ⟨t,none,false⟩)
    (tail : CppNestedProgram.runFuel (k+1) rest t = .finished out) :
    CppNestedProgram.runFuel (k+2) (.sequence (.primitive stmt) rest) s = .finished out := by
  change (do
    let p ← liftChecked (stmt.run s)
    if p.returned.isSome || p.breaking then pure p else CppNestedProgram.runFuel (k+1) rest p.state) = _
  rw [head]
  simpa [liftChecked,bind,Outcome.bind] using tail

theorem sized_stage (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) (s : NState)
    (real : Realizes (entry P h params owner binding scope n) s) :
    ∃ t, CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct1.body s =
        .finished ⟨t,none,false⟩ ∧
      Realizes (final P h params owner binding scope n) t ∧
      t.frame = installed s.frame (filledState s.frame.state i32 s.scope n (-1)) i32 true s.scope := by
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
  have last : CppNestedProgram.runFuel 4 (.primitive .skip) d = .finished ⟨d,none,false⟩ := rfl
  refine ⟨d,?_,reald,?_⟩
  · change CppNestedProgram.runFuel 8
      (.sequence (.primitive (.fillVector i32 true countExpr valueExpr))
        (.sequence (.primitive (.declare i32 true argument))
          (.sequence (.primitive (.declare i32 true argument))
            (.sequence (.primitive (.check checkExpr)) (.primitive .skip))))) s = _
    exact cons_actual 6 _ _ _ _ _ ra
      (cons_actual 5 _ _ _ _ _ rb (cons_actual 4 _ _ _ _ _ rc (cons_actual 3 _ _ _ _ _ rd last)))
  · rw [framed,framec,frameb]
    simpa using framea

theorem default_stage (P : List Proofs.CppState.Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope : Nat) (s : NState)
    (real : Realizes (defaultEntry P h params owner binding scope) s) :
    ∃ t, CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct0.body s =
        .finished ⟨t,none,false⟩ ∧
      Realizes (defaultFinal P h params owner binding scope) t ∧
      t.frame = installed s.frame (emptyState s.frame.state i32 s.scope) i32 true s.scope := by
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
  have last : CppNestedProgram.runFuel 5 (.primitive .skip) c = .finished ⟨c,none,false⟩ := rfl
  refine ⟨c,?_,realc,?_⟩
  · exact cons_actual 6 _ _ _ _ _ ra (cons_actual 5 _ _ _ _ _ rb (cons_actual 4 _ _ _ _ _ rc last))
  · rw [framec,frameb,framea]

def preparedFrame (caller : NState) : Frame := ⟨caller.frame.state,caller.frame.rootWritable,[]⟩

theorem sized_from_caller (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int)) :
    ∃ init t, Proofs.CppNestedCall.prepare caller Proofs.UnionFindConstructionInstance.UnionFind_construct1.parameters [.value en] = some init ∧
      CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct1.body init = .finished ⟨t,none,false⟩ ∧
      Realizes (final (Proofs.DoublingCall.callerP caller) (eraseHeap heap) [] caller.frame.state.storage.objects.length 0 (caller.scope+1) n) t ∧
      t.frame = installed (preparedFrame caller) (filledState caller.frame.state i32 (caller.scope+1) n (-1)) i32 true (caller.scope+1) := by
  obtain ⟨init,prepared,locals,frame,scopeEq,_⟩ := Proofs.UfConstructionPrepare.prepare_sized caller valid en n scalar type value (nat_i32 n small)
  have real := Proofs.UfConstructionPrepare.sized_real caller init heap valid models lengths n locals frame scopeEq
  obtain ⟨t,ran,after,footprint⟩ := sized_stage _ _ _ _ _ _ n small init real
  refine ⟨init,t,prepared,ran,after,?_⟩
  simpa only [frame,scopeEq,preparedFrame] using footprint

theorem default_from_caller (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length) :
    ∃ init t, Proofs.CppNestedCall.prepare caller Proofs.UnionFindConstructionInstance.UnionFind_construct0.parameters [] = some init ∧
      CppNestedProgram.runFuel 8 Proofs.UnionFindConstructionInstance.UnionFind_construct0.body init = .finished ⟨t,none,false⟩ ∧
      Realizes (defaultFinal (Proofs.DoublingCall.callerP caller) (eraseHeap heap) [] caller.frame.state.storage.objects.length 0 (caller.scope+1)) t ∧
      t.frame = installed (preparedFrame caller) (emptyState caller.frame.state i32 (caller.scope+1)) i32 true (caller.scope+1) := by
  obtain ⟨init,prepared,locals,frame,scopeEq,_⟩ := Proofs.UfConstructionPrepare.prepare_default caller valid
  have real := Proofs.UfConstructionPrepare.default_real caller init heap valid models lengths locals frame scopeEq
  obtain ⟨t,ran,after,footprint⟩ := default_stage _ _ _ _ _ _ init real
  refine ⟨init,t,prepared,ran,after,?_⟩
  simpa only [frame,scopeEq,preparedFrame] using footprint

end Proofs.UfConstructionFootprint
