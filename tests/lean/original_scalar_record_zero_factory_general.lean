namespace ScalarRecordZeroFactoryGeneral
open Proofs
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


open Proofs.MonoidLazyCall Proofs.MonoidCall


open ValueObject
open Proofs.Mod61Body

open ScalarRecordConstructorGeneral

def rawBody : Command :=
  .sequence (.primitive (.declare s64 true (.cast s64 (.literal i32 0))))
    (.sequence (.primitive (.declare s64 true (.variable s64 0)))
      (.sequence (.scope Sk) Sk))
theorem body_shape : SelectedZeroFactory.program.body = rawBody := rfl
theorem fields_shape : SelectedZeroFactory.fields = SelectedConstructor.fields := rfl

theorem raw_exec (P : List Cell) :
    ∃ r, pexec 1 SelectedZeroFactory.program.body ⟨P,[]⟩ = some r ∧
      r.ret = none ∧ r.cost = 6 ∧ r.need = P.length+7 ∧ r.ps = ws P [] (fieldCells 0) := by
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [] s64 (.cast s64 (.literal i32 0)) 0 rfl rfl)
  have d : (NExpr.variable s64 0).denote (penv (ws P [] [cx 0])) = some 0 := by
    rw [den_variable]; exact ws_env_loc P [] _ 0 (cx 0) s64 rfl rfl rfl
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx 0] s64 (.variable s64 0) 0 d rfl)
  have sc0 := pexec_scope 1 Sk (ws P [] [cx 0,cx 0]) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P [] [cx 0,cx 0]) =
      some ⟨ws P [] [cx 0,cx 0],none,1,P.length+4⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws] using sc0
  have run := seq_some q0 rfl (seq_some q1 rfl (seq_some sc rfl (pexec_skip 1 _)))
  refine ⟨⟨ws P [] (fieldCells 0),none,6,P.length+7⟩,?_,rfl,rfl,rfl,rfl⟩
  simpa [body_shape,rawBody,fieldCells,ws,NExpr.nodes,Nat.add_assoc] using run

theorem stage_ready (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller SelectedZeroFactory.program.parameters [] = some initial ∧
      runFuel fuel SelectedZeroFactory.program.body initial = .finished ⟨callee,none,false⟩ ∧
      ScalarRecordConstructorGeneral.StageState caller initial callee 0 3 := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prep_none caller SelectedZeroFactory.program.parameters rfl valid
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec (callerP caller)
  have qs : QS initial [] caller.scalars.baseMemory (caller.scope+1) (callerP caller) [] (ssl 0) :=
    ⟨by simpa [ssl] using slots,by simpa using mem,bindings,bas,scope⟩
  have fa : FA initial.frame caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope+1) caller.frame.state.storage.objects.length := by
    refine ⟨by rw [frame]; exact valid,by rw [frame]; exact lengths,by rw [frame],by rw [frame],?_,by rw [frame],by rw [frame]⟩
    intro owner c h
    rw [frame] at h
    have := strict owner c h
    omega
  have cq : Cq (scalarBound caller initial) (storageBound caller) initial.scalars.work initial := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · change initial.scalars.peak ≤ scalarBound caller initial
      unfold scalarBound; omega
    · change initial.frame.state.storage.peak ≤ storageBound caller
      rw [frame]
      change caller.frame.state.storage.peak ≤ storageBound caller
      unfold storageBound; omega
    · change initial.peak ≤ scalarBound caller initial+storageBound caller
      unfold scalarBound; omega
  have hbase : caller.scalars.baseMemory ≤ (callerP caller).length := by simp [callerP]; omega
  have run := sound SelectedZeroFactory.program.body (by decide) 1 ⟨callerP caller,[]⟩ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp only [List.length_nil,Nat.add_zero]; unfold scalarBound; omega)
    (by rw [need]; unfold scalarBound; omega) (Nat.le_refl _) (by unfold storageBound; omega)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : ScalarRecordConstructorGeneral.StageState caller initial step.state 0 3 := by
    refine ⟨?_,faD,?_,?_,by decide⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work,cost] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel SelectedZeroFactory.program.body initial step
        (by decide) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
      have initialContents : CppScalarContents.Contents caller.frame initial.frame := by
        rw [frame]; exact ⟨rfl,rfl,rfl,rfl⟩
      exact initialContents.trans stable.contents
  refine ⟨initial,fuel,step.state,prepared,?_,typed⟩
  have stepEq : step = ⟨step.state,none,false⟩ := by
    cases step
    simp only [ret,Option.map_none] at returned
    simp_all
  exact executed.trans (congrArg (fun q : NStep => Proofs.CppLoop.Outcome.finished q) stepEq)


theorem factory_correct (caller : NState) (targetConst : Bool)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel out, prepare caller SelectedZeroFactory.program.parameters [] = some initial ∧
      SelectedZeroFactory.view fuel caller [] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      ScalarRecordConstructorGeneral.ExportState 0 3 caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready caller valid lengths strict base
  obtain ⟨fin,post⟩ := ScalarRecordConstructorGeneral.finish_export 0 3 caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported 0 caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps SelectedZeroFactory.program fuel caller initial callee _ [] []
    SelectedZeroFactory.fields [] (SelectedConstructor.permissions targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran (Or.inl rfl)
    (by simpa [fields_shape] using fin)

theorem total_work (caller initial out : NState) (targetConst : Bool)
    (post : ScalarRecordConstructorGeneral.ExportState 0 3 caller initial out targetConst) :
    out.work ≤ caller.work+9 := by
  have hw := post.scalarWork
  have hs := post.storageWork
  simp only [NState.work]
  omega

end ScalarRecordZeroFactoryGeneral
