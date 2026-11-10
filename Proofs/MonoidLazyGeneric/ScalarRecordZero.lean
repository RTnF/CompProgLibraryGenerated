import Proofs.CppClassCopyCommands
import Proofs.CppConstructorMultiFinish
import Proofs.CppConstructorView
import Proofs.CppFrameResolveExtension
import Proofs.CppNestedCall
import Proofs.MemberSupport
import Proofs.GenericLazy
import Proofs.MonoidLazyCall
import Proofs.CppScalarValuePrepare
import Proofs.CppScalarContents
import Proofs.GenericExtrema
import Proofs.GenericCall
import Proofs.MonoidLazyGeneric.ScalarRecordCtor
open Proofs.CppScalar
namespace VPScalarRecordZero
def vectorPermissions (_targetConst : Bool) : List Bool := []
end VPScalarRecordZero
open VPScalarRecordZero
namespace GenericScalarZero
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


open Proofs.Mod61Body

open GenericScalarCtor

variable (ty : Ty)
def rawBody : Command :=
  .sequence (.primitive (.declare ty true (Proofs.GenericLazy.castTo ty i32 (.literal i32 0))))
    (.sequence (.primitive (.declare ty true (.variable ty 0)))
      (.sequence (.scope Sk) Sk))
def program : NProgram := ⟨[],.unit,rawBody ty⟩
def view (fuel : Nat) (caller : NState) (arguments : List NArgument) (targetConst : Bool) :
    Proofs.CppLoop.Outcome (NState × Proofs.CppConstructorMultiFinish.ObjectRef) :=
  MemberView.constructViewFuel (program ty) fuel caller arguments [] (GenericScalarCtor.fields ty) (vectorPermissions targetConst) (GenericScalarCtor.permissions ty targetConst)
theorem body_shape : (program ty).body = rawBody ty := rfl

theorem raw_exec (P : List Cell) :
    ∃ r, pexec 1 (program ty).body ⟨P,[]⟩ = some r ∧
      r.ret = none ∧ r.cost ≤ 6 ∧ r.need ≤ P.length+7 ∧ r.ps = ws P [] (fieldCells ty 0) := by
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P [] [] ty (Proofs.GenericLazy.castTo ty i32 (.literal i32 0)) 0 (Proofs.GenericLazy.R0z_gen ty _) (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
  have d : (NExpr.variable ty 0).denote (penv (ws P [] [cx ty 0])) = some 0 := by
    rw [den_variable]; exact ws_env_loc P [] _ 0 (cx ty 0) ty rfl rfl (Proofs.GenericLazy.valid_zero ty)
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P [] [cx ty 0] ty (.variable ty 0) 0 d (Proofs.GenericCall.convG ty 0 (Proofs.GenericLazy.valid_zero ty)))
  have sc0 := pexec_scope 1 Sk (ws P [] [cx ty 0,cx ty 0]) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P [] [cx ty 0,cx ty 0]) =
      some ⟨ws P [] [cx ty 0,cx ty 0],none,1,P.length+4⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws] using sc0
  have run := seq_some q0 rfl (seq_some q1 rfl (seq_some sc rfl (pexec_skip 1 _)))
  have hn := Proofs.GenericLazy.castTo_nodes ty i32 (.literal i32 0)
  simp only [NExpr.nodes] at hn
  refine ⟨⟨ws P [] (fieldCells ty 0),none,(Proofs.GenericLazy.castTo ty i32 (.literal i32 0)).nodes+4,P.length+max ((Proofs.GenericLazy.castTo ty i32 (.literal i32 0)).nodes+4) 7⟩,?_,rfl,?_,?_,rfl⟩
  · simpa [body_shape,rawBody,fieldCells,ws,NExpr.nodes,Nat.add_assoc] using run
  · simp only [NExpr.nodes] at *; omega
  · simp only [NExpr.nodes] at *; omega

theorem stage_ready (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ initial fuel callee, prepare caller (program ty).parameters [] = some initial ∧
      runFuel fuel (program ty).body initial = .finished ⟨callee,none,false⟩ ∧
      GenericScalarCtor.StageState ty caller initial callee 0 3 := by
  obtain ⟨initial,prepared,slots,mem,bindings,bas,scope,frame,work,peak⟩ :=
    prep_none caller (program ty).parameters rfl valid
  obtain ⟨r,ran,ret,cost,need,ps⟩ := raw_exec ty (callerP caller)
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
  have run := sound (program ty).body (by simp [program, rawBody, Scalar, NExpr.scalarOnly, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar, Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl]) 1 ⟨callerP caller,[]⟩ r ran
    (L0:=caller.frame.state.liveSpace) (T0:=caller.frame.state.storage.work)
    (N:=caller.frame.state.storage.objects.length) (scq:=caller.scope+1)
    (SPB:=scalarBound caller initial) (TPB:=storageBound caller) (W:=initial.scalars.work)
    initial qs fa cq hbase
    (by simp only [List.length_nil,Nat.add_zero]; unfold scalarBound; omega)
    (by unfold scalarBound; omega) (Nat.le_refl _) (by unfold storageBound; omega)
  obtain ⟨fuel,step,executed,returned,breaking,qsD,faD,cqD⟩ := run
  have typed : GenericScalarCtor.StageState ty caller initial step.state 0 3 := by
    refine ⟨?_,faD,?_,?_,Proofs.GenericLazy.valid_zero ty⟩
    · rw [ps] at qsD
      simpa [ws,fieldCells,fieldBindings] using qsD
    · refine ⟨?_,cqD.scalarPeak,cqD.storagePeak,cqD.outerPeak⟩
      have bound := cqD.work
      rw [work] at bound
      omega
    · have stable := CppScalarContents.run_stable fuel (program ty).body initial step
        (by simp [program, rawBody, Scalar, NExpr.scalarOnly, CppScalarContents.Allowed, Proofs.CppScalarFrame.Scalar, Proofs.GenericLazy.castTo_scalar ty i32 (.literal i32 0) rfl]) (by intro owner c found; rw [frame] at found; have h := strict owner c found; rw [scope]; omega) executed
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
    ∃ initial fuel out, prepare caller (program ty).parameters [] = some initial ∧
      (view ty) fuel caller [] targetConst =
        .finished (out,Proofs.CppConstructorMultiFinish.reference caller 0 1) ∧
      GenericScalarCtor.ExportState ty 0 3 caller initial out targetConst := by
  obtain ⟨initial,fuel,callee,prepared,ran,ready⟩ := stage_ready ty caller valid lengths strict base
  obtain ⟨fin,post⟩ := GenericScalarCtor.finish_export ty 0 3 caller initial callee targetConst ready base
  refine ⟨initial,fuel,exported ty 0 caller callee targetConst,prepared,?_,post⟩
  exact MemberView.constructView_of_steps (program ty) fuel caller initial callee _ [] []
    (GenericScalarCtor.fields ty) [] (GenericScalarCtor.permissions ty targetConst)
    (Proofs.CppConstructorMultiFinish.reference caller 0 1) none prepared ran (Or.inl rfl)
    (by simpa using fin)

theorem total_work (caller initial out : NState) (targetConst : Bool)
    (post : GenericScalarCtor.ExportState ty 0 3 caller initial out targetConst) :
    out.work ≤ caller.work+9 := by
  have hw := post.scalarWork
  have hs := post.storageWork
  simp only [NState.work]
  omega

end GenericScalarZero

