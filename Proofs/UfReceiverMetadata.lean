import Proofs.CppCallFrame
import Proofs.UfConstructorSpace

namespace Proofs.UfReceiverMetadata
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver Proofs.CppCallFrame
open Proofs.DoublingNested (i32)

theorem body_allowed (op : Operation) : Proofs.CppNoResizeScope.Allowed op.program.body = true := by
  cases op <;> simp only [Operation.program] <;> decide +kernel

def scalar_type : Operation → Proofs.CppScalar.Ty
  | .same _ _ => ⟨1,false,true⟩
  | _ => i32

theorem scalar_result (op : Operation) : op.program.result = .scalar (scalar_type op) := by
  cases op <;> rfl

theorem call_effect (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : call fuel s layout op = .finished (out,ret)) : CallEffects s out := by
  exact call_headers op.program fuel s out (arguments layout++op.extra) ret (scalar_type op)
    (scalar_result op) (body_allowed op) contexts actual

theorem actual_calls (fuels : List Nat) (ops : List Operation) (s : NState) (layout : Layout)
    (out : NState) (answers : List Int)
    (contexts : ∀ owner scope, s.frame.state.forest.context owner = some scope → scope ≤ s.scope)
    (actual : runCalls fuels ops s layout = .finished (out,answers)) : CallEffects s out := by
  induction ops generalizing fuels s out answers with
  | nil =>
    cases fuels with
    | nil =>
      have eq := congrArg Prod.fst (Outcome.finished.inj actual)
      change s = out at eq
      subst out
      exact CallEffects.refl _
    | cons fuel fuels => simp [runCalls] at actual
  | cons op ops ih =>
    cases fuels with
    | nil => simp [runCalls] at actual
    | cons fuel fuels =>
      cases ran : call fuel s layout op with
      | fault => simp [runCalls,ran,bind,Outcome.bind] at actual
      | exhausted => simp [runCalls,ran,bind,Outcome.bind] at actual
      | finished pair =>
        obtain ⟨middle,ret⟩ := pair
        have head := call_effect fuel s middle layout op ret contexts ran
        cases ret with
        | unit => simp [runCalls,ran,bind,Outcome.bind] at actual
        | vector owner element => simp [runCalls,ran,bind,Outcome.bind] at actual
        | scalar answer =>
          cases tailRun : runCalls fuels ops middle layout with
          | fault => simp [runCalls,ran,tailRun,bind,Outcome.bind] at actual
          | exhausted => simp [runCalls,ran,tailRun,bind,Outcome.bind] at actual
          | finished pair =>
            obtain ⟨final,rest⟩ := pair
            simp only [runCalls,ran,tailRun,bind,Outcome.bind,pure] at actual
            have eq := congrArg Prod.fst (Outcome.finished.inj actual)
            change final = out at eq
            subst out
            exact head.trans (ih fuels middle final rest (head.contexts contexts) tailRun)

theorem calls_work_effects (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work+ops.length*Proofs.UfTraceWork.budget ps.length ∧ CallEffects s out := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work⟩ :=
    Proofs.UfTraceWork.calls_work ops s layout ps count rank represented allowed
  obtain ⟨buf,cb,nb,inv⟩ := represented.1
  exact ⟨fuels,out,vec,nextCount,nextRank,answers,ran,strong,length,fuelsLength,answersLength,work,
    actual_calls fuels ops s layout out answers inv.ok.strict ran⟩


theorem constructed_work_effects (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int))
    (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed n) :
    ∃ receiver fuels out vec count rank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      runCalls fuels ops receiver (layoutOf caller) = .finished (out,answers) ∧
      Strong out (layoutOf caller) vec count rank ∧ vec.length = n ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ caller.work+en.nodes+n+30+ops.length*Proofs.UfTraceWork.budget n ∧
      Proofs.CppNestedEval.liveS out = Proofs.CppNestedEval.liveS caller+4 ∧
      out.frame.state.liveSpace = caller.frame.state.liveSpace+n+1 ∧ CallEffects receiver out := by
  obtain ⟨receiver,constructed,strong,ctorWork,scalarLive,vectorLive,peak⟩ :=
    Proofs.UfConstructorSpace.construct_sized caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalStrong,length,fuelsLength,answersLength,work,effects⟩ :=
    calls_work_effects ops receiver (layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) strong (by simpa using allowed)
  simp only [List.length_replicate] at length work
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalStrong,length,fuelsLength,answersLength,
    Nat.le_trans work (Nat.add_le_add_right ctorWork _),effects.scalarLive.trans scalarLive,effects.headers.live.trans vectorLive,effects⟩

theorem default_work_effects (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed 0) :
    ∃ receiver fuels out vec count rank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      runCalls fuels ops receiver (layoutOf caller) = .finished (out,answers) ∧
      Strong out (layoutOf caller) vec count rank ∧ vec.length = 0 ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ caller.work+12+ops.length*Proofs.UfTraceWork.budget 0 ∧
      Proofs.CppNestedEval.liveS out = Proofs.CppNestedEval.liveS caller+4 ∧
      out.frame.state.liveSpace = caller.frame.state.liveSpace+1 ∧ CallEffects receiver out := by
  obtain ⟨receiver,constructed,strong,ctorWork,scalarLive,vectorLive,peak⟩ :=
    Proofs.UfConstructorSpace.construct_default caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalStrong,length,fuelsLength,answersLength,work,effects⟩ :=
    calls_work_effects ops receiver (layoutOf caller) [] 0 (fun _ => 0) strong allowed
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalStrong,length,fuelsLength,answersLength,
    Nat.le_trans work (Nat.add_le_add_right ctorWork _),effects.scalarLive.trans scalarLive,effects.headers.live.trans vectorLive,effects⟩

end Proofs.UfReceiverMetadata
