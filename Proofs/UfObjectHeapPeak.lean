import Proofs.UfObjectTraceActual
import Proofs.CppMoveSpace

namespace Proofs.UfObjectHeapPeak
open Proofs.CppMoveContext Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfObjectTrace Proofs.UfObjectTraceActual Proofs.UfObjectState Proofs.UfObjectStateMethods
open Proofs.CppMoveCallLayout Proofs.CppMoveRestore Proofs.CppMoveSpace Proofs.CppMoveFrame
open Proofs.CppMoveCallBindings Proofs.VecExpr Proofs.VecWrite Proofs.DoublingNested
open Proofs.UfCompactRootBody Proofs.DynamicResultValid

def budget (s : Context) : Nat := max s.objects.heap.peak (s.objects.heap.liveSpace+1-s.objects.heap.baseSpace)

theorem prepare_heap (s out : Context) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (prepared : prepareArguments s i32 parameters arguments = some out) :
    out.objects.heap = s.objects.heap := by
  unfold prepareArguments at prepared
  obtain ⟨pair,resolved,bound⟩ := bind_some _ _ _ prepared
  rcases pair with ⟨last,saved⟩
  have stable := Proofs.CppMoveArgumentFacts.resolveArguments_stable s last i32 parameters arguments saved resolved
  exact (prepareSaved_effects last out saved bound).1.trans (congrArg Proofs.CppMoveViews.State.heap stable.objects)

theorem prepared_budget (s : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (prepared : Context) (initial : NState) (program : NProgram)
    (arguments : List NArgument) (vc : VCtx)
    (prep : prepareArguments s i32 program.parameters arguments = some prepared)
    (compacted : compact (project prepared i32) = some initial)
    (frame : FW vc state.data.items (box state.data) 0 initial.frame) :
    storageBudget initial vc.L0 = budget s := by
  have heap := prepare_heap s prepared program.parameters arguments prep
  have projected : (project prepared i32).frame.state = (project s i32).frame.state := by
    simp only [project,materialize,heap]
  have shape := (compact_metadata (project prepared i32) initial compacted).1.trans projected
  have currentLive := Proofs.CppMoveSpace.materialize_liveSpace s.objects i32 state.unique state.covered live
  have length : initial.frame.state.liveSpace = s.objects.heap.liveSpace := by
    rw [shape]
    exact currentLive
  have count : vc.L0 = s.objects.heap.liveSpace := frame.live.symm.trans length
  unfold storageBudget budget
  rw [count,shape]
  rfl

theorem invoke_heap_effects (s out : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (op : Operation) (fuel : Nat) (result : Ret)
    (actual : invoke fuel s object op = .finished (out,result)) :
    out.objects.heap.liveSpace = s.objects.heap.liveSpace ∧
    out.objects.heap.baseSpace = s.objects.heap.baseSpace ∧ HeadersLive out.objects.heap := by
  rw [invoke_state fuel s object state op] at actual
  obtain ⟨after,restored⟩ := call_objects op.program fuel s out i32 _ result actual
  exact ⟨restore_liveSpace s.objects out.objects i32 after.frame restored,
    restore_baseSpace s.objects out.objects i32 after.frame restored,
    restore_headersLive s.objects out.objects i32 after.frame restored live⟩

theorem invoke_peak (s out : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (op : Operation) (ready : op.Valid state.data.items.length)
    (fuel : Nat) (result : Ret) (actual : invoke fuel s object op = .finished (out,result)) :
    out.objects.heap.peak ≤ budget s := by
  rw [invoke_state fuel s object state op] at actual
  cases op with
  | root a =>
    change a < state.data.items.length at ready
    have av := literal_valid s object state a ready
    obtain ⟨prepared,initial,vc,chosen,after,r,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      root_step s object state a ready (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
    obtain ⟨prep,compacted,frame,ran,compressed,forest,cost,memory,scalarPeak,heapPeak,rest⟩ := post
    have same := Prod.mk.inj (Proofs.CppMoveCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_root chosen fuel s i32 _ _ _ ran actual)
    rw [← same.1]
    rw [prepared_budget s object state live prepared initial Proofs.UnionFindCandidateInstance.UnionFind_root _ vc prep compacted frame] at heapPeak
    exact heapPeak
  | same a b =>
    change a < state.data.items.length ∧ b < state.data.items.length at ready
    have av := literal_valid s object state a ready.1
    have bv := literal_valid s object state b ready.2
    obtain ⟨prepared,initial,vc,chosen,after,r1,r2,middle,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      same_step s object state a ready.1 b ready.2 (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
        (.literal i32 (b : Int)) rfl rfl (by simp [NExpr.denote,bv])
    obtain ⟨prep,compacted,frame,ran,c1,c2,forest,connected,cost,memory,scalarPeak,heapPeak,rest⟩ := post
    have same := Prod.mk.inj (Proofs.CppMoveCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_same chosen fuel s i32 _ _ _ ran actual)
    rw [← same.1]
    rw [prepared_budget s object state live prepared initial Proofs.UnionFindCandidateInstance.UnionFind_same _ vc prep compacted frame] at heapPeak
    exact heapPeak
  | size a =>
    change a < state.data.items.length at ready
    have av := literal_valid s object state a ready
    obtain ⟨prepared,initial,vc,chosen,after,r,weight,final,post,next,rankEq,countEq,sizeEq,itemsEq⟩ :=
      size_step s object state a ready (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
    obtain ⟨prep,compacted,frame,ran,atRoot,negative,compressed,forest,weights,meaning,cost,memory,scalarPeak,heapPeak,rest⟩ := post
    have same := Prod.mk.inj (Proofs.CppMoveCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_size chosen fuel s i32 _ _ _ ran actual)
    rw [← same.1]
    rw [prepared_budget s object state live prepared initial Proofs.UnionFindCandidateInstance.UnionFind_size _ vc prep compacted frame] at heapPeak
    exact heapPeak
  | unite a b =>
    change a < state.data.items.length ∧ b < state.data.items.length at ready
    have av := literal_valid s object state a ready.1
    have bv := literal_valid s object state b ready.2
    obtain ⟨prepared,initial,vc,chosen,after,r1,r2,middle,two,final,post,next,countEq,sizeEq,itemsEq⟩ :=
      unite_step s object state a ready.1 b ready.2 (.literal i32 (a : Int)) rfl rfl (by simp [NExpr.denote,av])
        (.literal i32 (b : Int)) rfl rfl (by simp [NExpr.denote,bv])
    obtain ⟨prep,compacted,frame,ran,c1,c2,finalEq,newValid,connected,cost,memory,scalarPeak,heapPeak,rest⟩ := post
    have same := Prod.mk.inj (Proofs.CppMoveCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_unite chosen fuel s i32 _ _ _ ran actual)
    rw [← same.1]
    rw [prepared_budget s object state live prepared initial Proofs.UnionFindCandidateInstance.UnionFind_unite _ vc prep compacted frame] at heapPeak
    exact heapPeak
  | groups =>
    obtain ⟨prepared,initial,vc,chosen,after,post,next,rankEq,countEq,sizeEq,itemsEq⟩ := counter_step s object state
    obtain ⟨prep,compacted,current,frame,ran,cost,memory,scalarPeak,heapPeak,rest⟩ := post
    have same := Prod.mk.inj (Proofs.CppMoveCallUnique.call_unique Proofs.UnionFindCandidateInstance.UnionFind_num_groups chosen fuel s i32 _ _ _ ran actual)
    rw [← same.1]
    rw [prepared_budget s object state live prepared initial Proofs.UnionFindCandidateInstance.UnionFind_num_groups _ vc prep compacted frame] at heapPeak
    exact heapPeak

theorem history_peak (object : ObjectRef) (s out : Context) (state : State s object)
    (next : State out object) (ops : List Operation) (results : List Ret)
    (history : History object s state ops out results next) (live : HeadersLive s.objects.heap) :
    out.objects.heap.peak ≤ budget s ∧ out.objects.heap.liveSpace = s.objects.heap.liveSpace ∧
    out.objects.heap.baseSpace = s.objects.heap.baseSpace ∧ HeadersLive out.objects.heap := by
  induction history with
  | nil original initial => exact ⟨Nat.le_max_left _ _,rfl,rfl,live⟩
  | @cons source middle final initial after last op tail result results ready fuel first rest ih =>
    have effects := invoke_heap_effects source middle object initial live op fuel result first.actual
    have peak := invoke_peak source middle object initial live op ready fuel result first.actual
    have tailBound := ih effects.2.2
    have bound : budget middle ≤ budget source := by
      unfold budget
      rw [effects.1,effects.2.1]
      unfold budget at peak
      clear * - peak
      omega
    exact ⟨tailBound.1.trans bound,tailBound.2.1.trans effects.1,
      tailBound.2.2.1.trans effects.2.1,tailBound.2.2.2⟩

theorem actual_peak (s out : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (script : List (Nat × Operation)) (results : List Ret)
    (ready : ∀ op ∈ script.map Prod.snd, op.Valid state.data.items.length)
    (actual : run s object script = .finished (out,results)) :
    out.objects.heap.peak ≤ budget s ∧ out.objects.heap.liveSpace = s.objects.heap.liveSpace ∧
    out.objects.heap.baseSpace = s.objects.heap.baseSpace ∧ HeadersLive out.objects.heap := by
  obtain ⟨next,charge,history,charges,bound,count,size⟩ := actual_work s out object state script results ready actual
  exact history_peak object s out state next _ results history live

theorem actual_additional_peak (s out : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (baseline : s.objects.heap.baseSpace = s.objects.heap.liveSpace)
    (script : List (Nat × Operation)) (results : List Ret)
    (ready : ∀ op ∈ script.map Prod.snd, op.Valid state.data.items.length)
    (actual : run s object script = .finished (out,results)) :
    out.objects.heap.peak ≤ max s.objects.heap.peak 1 := by
  have peak := (actual_peak s out object state live script results ready actual).1
  have one : s.objects.heap.liveSpace+1-s.objects.heap.baseSpace = 1 := by rw [baseline]; omega
  simpa only [budget,one] using peak

-- Keep constructive termination, all method meanings, and both resource bounds.
theorem execute_peak_work (s : Context) (object : ObjectRef) (state : State s object)
    (live : HeadersLive s.objects.heap) (ops : List Operation)
    (ready : ∀ op ∈ ops, op.Valid state.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out object) (charge : Nat),
      script.map Prod.snd = ops ∧ run s object script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = state.receiver.size.value ∧
      History object s state ops out results next ∧ Proofs.UfObjectTraceWork.Charges object s state ops out results next charge ∧
      work out ≤ work s + charge ∧ out.objects.heap.peak ≤ budget s ∧
      out.objects.heap.liveSpace = s.objects.heap.liveSpace ∧ out.objects.heap.baseSpace = s.objects.heap.baseSpace ∧
      HeadersLive out.objects.heap := by
  obtain ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound⟩ :=
    Proofs.UfObjectTraceWork.execute_work s object state ops ready
  have peak := history_peak object s out state next ops results history live
  exact ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound,peak⟩

end Proofs.UfObjectHeapPeak
