import Proofs.UfHistoricalRank
import Proofs.UfBalancedReceiver

namespace Proofs.UfHistoricalTrace
open Proofs.UfHistoricalRank Proofs.UfClassInvariant Proofs.UfUniteCall

open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.UfReceiverState Proofs.UfReceiverTrace
open Proofs.DoublingNested (i32)
open Proofs.CppLoop (Outcome)
open Proofs.UfBalancedReceiver (root_kept)

theorem historical_step (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank historyRank : Nat → Nat) (represented : Represents s layout ps count rank)
    (history : History ps historyRank) (op : Operation) (allowed : op.allowed ps.length) :
    ∃ fuel out vec nextCount nextRank nextHistory answer,
      call fuel s layout op = .finished (out,.scalar answer) ∧
      Represents out layout vec nextCount nextRank ∧ History vec nextHistory ∧ vec.length = ps.length := by
  cases op with
  | root a =>
    obtain ⟨fuel,out,r,vec,ran,compressed,rep⟩ := root_step s layout ps count rank represented a allowed
    exact ⟨fuel,out,vec,count,rank,historyRank,(r : Int),ran,rep,
      history_compressed history compressed,compressed.length⟩
  | size a =>
    obtain ⟨fuel,out,r,vec,ran,compressed,rep⟩ := size_step s layout ps count rank represented a allowed
    exact ⟨fuel,out,vec,count,rank,historyRank,((component ps a).length : Int),ran,rep,
      history_compressed history compressed,compressed.length⟩
  | same a b =>
    obtain ⟨fuel,out,r1,r2,middle,vec,ran,c1,c2,connected,rep⟩ :=
      same_step s layout ps count rank represented a b allowed.1 allowed.2
    exact ⟨fuel,out,vec,count,rank,historyRank,(if r1=r2 then 1 else 0),ran,rep,
      history_compressed (history_compressed history c1) c2,c2.length.trans c1.length⟩
  | unite a b =>
    obtain ⟨fuel,out,r1,r2,middle,two,vec,nextRank,ran,c1,c2,finalEq,connected,length,rep⟩ :=
      unite_step s layout ps count rank represented a b allowed.1 allowed.2
    obtain ⟨nextHistory,hist⟩ := unite_history (history_compressed (history_compressed history c1) c2)
      r1 r2 (root_kept c2 (root_kept c1 c1.root)) (root_kept c2 c2.root)
    have finalHistory : History vec nextHistory := by rw [finalEq]; exact hist
    exact ⟨fuel,out,vec,Proofs.UfFieldsUnite.countAfter count r1 r2,nextRank,nextHistory,
      (uniteX two r1 r2 : Int),ran,rep,finalHistory,length⟩
  | numGroups =>
    obtain ⟨fuel,out,ran,rep⟩ := getter_step s layout ps count rank represented
    exact ⟨fuel,out,ps,count,rank,historyRank,count,ran,rep,history,rfl⟩

theorem historical_calls (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank historyRank : Nat → Nat)
    (represented : Represents s layout ps count rank) (history : History ps historyRank)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank nextHistory answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Represents out layout vec nextCount nextRank ∧ History vec nextHistory ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  induction ops generalizing s ps count rank historyRank with
  | nil => exact ⟨[],s,ps,count,rank,historyRank,[],rfl,represented,history,rfl,rfl,rfl⟩
  | cons op ops ih =>
    obtain ⟨fuel,middle,vec1,count1,rank1,history1,answer,ran,rep,hist,length1⟩ :=
      historical_step s layout ps count rank historyRank represented history op (allowed op (by simp))
    have tailAllowed : ∀ other ∈ ops, other.allowed vec1.length := by
      intro other member
      rw [length1]
      exact allowed other (by simp [member])
    obtain ⟨fuels,out,vec,count2,rank2,history2,answers,tailRun,finalRep,finalHist,length2,fl,al⟩ :=
      ih middle vec1 count1 rank1 history1 rep hist tailAllowed
    refine ⟨fuel::fuels,out,vec,count2,rank2,history2,answer::answers,?_,finalRep,finalHist,
      length2.trans length1,by simp [fl],by simp [al]⟩
    simp only [runCalls,ran,bind,Outcome.bind,tailRun,pure]

theorem constructed_historical_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int))
    (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed n) :
    ∃ receiver fuels out vec count rank historyRank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      runCalls fuels ops receiver (layoutOf caller) = .finished (out,answers) ∧
      Represents out (layoutOf caller) vec count rank ∧ History vec historyRank ∧ vec.length = n ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,rep⟩ := construct_sized caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,historyRank,answers,ran,finalRep,hist,length,fl,al⟩ := historical_calls ops receiver (layoutOf caller)
    (List.replicate n (-1)) n (fun _ => 0) (fun _ => 0) rep (initial_history _) (by simpa using allowed)
  exact ⟨receiver,fuels,out,vec,count,rank,historyRank,answers,constructed,ran,finalRep,hist,by simpa using length,fl,al⟩

theorem default_historical_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (ops : List Operation) (allowed : ∀ op ∈ ops, op.allowed 0) :
    ∃ receiver fuels out vec count rank historyRank answers,
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
          .finished (receiver,Proofs.CppConstructorFinish.reference caller 2) ∧
      runCalls fuels ops receiver (layoutOf caller) = .finished (out,answers) ∧
      Represents out (layoutOf caller) vec count rank ∧ History vec historyRank ∧ vec.length = 0 ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,rep⟩ := construct_default caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,historyRank,answers,ran,finalRep,hist,length,fl,al⟩ := historical_calls ops receiver (layoutOf caller)
    [] 0 (fun _ => 0) (fun _ => 0) rep (initial_history 0) allowed
  exact ⟨receiver,fuels,out,vec,count,rank,historyRank,answers,constructed,ran,finalRep,hist,length,fl,al⟩

end Proofs.UfHistoricalTrace
