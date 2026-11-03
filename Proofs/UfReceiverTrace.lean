import Proofs.UfReceiverState

namespace Proofs.UfReceiverTrace
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.UfReceiverState
open Proofs.CppLoop (Outcome)
open Proofs.DoublingNested (i32)

inductive Operation where
  | root (a : Nat)
  | same (a b : Nat)
  | size (a : Nat)
  | unite (a b : Nat)
  | numGroups
  deriving DecidableEq, Repr

def Operation.allowed (n : Nat) : Operation → Prop
  | .root a | .size a => a < n
  | .same a b | .unite a b => a < n ∧ b < n
  | .numGroups => True

def Operation.program : Operation → NProgram
  | .root _ => Proofs.UnionFindCandidateInstance.UnionFind_root
  | .same _ _ => Proofs.UnionFindCandidateInstance.UnionFind_same
  | .size _ => Proofs.UnionFindCandidateInstance.UnionFind_size
  | .unite _ _ => Proofs.UnionFindCandidateInstance.UnionFind_unite
  | .numGroups => Proofs.UnionFindCandidateInstance.UnionFind_num_groups

def Operation.extra : Operation → List NArgument
  | .root a | .size a => [.value (.literal i32 a)]
  | .same a b | .unite a b => [.value (.literal i32 a),.value (.literal i32 b)]
  | .numGroups => []

def call (fuel : Nat) (s : NState) (layout : Layout) (op : Operation) : Outcome (NState × Ret) :=
  op.program.callFuel fuel s (arguments layout ++ op.extra)

theorem step (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (op : Operation) (allowed : op.allowed ps.length) :
    ∃ fuel out vec nextCount nextRank answer,
      call fuel s layout op = .finished (out,.scalar answer) ∧
      Represents out layout vec nextCount nextRank ∧ vec.length = ps.length := by
  cases op with
  | root a =>
    obtain ⟨fuel,out,r,vec,ran,compressed,rep⟩ := root_step s layout ps count rank represented a allowed
    exact ⟨fuel,out,vec,count,rank,(r : Int),ran,rep,compressed.length⟩
  | same a b =>
    obtain ⟨fuel,out,r1,r2,middle,vec,ran,c1,c2,connected,rep⟩ := same_step s layout ps count rank represented a b allowed.1 allowed.2
    exact ⟨fuel,out,vec,count,rank,(if r1=r2 then 1 else 0),ran,rep,c2.length.trans c1.length⟩
  | size a =>
    obtain ⟨fuel,out,r,vec,ran,compressed,rep⟩ := size_step s layout ps count rank represented a allowed
    exact ⟨fuel,out,vec,count,rank,((Proofs.UfClassInvariant.component ps a).length : Int),ran,rep,compressed.length⟩
  | unite a b =>
    obtain ⟨fuel,out,r1,r2,middle,two,vec,nextRank,ran,c1,c2,finalEq,connected,length,rep⟩ :=
      unite_step s layout ps count rank represented a b allowed.1 allowed.2
    exact ⟨fuel,out,vec,Proofs.UfFieldsUnite.countAfter count r1 r2,nextRank,
      (Proofs.UfUniteCall.uniteX two r1 r2 : Int),ran,rep,length⟩
  | numGroups =>
    obtain ⟨fuel,out,ran,rep⟩ := getter_step s layout ps count rank represented
    exact ⟨fuel,out,ps,count,rank,count,ran,rep,rfl⟩

-- This interpreter invokes the generated C++ method programs, not a pure oracle.
def runCalls : List Nat → List Operation → NState → Layout → Outcome (NState × List Int)
  | [],[],s,_ => .finished (s,[])
  | fuel::fuels,op::ops,s,layout => do
      let (next,result) ← call fuel s layout op
      match result with
      | .scalar answer => do
          let (out,answers) ← runCalls fuels ops next layout
          pure (out,answer::answers)
      | _ => .fault
  | _,_,_,_ => .fault

theorem calls_preserve (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Represents out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  induction ops generalizing s ps count rank with
  | nil => exact ⟨[],s,ps,count,rank,[],rfl,represented,rfl,rfl,rfl⟩
  | cons op ops ih =>
    obtain ⟨fuel,middle,vec1,count1,rank1,answer,ran,rep,length1⟩ :=
      step s layout ps count rank represented op (allowed op (by simp))
    have tailAllowed : ∀ other ∈ ops, other.allowed vec1.length := by
      intro other member
      rw [length1]
      exact allowed other (by simp [member])
    obtain ⟨fuels,out,vec,count2,rank2,answers,tailRun,finalRep,length2,fuelsLength,answersLength⟩ :=
      ih middle vec1 count1 rank1 rep tailAllowed
    refine ⟨fuel::fuels,out,vec,count2,rank2,answer::answers,?_,finalRep,length2.trans length1,?_,?_⟩
    · simp only [runCalls,ran,bind,Outcome.bind,tailRun,pure]
    · simp [fuelsLength]
    · simp [answersLength]

theorem constructed_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
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
      Represents out (layoutOf caller) vec count rank ∧ vec.length = n ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,rep⟩ := construct_sized caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalRep,length,fl,al⟩ := calls_preserve ops receiver (layoutOf caller)
    (List.replicate n (-1)) n (fun _ => 0) rep (by simpa using allowed)
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalRep,by simpa using length,fl,al⟩

theorem default_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
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
      Represents out (layoutOf caller) vec count rank ∧ vec.length = 0 ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,rep⟩ := construct_default caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalRep,length,fl,al⟩ := calls_preserve ops receiver (layoutOf caller)
    [] 0 (fun _ => 0) rep allowed
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalRep,length,fl,al⟩

end Proofs.UfReceiverTrace
