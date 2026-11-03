import Proofs.UfRankDoubling
import Proofs.UfReceiverTrace

namespace Proofs.UfBalancedReceiver
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedEval
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfRankDoubling
open Proofs.UfClassInvariant Proofs.UfCompression Proofs.UfFindCall
open Proofs.CppLoop (Outcome)
open Proofs.DoublingNested (i32)

def Strong (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat) : Prop :=
  Represents s layout ps count rank ∧ Balanced ps rank

theorem rerank {s layout ps count oldRank} (represented : Represents s layout ps count oldRank)
    (rank : Nat → Nat) (math : Valid ps count rank) : Represents s layout ps count rank := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  exact ⟨buf,cb,nb,inv.ok,inv.items,inv.bufferValid,inv.limit,inv.owner,math,
    inv.countCell,inv.writable,inv.nCell,inv.different⟩

theorem root_kept {ps vec : List Int} {a r z : Nat} (compressed : Compressed ps vec a r)
    (root : ∃ w, ps[z]? = some w ∧ w < 0) : ∃ w, vec[z]? = some w ∧ w < 0 := by
  obtain ⟨w,found,negative⟩ := root
  exact ⟨w,(negative_entry compressed w negative).mpr found,negative⟩

theorem strong_step (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (op : Operation) (allowed : op.allowed ps.length) :
    ∃ fuel out vec nextCount nextRank answer,
      call fuel s layout op = .finished (out,.scalar answer) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length := by
  cases op with
  | root a =>
    obtain ⟨fuel,out,r,vec,ran,compressed,rep⟩ := root_step s layout ps count rank represented.1 a allowed
    exact ⟨fuel,out,vec,count,rank,(r : Int),ran,⟨rep,represented.2.compressed compressed⟩,compressed.length⟩
  | same a b =>
    obtain ⟨fuel,out,r1,r2,middle,vec,ran,c1,c2,connected,rep⟩ := same_step s layout ps count rank represented.1 a b allowed.1 allowed.2
    exact ⟨fuel,out,vec,count,rank,(if r1=r2 then 1 else 0),ran,
      ⟨rep,(represented.2.compressed c1).compressed c2⟩,c2.length.trans c1.length⟩
  | size a =>
    obtain ⟨fuel,out,r,vec,ran,compressed,rep⟩ := size_step s layout ps count rank represented.1 a allowed
    exact ⟨fuel,out,vec,count,rank,((component ps a).length : Int),ran,
      ⟨rep,represented.2.compressed compressed⟩,compressed.length⟩
  | unite a b =>
    obtain ⟨buf,cb,nb,inv⟩ := represented.1
    obtain ⟨fuel,out,r1,r2,middle,two,vec,oldRank,ran,c1,c2,finalEq,connected,length,rep⟩ :=
      unite_step s layout ps count rank represented.1 a b allowed.1 allowed.2
    have middleValid := inv.math.compressed c1
    have twoValid := middleValid.compressed c2
    have twoBalanced := (represented.2.compressed c1).compressed c2
    obtain ⟨nextRank,math,balanced⟩ := unite_balanced twoValid twoBalanced r1 r2
      (root_kept c2 (root_kept c1 c1.root)) (root_kept c2 c2.root)
    have finalMath : Valid vec (Proofs.UfFieldsUnite.countAfter count r1 r2) nextRank := by
      rw [finalEq]; exact math
    have finalBalanced : Balanced vec nextRank := by rw [finalEq]; exact balanced
    exact ⟨fuel,out,vec,Proofs.UfFieldsUnite.countAfter count r1 r2,nextRank,
      (Proofs.UfUniteCall.uniteX two r1 r2 : Int),ran,⟨rerank rep nextRank finalMath,finalBalanced⟩,length⟩
  | numGroups =>
    obtain ⟨fuel,out,ran,rep⟩ := getter_step s layout ps count rank represented.1
    exact ⟨fuel,out,ps,count,rank,count,ran,⟨rep,represented.2⟩,rfl⟩

theorem strong_rank_bound {s layout ps count rank} (represented : Strong s layout ps count rank)
    (i : Nat) (inside : i < ps.length) : rank i ≤ Nat.log2 ps.length := by
  obtain ⟨buf,cb,nb,inv⟩ := represented.1
  exact rank_bound inv.math represented.2 i inside

theorem construct_sized (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
      (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
        .finished (out,Proofs.CppConstructorFinish.reference caller 2) ∧
      Strong out (layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) := by
  obtain ⟨out,ran,rep⟩ := Proofs.UfReceiverState.construct_sized caller heap valid models lengths strict base en n small scalar type value
  exact ⟨out,ran,rep,initial_balanced n⟩

theorem construct_default (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
      (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
        .finished (out,Proofs.CppConstructorFinish.reference caller 2) ∧
      Strong out (layoutOf caller) [] 0 (fun _ => 0) := by
  obtain ⟨out,ran,rep⟩ := Proofs.UfReceiverState.construct_default caller heap valid models lengths strict base
  exact ⟨out,ran,rep,initial_balanced 0⟩

theorem strong_calls (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  induction ops generalizing s ps count rank with
  | nil => exact ⟨[],s,ps,count,rank,[],rfl,represented,rfl,rfl,rfl⟩
  | cons op ops ih =>
    obtain ⟨fuel,middle,vec1,count1,rank1,answer,ran,rep,length1⟩ :=
      strong_step s layout ps count rank represented op (allowed op (by simp))
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
      Strong out (layoutOf caller) vec count rank ∧ vec.length = n ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,rep⟩ := construct_sized caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalRep,length,fl,al⟩ := strong_calls ops receiver (layoutOf caller)
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
      Strong out (layoutOf caller) vec count rank ∧ vec.length = 0 ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,rep⟩ := construct_default caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalRep,length,fl,al⟩ := strong_calls ops receiver (layoutOf caller)
    [] 0 (fun _ => 0) rep allowed
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalRep,length,fl,al⟩


theorem root_work (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (a : Nat) (inside : a < ps.length) :
    ∃ fuel out, ∃ (r : Nat) (vec : List Int),
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a)]) = .finished (out,.scalar (r : Int)) ∧
      Compressed ps vec a r ∧ Strong out layout vec count rank ∧
      out.work ≤ s.work + 91 * Nat.log2 ps.length + 142 := by
  obtain ⟨buf,cb,nb,inv⟩ := represented.1
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r,vec,prep,ran,compressed,forest,oldRun,post,ready,cells⟩ :=
    Proofs.UfRootReady.root_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
      inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
      rfl rfl rfl rfl inv.n_value (literal_value a av s) inside
  have preserved := inv.readonly_transition out vec (inv.math.compressed compressed) compressed.length ready cells
  have bound := strong_rank_bound represented a inside
  have scalarWork := post.scalarWork
  change out.scalars.work ≤ s.scalars.work+2+(90*rank a+140) at scalarWork
  have storageWork := post.storageWork
  refine ⟨fuel,out,r,vec,ran,compressed,⟨preserved,represented.2.compressed compressed⟩,?_⟩
  unfold NState.work
  omega

end Proofs.UfBalancedReceiver
