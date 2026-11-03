import Proofs.UfBalancedReceiver

namespace Proofs.UfTraceWork
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfBalancedReceiver
open Proofs.UfClassInvariant Proofs.UfCompression Proofs.UfRankDoubling
open Proofs.CppLoop (Outcome)
open Proofs.DoublingNested (i32)

def budget (n : Nat) : Nat := 182 * Nat.log2 n + 405

theorem step_work (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank) (op : Operation) (allowed : op.allowed ps.length) :
    ∃ fuel out vec nextCount nextRank answer,
      call fuel s layout op = .finished (out,.scalar answer) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      out.work ≤ s.work + budget ps.length := by
  obtain ⟨buf,cb,nb,inv⟩ := represented.1
  cases op with
  | root a =>
    obtain ⟨fuel,out,r,vec,ran,compressed,rep,work⟩ := root_work s layout ps count rank represented a allowed
    refine ⟨fuel,out,vec,count,rank,(r : Int),ran,rep,compressed.length,?_⟩
    unfold budget
    omega
  | size a =>
    change a < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,fuel,out,r,w,vec,prep,ran,found,negative,compressed,forest,weights,post,ready,cells⟩ :=
      Proofs.UfSizeReady.size_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
        inv.math.weights inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
        rfl rfl rfl rfl inv.n_value (literal_value a av s) allowed
    have rep := inv.readonly_transition out vec (inv.math.compressed compressed) compressed.length ready cells
    have bound := strong_rank_bound represented a allowed
    have scalarWork := post.scalarWork
    change out.scalars.work ≤ s.scalars.work+2+(90*rank a+160) at scalarWork
    have storageWork := post.storageWork
    refine ⟨fuel,out,vec,count,rank,(-w),ran,⟨rep,represented.2.compressed compressed⟩,compressed.length,?_⟩
    unfold NState.work budget
    omega
  | same a b =>
    change a < ps.length ∧ b < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,fuel,out,r1,r2,middle,vec,prep,ran,c1,c2,forest,connected,post,ready,cells⟩ :=
      Proofs.UfSameReady.same_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
        inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
        a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) allowed.1 allowed.2
    have length := c2.length.trans c1.length
    have rep := inv.readonly_transition out vec ((inv.math.compressed c1).compressed c2) length ready cells
    have boundA := strong_rank_bound represented a allowed.1
    have boundB := strong_rank_bound represented b allowed.2
    have scalarWork := post.scalarWork
    change out.scalars.work ≤ s.scalars.work+3+(90*rank a+90*rank b+220) at scalarWork
    have storageWork := post.storageWork
    refine ⟨fuel,out,vec,count,rank,(if r1=r2 then 1 else 0),ran,
      ⟨rep,(represented.2.compressed c1).compressed c2⟩,length,?_⟩
    unfold NState.work budget
    omega
  | unite a b =>
    change a < ps.length ∧ b < ps.length at allowed
    have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
    have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
    obtain ⟨init,fuel,out,r1,r2,middle,two,vec,prep,ran,c1,c2,finalEq,newValid,connected,
        bindings,base,post,ready,counter,other,aliases⟩ :=
      Proofs.UfUniteReady.unite_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math
        inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
        a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) allowed.1 allowed.2
    obtain ⟨next,ok,items,valid,limit,owner⟩ := ready
    have length : vec.length = ps.length := by
      have len1 := c1.length
      have len2 := c2.length
      rw [finalEq]
      unfold Proofs.UfUniteCall.uniteVec
      split_ifs <;> (try simp only [List.length_set]) <;> omega
    have savedN := other layout.nSlot i32 nb ⟨i32,ps.length⟩ inv.nCell inv.different
    have twoValid := (inv.math.compressed c1).compressed c2
    have twoBalanced := (represented.2.compressed c1).compressed c2
    obtain ⟨nextRank,math,balanced⟩ := unite_balanced twoValid twoBalanced r1 r2
      (root_kept c2 (root_kept c1 c1.root)) (root_kept c2 c2.root)
    have finalMath : Valid vec (Proofs.UfFieldsUnite.countAfter count r1 r2) nextRank := by rw [finalEq]; exact math
    have finalBalanced : Balanced vec nextRank := by rw [finalEq]; exact balanced
    have rep : Represents out layout vec (Proofs.UfFieldsUnite.countAfter count r1 r2) nextRank := by
      refine ⟨next,cb,nb,ok,items,valid,limit,owner,finalMath,counter,inv.writable,?_,inv.different⟩
      rw [length]
      exact savedN
    have boundA := strong_rank_bound represented a allowed.1
    have boundB := strong_rank_bound represented b allowed.2
    have scalarWork := post.scalarWork
    change out.scalars.work ≤ s.scalars.work+3+(90*rank a+90*rank b+400) at scalarWork
    have storageWork := post.storageWork
    refine ⟨fuel,out,vec,Proofs.UfFieldsUnite.countAfter count r1 r2,nextRank,
      (Proofs.UfUniteCall.uniteX two r1 r2 : Int),ran,⟨rep,finalBalanced⟩,length,?_⟩
    unfold NState.work budget
    omega
  | numGroups =>
    obtain ⟨init,fuel,out,prep,ran,bindings,base,post,ready,cells⟩ :=
      Proofs.UfCounterReady.num_groups_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math
        inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) rfl rfl inv.n_value
    rw [← inv.math.count] at ran
    have rep := inv.readonly_transition out ps inv.math rfl ready cells
    have scalarWork := post.scalarWork
    change out.scalars.work ≤ s.scalars.work+1+40 at scalarWork
    have storageWork := post.storageWork
    refine ⟨fuel,out,ps,count,rank,count,ran,⟨rep,represented.2⟩,rfl,?_⟩
    unfold NState.work budget
    omega

theorem calls_work (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Strong s layout ps count rank)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Strong out layout vec nextCount nextRank ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length ∧
      out.work ≤ s.work + ops.length * budget ps.length := by
  induction ops generalizing s ps count rank with
  | nil => exact ⟨[],s,ps,count,rank,[],rfl,represented,rfl,rfl,rfl,by simp⟩
  | cons op ops ih =>
    obtain ⟨fuel,middle,vec1,count1,rank1,answer,ran,rep,length1,headWork⟩ :=
      step_work s layout ps count rank represented op (allowed op (by simp))
    have tailAllowed : ∀ other ∈ ops, other.allowed vec1.length := by
      intro other member
      rw [length1]
      exact allowed other (by simp [member])
    obtain ⟨fuels,out,vec,count2,rank2,answers,tailRun,finalRep,length2,fuelsLength,answersLength,tailWork⟩ :=
      ih middle vec1 count1 rank1 rep tailAllowed
    refine ⟨fuel::fuels,out,vec,count2,rank2,answer::answers,?_,finalRep,length2.trans length1,?_,?_,?_⟩
    · simp only [runCalls,ran,bind,Outcome.bind,tailRun,pure]
    · simp [fuelsLength]
    · simp [answersLength]
    · rw [length1] at tailWork
      simp only [List.length_cons,Nat.succ_mul]
      omega

theorem constructed_calls_work (caller : NState) (heap : Proofs.CppRootModel.Heap)
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
      out.work ≤ receiver.work + ops.length * budget n := by
  obtain ⟨receiver,constructed,rep⟩ := Proofs.UfBalancedReceiver.construct_sized caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalRep,length,fl,al,work⟩ := calls_work ops receiver (layoutOf caller)
    (List.replicate n (-1)) n (fun _ => 0) rep (by simpa using allowed)
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalRep,by simpa using length,fl,al,by simpa using work⟩

theorem default_calls_work (caller : NState) (heap : Proofs.CppRootModel.Heap)
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
      out.work ≤ receiver.work + ops.length * budget 0 := by
  obtain ⟨receiver,constructed,rep⟩ := Proofs.UfBalancedReceiver.construct_default caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,answers,ran,finalRep,length,fl,al,work⟩ := calls_work ops receiver (layoutOf caller)
    [] 0 (fun _ => 0) rep allowed
  exact ⟨receiver,fuels,out,vec,count,rank,answers,constructed,ran,finalRep,length,fl,al,work⟩



end Proofs.UfTraceWork
