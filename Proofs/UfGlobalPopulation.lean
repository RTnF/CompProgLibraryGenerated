import Proofs.UfPopulationTrace

namespace Proofs.UfGlobalPopulation
open Proofs.UfClassInvariant Proofs.UfCompression Proofs.UfMergeInvariant
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfRankPopulation

noncomputable def components (ps : List Int) : List Nat := (roots ps).flatMap (members ps)

theorem root_of_mem {ps : List Int} {r : Nat} (member : r ∈ roots ps) :
    ∃ w, ps[r]? = some w ∧ w < 0 := by
  classical
  unfold roots at member
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem reach_of_member {ps : List Int} {i r : Nat} (member : i ∈ members ps r) : Reach ps i r := by
  classical
  unfold members at member
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem members_disjoint_lists (ps : List Int) (X Y : Nat)
    (rx : X ∈ roots ps) (ry : Y ∈ roots ps) (different : X ≠ Y) :
    List.Disjoint (members ps X) (members ps Y) := by
  apply List.disjoint_left.mpr
  intro i hx hy
  exact members_disjoint ps X Y (root_of_mem rx) (root_of_mem ry) different i
    (reach_of_member hx) (reach_of_member hy)

theorem components_nodup (ps : List Int) : (components ps).Nodup := by
  unfold components
  change List.Pairwise (fun (a b : Nat) => a ≠ b) ((roots ps).flatMap (members ps))
  apply List.pairwise_flatMap.mpr
  refine ⟨fun r _ => members_nodup ps r,?_⟩
  apply List.Pairwise.imp_of_mem _ (roots_nodup ps)
  intro X Y hx hy different i hi j hj same
  subst j
  exact (List.disjoint_left.mp (members_disjoint_lists ps X Y hx hy different)) hi hj

theorem components_mem {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (i : Nat) : i ∈ components ps ↔ i < ps.length := by
  classical
  constructor
  · intro member
    obtain ⟨r,root,inside⟩ := List.mem_flatMap.mp member
    have range := (List.mem_filter.mp inside).1
    exact List.mem_range.mp range
  · intro inside
    obtain ⟨out,r,run,ret,reach,rootInside,root,rest⟩ :=
      Proofs.UfFindCall.body_exec_find [] ps rank valid.forest valid.length i inside (rank i+2) (by omega)
    apply List.mem_flatMap.mpr
    refine ⟨r,?_,?_⟩
    · simp only [roots,List.mem_filter,List.mem_range,decide_eq_true_eq]
      exact ⟨rootInside,root⟩
    · simp only [members,List.mem_filter,List.mem_range,decide_eq_true_eq]
      exact ⟨inside,reach⟩

theorem components_perm {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) : (components ps).Perm (List.range ps.length) := by
  apply (List.perm_ext_iff_of_nodup (components_nodup ps) List.nodup_range).mpr
  intro i
  simpa only [List.mem_range] using components_mem valid i

theorem component_sizes_sum {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) :
    ((roots ps).map (fun r => (members ps r).length)).sum = ps.length := by
  have eq := (components_perm valid).length_eq
  simpa only [components,List.length_flatMap,List.length_range] using eq

theorem component_counts_sum {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (predicate : Nat → Bool) :
    ((List.range ps.length).filter predicate).length =
      ((roots ps).map (fun r => count ps predicate r)).sum := by
  have eq := ((components_perm valid).filter predicate).length_eq.symm
  simpa only [components,List.filter_flatMap,List.length_flatMap,count] using eq

theorem sum_count_bounds (rs : List Nat) (sizes counts : Nat → Nat) (threshold : Nat)
    (bounds : ∀ r ∈ rs, counts r * threshold ≤ 2 * sizes r) :
    (rs.map counts).sum * threshold ≤ 2 * (rs.map sizes).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have head := bounds r (by simp)
    have tail := ih (fun other member => bounds other (by simp [member]))
    simp only [List.map_cons,List.sum_cons,Nat.add_mul,Nat.mul_add]
    omega

noncomputable def globalCount (ps : List Int) (rho : Nat → Nat) (k : Nat) : Nat :=
  ((List.range ps.length).filter (fun i => decide (k ≤ rho i))).length

def GlobalPopulation (ps : List Int) (rho : Nat → Nat) : Prop :=
  ∀ k, globalCount ps rho k * 2^k ≤ 2 * ps.length

theorem population_global {ps : List Int} {groups : Int} {rank rho : Nat → Nat}
    (valid : Valid ps groups rank) (population : Population ps rho) : GlobalPopulation ps rho := by
  intro k
  have summed := sum_count_bounds (roots ps) (fun r => (members ps r).length)
    (fun r => highCount ps rho k r) (2^k) (by
      intro r member
      obtain ⟨w,found,negative⟩ := root_of_mem member
      have budget := population r w found negative k
      by_cases small : (members ps r).length < 2^k
      · rw [budget.1 small]
        simp
      · have bound := budget.2 (show 2^k ≤ (members ps r).length by omega)
        exact (Nat.le_add_right _ _).trans bound)
  have counts := component_counts_sum valid (fun i => decide (k ≤ rho i))
  change globalCount ps rho k = ((roots ps).map (fun r => highCount ps rho k r)).sum at counts
  rw [← counts,component_sizes_sum valid] at summed
  exact summed

open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfReceiverState Proofs.UfReceiverTrace Proofs.UfPopulationTrace
open Proofs.DoublingNested (i32)
open Proofs.CppLoop (Outcome)

theorem represented_global {s : NState} {layout : Layout} {ps : List Int} {groups : Int}
    {rank rho : Nat → Nat} (represented : Represents s layout ps groups rank)
    (history : HistoryWithPopulation ps rho) : GlobalPopulation ps rho := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  exact population_global inv.math history.2

theorem global_calls (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank historyRank : Nat → Nat)
    (represented : Represents s layout ps count rank) (history : HistoryWithPopulation ps historyRank)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank nextHistory answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Represents out layout vec nextCount nextRank ∧ HistoryWithPopulation vec nextHistory ∧ GlobalPopulation vec nextHistory ∧ vec.length = ps.length ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨fuels,out,vec,nextCount,nextRank,nextHistory,answers,ran,rep,hist,length,fl,al⟩ :=
    population_calls ops s layout ps count rank historyRank represented history allowed
  exact ⟨fuels,out,vec,nextCount,nextRank,nextHistory,answers,ran,rep,hist,
    represented_global rep hist,length,fl,al⟩

theorem constructed_global_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
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
      Represents out (layoutOf caller) vec count rank ∧ HistoryWithPopulation vec historyRank ∧ GlobalPopulation vec historyRank ∧ vec.length = n ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,fuels,out,vec,count,rank,historyRank,answers,constructed,ran,rep,hist,length,fl,al⟩ :=
    constructed_population_calls caller heap valid models lengths strict base en n small scalar type value ops allowed
  exact ⟨receiver,fuels,out,vec,count,rank,historyRank,answers,constructed,ran,rep,hist,
    represented_global rep hist,length,fl,al⟩

theorem default_global_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
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
      Represents out (layoutOf caller) vec count rank ∧ HistoryWithPopulation vec historyRank ∧ GlobalPopulation vec historyRank ∧ vec.length = 0 ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,fuels,out,vec,count,rank,historyRank,answers,constructed,ran,rep,hist,length,fl,al⟩ :=
    default_population_calls caller heap valid models lengths strict base ops allowed
  exact ⟨receiver,fuels,out,vec,count,rank,historyRank,answers,constructed,ran,rep,hist,
    represented_global rep hist,length,fl,al⟩

end Proofs.UfGlobalPopulation
