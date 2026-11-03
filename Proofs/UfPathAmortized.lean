import Proofs.UfForestPotential

namespace Proofs.UfPathAmortized
open Proofs.UfClassInvariant Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression

inductive Trace (ps : List Int) : Nat → Nat → List Nat → Prop where
  | done (root : Nat) (value : Int) (found : ps[root]? = some value) (negative : value < 0) : Trace ps root root []
  | step (i p root : Nat) (nodes : List Nat) (parent : ps[i]? = some (p : Int))
      (tail : Trace ps p root nodes) : Trace ps i root (i::nodes)

theorem Trace.reaches {ps : List Int} {i root : Nat} {nodes : List Nat} (trace : Trace ps i root nodes) :
    Reach ps i root := by
  induction trace with
  | done root value found negative => exact .refl _
  | step i p root nodes parent tail ih => exact .step i p root parent ih

theorem Trace.root {ps : List Int} {i root : Nat} {nodes : List Nat} (trace : Trace ps i root nodes) :
    ∃ value, ps[root]? = some value ∧ value < 0 := by
  induction trace with
  | done root value found negative => exact ⟨value,found,negative⟩
  | step i p root nodes parent tail ih => exact ih

theorem Trace.inside {ps : List Int} {i root : Nat} {nodes : List Nat} (trace : Trace ps i root nodes) :
    i < ps.length := by
  cases trace with
  | done root value found negative => exact (List.getElem?_eq_some_iff.mp found).1
  | step i p root nodes parent tail => exact (List.getElem?_eq_some_iff.mp parent).1

theorem Trace.unique {ps : List Int} {i r1 r2 : Nat} {nodes1 nodes2 : List Nat}
    (first : Trace ps i r1 nodes1) (second : Trace ps i r2 nodes2) : r1 = r2 ∧ nodes1 = nodes2 := by
  induction first generalizing r2 nodes2 with
  | done root value found negative =>
    cases second with
    | done root value2 found2 negative2 => exact ⟨rfl,rfl⟩
    | step i p root nodes parent tail =>
      have eq := Option.some.inj (found.symm.trans parent)
      omega
  | step i p root nodes parent tail ih =>
    cases second with
    | done root value found negative =>
      have eq := Option.some.inj (found.symm.trans parent)
      omega
    | step i q root2 nodes2 parent2 tail2 =>
      have same := Option.some.inj (parent.symm.trans parent2)
      have eq : p = q := by omega
      subst q
      obtain ⟨rootEq,nodesEq⟩ := ih tail2
      exact ⟨rootEq,by simp [nodesEq]⟩

theorem trace_of_reach {ps : List Int} {i root : Nat} (reach : Reach ps i root) :
    (∃ value, ps[root]? = some value ∧ value < 0) → ∃ nodes, Trace ps i root nodes := by
  induction reach with
  | refl root =>
    rintro ⟨value,found,negative⟩
    exact ⟨[],.done root value found negative⟩
  | step i p root parent rest ih =>
    intro rootFound
    obtain ⟨nodes,tail⟩ := ih rootFound
    exact ⟨i::nodes,.step i p root nodes parent tail⟩

theorem trace_exists {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (i : Nat) (inside : i < ps.length) :
    ∃ root nodes, Trace ps i root nodes := by
  obtain ⟨out,root,run,ret,reach,rootInside,rootFound,rest⟩ :=
    body_exec_find [] ps rank valid.forest valid.length i inside (rank i+2) (by omega)
  obtain ⟨nodes,trace⟩ := trace_of_reach reach rootFound
  exact ⟨root,nodes,trace⟩

theorem length_exists {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (i : Nat) (inside : i < ps.length) :
    ∃ length, ∃ root nodes, Trace ps i root nodes ∧ nodes.length = length := by
  obtain ⟨root,nodes,trace⟩ := trace_exists valid i inside
  exact ⟨nodes.length,root,nodes,trace,rfl⟩

noncomputable def depth {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) (i : Nat) : Nat :=
  if inside : i < ps.length then Classical.choose (length_exists valid i inside) else 0

theorem depth_of_trace {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) {i root : Nat} {nodes : List Nat} (trace : Trace ps i root nodes) :
    depth valid i = nodes.length := by
  have inside := trace.inside
  simp only [depth,dite_eq_left inside]
  obtain ⟨selectedRoot,selectedNodes,selectedTrace,length⟩ := Classical.choose_spec (length_exists valid i inside)
  have same := (trace.unique selectedTrace).2
  rw [← same] at length
  exact length.symm

theorem depth_root {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) {root : Nat} {value : Int}
    (found : ps[root]? = some value) (negative : value < 0) : depth valid root = 0 :=
  depth_of_trace valid (.done root value found negative)

theorem depth_parent {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) {i p : Nat} (parent : ps[i]? = some (p : Int)) :
    depth valid i = depth valid p+1 := by
  have inside : p < ps.length := by
    have bound := valid.forest.inside i (p : Int) parent (by omega)
    omega
  obtain ⟨root,nodes,tail⟩ := trace_exists valid p inside
  have child := depth_of_trace valid (.step i p root nodes parent tail)
  have next := depth_of_trace valid tail
  simp only [List.length_cons] at child
  omega

theorem depth_forest {ps : List Int} {groups : Int} {rank : Nat → Nat}
    (valid : Valid ps groups rank) : Forest ps (depth valid) := by
  refine ⟨valid.forest.valid,valid.forest.inside,?_⟩
  intro i value found nonnegative
  have parent : ps[i]? = some (value.toNat : Int) := by
    rw [Int.toNat_of_nonneg nonnegative]
    exact found
  have equation := depth_parent valid parent
  omega

open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfReceiverState Proofs.UfReceiverTrace
open Proofs.DoublingNested (i32)

theorem root_work_trace (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) {a root : Nat} {nodes : List Nat}
    (trace : Trace ps a root nodes) :
    ∃ fuel out vec,
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a)]) = .finished (out,.scalar (root : Int)) ∧
      Compressed ps vec a root ∧ Represents out layout vec count rank ∧
      out.work ≤ s.work+91*nodes.length+142 := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have inside := trace.inside
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r,vec,prep,ran,compressed,forest,oldRun,post,ready,cells⟩ :=
    Proofs.UfRootReady.root_call_ready s inv.ok cb count inv.countCell inv.writable ps (depth inv.math) (depth_forest inv.math)
      inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
      rfl rfl rfl rfl inv.n_value (literal_value a av s) inside
  have same := root_unique compressed.reach trace.reaches compressed.root trace.root
  subst r
  have preserved := inv.readonly_transition out vec (inv.math.compressed compressed) compressed.length ready cells
  have scalarWork := post.scalarWork
  change out.scalars.work ≤ s.scalars.work+2+(90*depth inv.math a+140) at scalarWork
  have storageWork := post.storageWork
  simp only [depth_of_trace inv.math trace] at scalarWork storageWork
  refine ⟨fuel,out,vec,ran,compressed,preserved,?_⟩
  unfold NState.work
  omega

theorem root_work_exact_path (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (a : Nat) (inside : a < ps.length) :
    ∃ fuel out root vec nodes,
      Trace ps a root nodes ∧
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a)]) = .finished (out,.scalar (root : Int)) ∧
      Compressed ps vec a root ∧ Represents out layout vec count rank ∧
      out.work ≤ s.work+91*nodes.length+142 := by
  have valid : Valid ps count rank := by
    obtain ⟨buf,cb,nb,inv⟩ := represented
    exact inv.math
  obtain ⟨root,nodes,trace⟩ := trace_exists valid a inside
  obtain ⟨fuel,out,vec,ran,compressed,post,work⟩ := root_work_trace s layout ps count rank represented trace
  exact ⟨fuel,out,root,vec,nodes,trace,ran,compressed,post,work⟩


open Proofs.UfPotential

theorem iteration_cap (n r p : Nat) (positive : 0 < r) (edge : r < p) (bound : p ≤ n) :
    p < iterateNat (ack (level n r p)) (r+1) r := by
  have cutoff := level_next n r p positive edge bound
  rw [ack_repeat] at cutoff
  have start := repeat_mono_start (ack (level n r p)) (ack_right_strict _).monotone (r+1)
    (show 1 ≤ r by omega)
  exact cutoff.trans_le start

theorem index_next (n r p : Nat) (positive : 0 < r) (edge : r < p) (bound : p ≤ n) :
    p < iterateNat (ack (level n r p)) (index n r p+1) r := by
  have indices := index_bounds n r p positive edge
  by_cases below : index n r p < r
  · have absent : ¬ iterateNat (ack (level n r p)) (index n r p+1) r ≤ p :=
      Nat.findGreatest_is_greatest
        (P := fun j => iterateNat (ack (level n r p)) j r ≤ p) (n := r)
        (Nat.lt_succ_self _) (by omega)
    omega
  · have eq : index n r p = r := by omega
    simpa only [eq] using iteration_cap n r p positive edge bound

theorem level_antitone_rank (n rootRank : Nat) {r s : Nat} (growth : r ≤ s) :
    level n s rootRank ≤ level n r rootRank := by
  unfold level
  apply Nat.findGreatest_mono_left
  intro k eligible
  exact ((ack_right_strict k).monotone growth).trans eligible

-- An internal positive-rank node whose final level equals its parent's final
-- level pays one unit. Rank0, root neighbors and strict final-level drops still
-- need their own count; no bound on all traversals is claimed here.
theorem charged_edge_drop (n r p rootRank : Nat) (positive : 0 < r)
    (childEdge : r < p) (parentEdge : p < rootRank) (bound : rootRank ≤ n)
    (sameFinal : level n r rootRank = level n p rootRank) :
    nodePotential n r rootRank+1 ≤ nodePotential n r p := by
  have levels := level_mono_parent n r (show p ≤ rootRank by omega)
  by_cases increase : level n r p < level n r rootRank
  · exact Nat.succ_le_of_lt (nodePotential_level_drop n r p rootRank positive childEdge
      (by omega) (by omega) bound increase)
  · have same : level n r p = level n r rootRank := by omega
    have parentThreshold := level_spec n p rootRank parentEdge
    rw [← sameFinal,← same] at parentThreshold
    have oldIndex := index_spec n r p positive childEdge
    have nextOld : iterateNat (ack (level n r p)) (index n r p+1) r ≤ rootRank :=
      ((ack_right_strict (level n r p)).monotone oldIndex).trans parentThreshold
    have next : iterateNat (ack (level n r rootRank)) (index n r p+1) r ≤ rootRank := by
      simpa only [same] using nextOld
    have oldBound := (index_bounds n r p positive childEdge).2
    have below : index n r p < r := by
      by_contra notBelow
      have eq : index n r p = r := by omega
      rw [eq] at next
      have forbidden := iteration_cap n r rootRank positive (by omega) bound
      omega
    have newIndex : index n r p+1 ≤ index n r rootRank :=
      Nat.le_findGreatest
        (P := fun j => iterateNat (ack (level n r rootRank)) j r ≤ rootRank)
        (n := r) (m := index n r p+1) (by omega) next
    exact Nat.succ_le_of_lt (nodePotential_index_drop n r p rootRank positive childEdge
      (by omega) (by omega) bound same (by omega))

open Proofs.UfPotential Proofs.UfHistoricalRank Proofs.UfForestPotential

theorem Trace.cons_head {ps : List Int} {start root head : Nat} {tail : List Nat}
    (trace : Trace ps start root (head::tail)) : head = start := by
  cases trace with
  | step start p root nodes parent rest => rfl

theorem Trace.member_parent {ps : List Int} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) : ∀ v ∈ nodes, ∃ p : Nat, ps[v]? = some (p : Int) := by
  induction trace with
  | done root value found negative => simp
  | step i p root nodes parent tail ih =>
    intro v member
    rcases List.mem_cons.mp member with same | inside
    · subst v; exact ⟨p,parent⟩
    · exact ih v inside

theorem Trace.member_reaches {ps : List Int} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) : ∀ v ∈ nodes, Reach ps i v := by
  induction trace with
  | done root value found negative => simp
  | step i p root nodes parent tail ih =>
    intro v member
    rcases List.mem_cons.mp member with same | inside
    · subst v; exact .refl _
    · exact .step i p v parent (ih v inside)

theorem Trace.member_ne_root {ps : List Int} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) {v : Nat} (member : v ∈ nodes) : v ≠ root := by
  obtain ⟨p,parent⟩ := trace.member_parent v member
  obtain ⟨value,found,negative⟩ := trace.root
  intro same
  subst v
  have eq := Option.some.inj (found.symm.trans parent)
  omega

theorem Trace.path_member {ps : List Int} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) {v : Nat} (member : v ∈ nodes) : PathSet ps i root v :=
  ⟨trace.member_reaches v member,trace.member_ne_root member⟩

theorem Trace.member_inside {ps : List Int} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) {v : Nat} (member : v ∈ nodes) : v < ps.length := by
  obtain ⟨p,parent⟩ := trace.member_parent v member
  exact (List.getElem?_eq_some_iff.mp parent).1

theorem Trace.rank_lower {ps : List Int} {rho : Nat → Nat} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) (history : ParentRanks ps rho) : ∀ v ∈ nodes, rho i ≤ rho v := by
  induction trace with
  | done root value found negative => simp
  | step i p root nodes parent tail ih =>
    intro v member
    rcases List.mem_cons.mp member with same | inside
    · subst v; exact Nat.le_refl _
    · exact (history i p parent).le.trans (ih v inside)

theorem Trace.rank_pairwise {ps : List Int} {rho : Nat → Nat} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) (history : ParentRanks ps rho) :
    nodes.Pairwise (fun a b => rho a < rho b) := by
  induction trace with
  | done root value found negative => exact .nil
  | step i p root nodes parent tail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro v member
    exact (history i p parent).trans_le (tail.rank_lower history v member)

theorem Trace.nodup {ps : List Int} {rho : Nat → Nat} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) (history : ParentRanks ps rho) : nodes.Nodup := by
  apply List.Pairwise.imp _ (trace.rank_pairwise history)
  intro a b smaller same
  subst b
  omega

noncomputable def finalPath (n : Nat) (rho : Nat → Nat) (rootRank : Nat) (nodes : List Nat) : Nat :=
  (nodes.map (fun i => nodePotential n (rho i) rootRank)).sum

noncomputable def initialPath (n : Nat) (ps : List Int) (rho : Nat → Nat) (nodes : List Nat) : Nat :=
  (nodes.map (vertexPotential n ps rho)).sum

theorem vertex_parent (n : Nat) (ps : List Int) (rho : Nat → Nat) (i p : Nat)
    (parent : ps[i]? = some (p : Int)) :
    vertexPotential n ps rho i = nodePotential n (rho i) (rho p) := by
  have nonnegative : ¬ (p : Int) < 0 := by omega
  simp [vertexPotential,parent,nonnegative]

theorem Trace.positive_budget {ps : List Int} {rho : Nat → Nat} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) (history : ParentRanks ps rho) (n : Nat) :
    rho root ≤ n → 0 < rho i →
    nodes.length+finalPath n rho (rho root) nodes ≤ initialPath n ps rho nodes+level n (rho i) (rho root)+1 := by
  induction trace with
  | done root value found negative => intro bound positive; simp [finalPath,initialPath]
  | step i p root nodes parent tail ih =>
    intro bound positive
    have edge := history i p parent
    have growth := reach_mono history tail.reaches
    have monotone := nodePotential_parent_mono n (rho i) (rho p) (rho root) positive edge growth bound
    have tailBudget := ih bound (show 0 < rho p by omega)
    cases nodes with
    | nil =>
      simp only [List.length_cons,List.length_nil,finalPath,initialPath,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,Nat.add_zero,vertex_parent n ps rho i p parent]
      omega
    | cons j rest =>
      have eq := tail.cons_head
      subst j
      have parentEdge := reach_strict history tail.reaches (tail.member_ne_root (by simp))
      have levels := level_antitone_rank n (rho root) (Nat.le_of_lt edge)
      simp only [finalPath,initialPath,List.map_cons,List.sum_cons,List.length_cons,
        vertex_parent n ps rho i p parent] at *
      by_cases same : level n (rho i) (rho root) = level n (rho p) (rho root)
      · have drop := charged_edge_drop n (rho i) (rho p) (rho root) positive edge parentEdge bound same
        omega
      · omega

theorem Trace.path_budget {ps : List Int} {rho : Nat → Nat} {i root : Nat} {nodes : List Nat}
    (trace : Trace ps i root nodes) (history : ParentRanks ps rho) (n : Nat) (bound : rho root ≤ n) :
    nodes.length+finalPath n rho (rho root) nodes ≤ initialPath n ps rho nodes+alpha n+2 := by
  by_cases positive : 0 < rho i
  · have budget := trace.positive_budget history n bound positive
    have maxLevel : level n (rho i) (rho root) ≤ alpha n := Nat.findGreatest_le (P := fun k => ack k (rho i) ≤ rho root) _
    omega
  · have zero : rho i = 0 := by omega
    cases trace with
    | done root value found negative => simp [finalPath,initialPath]
    | step i p root nodes parent tail =>
      have edge := history i p parent
      have budget := tail.positive_budget history n bound (by omega)
      have maxLevel : level n (rho p) (rho root) ≤ alpha n := Nat.findGreatest_le (P := fun k => ack k (rho p) ≤ rho root) _
      simp only [finalPath,initialPath,List.map_cons,List.sum_cons,List.length_cons,
        vertex_parent n ps rho i p parent,zero,nodePotential_zero,Nat.zero_add] at *
      omega


theorem mapped_sum_perm {xs ys : List Nat} (perm : xs.Perm ys) (f : Nat → Nat) :
    (xs.map f).sum = (ys.map f).sum := by
  induction perm with
  | nil => rfl
  | cons x perm ih => simp only [List.map_cons,List.sum_cons,ih]
  | swap x y l => simp only [List.map_cons,List.sum_cons]; omega
  | trans first second ih1 ih2 => exact ih1.trans ih2

theorem sum_filter_bound (xs : List Nat) (pred : Nat → Bool) (f : Nat → Nat) :
    ((xs.filter pred).map f).sum ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases keep : pred x = true
    · simpa [List.filter_cons,keep] using Nat.add_le_add_left ih (f x)
    · simp only [List.filter_cons,keep,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons]
      omega

theorem subset_sum_bound (selected whole : List Nat) (unique : selected.Nodup)
    (wholeUnique : whole.Nodup) (subset : ∀ i ∈ selected, i ∈ whole) (f : Nat → Nat) :
    (selected.map f).sum ≤ (whole.map f).sum := by
  classical
  let filtered := whole.filter (fun i => decide (i ∈ selected))
  have filteredUnique : filtered.Nodup := List.Pairwise.filter _ wholeUnique
  have perm : selected.Perm filtered := (List.perm_ext_iff_of_nodup unique filteredUnique).mpr (by
    intro i
    simp only [filtered,List.mem_filter,decide_eq_true_eq]
    exact ⟨fun member => ⟨subset i member,member⟩,fun member => member.2⟩)
  rw [mapped_sum_perm perm f]
  exact sum_filter_bound whole _ f

theorem sum_deficit_account (xs : List Nat) (f g : Nat → Nat) (bound : ∀ i ∈ xs, f i ≤ g i) :
    (xs.map f).sum+(xs.map (fun i => g i-f i)).sum = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head := bound x (by simp)
    have tail := ih (fun i member => bound i (by simp [member]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem selected_change (selected whole : List Nat) (unique : selected.Nodup)
    (wholeUnique : whole.Nodup) (subset : ∀ i ∈ selected, i ∈ whole)
    (f g : Nat → Nat) (bound : ∀ i ∈ whole, f i ≤ g i) :
    (whole.map f).sum+(selected.map g).sum ≤ (whole.map g).sum+(selected.map f).sum := by
  have full := sum_deficit_account whole f g bound
  have part := sum_deficit_account selected f g (fun i member => bound i (subset i member))
  have deficits := subset_sum_bound selected whole unique wholeUnique subset (fun i => g i-f i)
  omega

theorem Trace.forest_budget {ps vec : List Int} {groups : Int} {rank rho : Nat → Nat}
    (valid : Valid ps groups rank) (history : History ps rho) {a root : Nat} {nodes : List Nat}
    (trace : Trace ps a root nodes) (compressed : Compressed ps vec a root) :
    nodes.length+forestPotential vec rho ≤ forestPotential ps rho+alpha ps.length+2 := by
  have change := selected_change nodes (List.range ps.length) (trace.nodup history.1)
    List.nodup_range (fun i member => List.mem_range.mpr (trace.member_inside member))
    (vertexPotential ps.length vec rho) (vertexPotential ps.length ps rho)
    (fun i _ => vertex_compressed valid history compressed i)
  have pathSum : (nodes.map (vertexPotential ps.length vec rho)).sum = finalPath ps.length rho (rho root) nodes := by
    unfold finalPath
    congr 1
    apply List.map_congr_left
    intro i member
    have update := (compressed.entries i).1 (trace.path_member member)
    have nonnegative : ¬ (root : Int) < 0 := by omega
    simp [vertexPotential,update,nonnegative]
  obtain ⟨value,found,negative⟩ := trace.root
  have rootInside := (List.getElem?_eq_some_iff.mp found).1
  have rankBound := historical_rank_bound valid history root rootInside
  have budget := trace.path_budget history.1 ps.length (rankBound.trans (Nat.log2_le_self _))
  unfold forestPotential
  rw [compressed.length]
  rw [pathSum] at change
  change nodes.length+_ ≤ _+alpha ps.length+2
  unfold initialPath at budget
  omega


theorem root_amortized (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank rho : Nat → Nat) (represented : Represents s layout ps count rank)
    (history : History ps rho) (a : Nat) (inside : a < ps.length) :
    ∃ fuel out, ∃ root : Nat, ∃ vec,
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a)]) = .finished (out,.scalar (root : Int)) ∧
      Compressed ps vec a root ∧ Represents out layout vec count rank ∧ History vec rho ∧
      out.work+91*forestPotential vec rho ≤
        s.work+91*forestPotential ps rho+324*(alpha ps.length+1) := by
  have valid : Valid ps count rank := by
    obtain ⟨buf,cb,nb,inv⟩ := represented
    exact inv.math
  obtain ⟨root,nodes,trace⟩ := trace_exists valid a inside
  obtain ⟨fuel,out,vec,ran,compressed,post,work⟩ := root_work_trace s layout ps count rank represented trace
  have potential := trace.forest_budget valid history compressed
  refine ⟨fuel,out,root,vec,ran,compressed,post,history_compressed history compressed,?_⟩
  omega

theorem alpha_positive_unit (n : Nat) : alpha n+1 ≤ 3*(diagonalAlpha n+1) := by
  have bound := alpha_diagonal_bound n
  omega

end Proofs.UfPathAmortized
