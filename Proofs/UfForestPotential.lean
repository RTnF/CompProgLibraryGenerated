import Proofs.UfPotential

namespace Proofs.UfForestPotential
open Proofs.UfPotential Proofs.UfHistoricalRank Proofs.UfClassInvariant
open Proofs.UfRootCall Proofs.UfFindCall Proofs.UfCompression Proofs.UfMergeInvariant

noncomputable def vertexPotential (n : Nat) (ps : List Int) (rho : Nat → Nat) (i : Nat) : Nat :=
  match ps[i]? with
  | none => 0
  | some value => if value < 0 then alpha n*rho i else nodePotential n (rho i) (rho value.toNat)

noncomputable def forestPotential (ps : List Int) (rho : Nat → Nat) : Nat :=
  ((List.range ps.length).map (vertexPotential ps.length ps rho)).sum

theorem sum_map_le (l : List Nat) (f g : Nat → Nat) (bounds : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have head := bounds i (by simp)
    have tail := ih (fun j member => bounds j (by simp [member]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem vertex_zero (n : Nat) (ps : List Int) (i : Nat) :
    vertexPotential n ps (fun _ => 0) i = 0 := by
  cases found : ps[i]? with
  | none => simp [vertexPotential,found]
  | some value => by_cases negative : value < 0 <;> simp [vertexPotential,found,negative,nodePotential_zero]

theorem forest_zero (ps : List Int) : forestPotential ps (fun _ => 0) = 0 := by
  unfold forestPotential
  have all : ∀ (l : List Nat), (l.map (vertexPotential ps.length ps (fun _ => 0))).sum = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simp [vertex_zero,ih]
  exact all _

theorem path_has_parent {ps vec : List Int} {a root i : Nat}
    (compressed : Compressed ps vec a root) (path : PathSet ps a root i) :
    ∃ p : Nat, ps[i]? = some (p : Int) := by
  have reaches := path_reaches_root compressed path
  cases reaches with
  | refl i => exact False.elim (path.2 rfl)
  | step i p root parent rest => exact ⟨p,parent⟩

theorem vertex_compressed {ps vec : List Int} {groups : Int} {rank rho : Nat → Nat}
    (valid : Valid ps groups rank) (history : History ps rho) {a root : Nat}
    (compressed : Compressed ps vec a root) (i : Nat) :
    vertexPotential ps.length vec rho i ≤ vertexPotential ps.length ps rho i := by
  by_cases path : PathSet ps a root i
  · obtain ⟨p,parent⟩ := path_has_parent compressed path
    have updated := compression_node_potential_all valid history compressed path parent
    have rootNonnegative : ¬ (root : Int) < 0 := by omega
    have parentNonnegative : ¬ (p : Int) < 0 := by omega
    simpa [vertexPotential,parent,updated.1,rootNonnegative,parentNonnegative] using updated.2
  · have same := (compressed.entries i).2 path
    simp [vertexPotential,same]

theorem forest_compressed {ps vec : List Int} {groups : Int} {rank rho : Nat → Nat}
    (valid : Valid ps groups rank) (history : History ps rho) {a root : Nat}
    (compressed : Compressed ps vec a root) : forestPotential vec rho ≤ forestPotential ps rho := by
  unfold forestPotential
  rw [compressed.length]
  exact sum_map_le _ _ _ (fun i _ => vertex_compressed valid history compressed i)

theorem sum_map_one_error (l : List Nat) (nodup : l.Nodup) (X : Nat) (member : X ∈ l)
    (f g : Nat → Nat) (error : Nat) (head : f X ≤ g X+error)
    (others : ∀ i ∈ l, i ≠ X → f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum+error := by
  induction l with
  | nil => simp at member
  | cons a l ih =>
    obtain ⟨notMember,tailDup⟩ := List.nodup_cons.mp nodup
    by_cases same : a = X
    · subst a
      have tail := sum_map_le l f g (by
        intro i inside
        have different : i ≠ X := by intro eq; subst i; exact notMember inside
        exact others i (by simp [inside]) different)
      simp only [List.map_cons,List.sum_cons]
      omega
    · have inside : X ∈ l := by simpa [Ne.symm same] using member
      have tail := ih tailDup inside (fun i mem different => others i (by simp [mem]) different)
      have first := others a (by simp) same
      simp only [List.map_cons,List.sum_cons]
      omega

theorem forest_linked (ps : List Int) (rank rho : Nat → Nat) (groups : Int)
    (valid : Valid ps groups rank) (history : History ps rho)
    (X Y : Nat) (vx vy : Int) (fx : ps[X]? = some vx) (fy : ps[Y]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (different : X ≠ Y) (smaller : -vy ≤ -vx) :
    forestPotential (linked ps X Y (vx+vy)) (promote rho X (Nat.log2 (-(vx+vy)).toNat)) ≤
      forestPotential ps rho+alpha ps.length := by
  have ix := (List.getElem?_eq_some_iff.mp fx).1
  have iy := (List.getElem?_eq_some_iff.mp fy).1
  have negative : vx+vy < 0 := by omega
  obtain ⟨nextRank,nextValid⟩ := valid.linked X Y vx vy fx fy nx ny different
  have nextHistory := merge_preserves ps rho history.1 history.2 X Y vx vy fx fy nx ny different smaller
  have winner : vertexPotential ps.length (linked ps X Y (vx+vy))
      (promote rho X (Nat.log2 (-(vx+vy)).toNat)) X ≤ vertexPotential ps.length ps rho X+alpha ps.length := by
    have upper := winner_rank_upper ps rho history.2 X Y vx vy fx fy nx ny smaller
    have product := Nat.mul_le_mul_left (alpha ps.length) upper
    simpa [vertexPotential,linked_x ps X Y (vx+vy) ix different,fx,nx,negative,promote,Nat.mul_add] using product
  have loser : vertexPotential ps.length (linked ps X Y (vx+vy))
      (promote rho X (Nat.log2 (-(vx+vy)).toNat)) Y ≤ vertexPotential ps.length ps rho Y := by
    have parentNonnegative : ¬ (X : Int) < 0 := by omega
    have upper := nodePotential_upper ps.length (rho Y) (Nat.log2 (-(vx+vy)).toNat)
    simpa [vertexPotential,linked_y ps X Y (vx+vy) iy,fy,ny,parentNonnegative,promote,Ne.symm different] using upper
  have other : ∀ i, i ≠ X → i ≠ Y →
      vertexPotential ps.length (linked ps X Y (vx+vy))
        (promote rho X (Nat.log2 (-(vx+vy)).toNat)) i ≤ vertexPotential ps.length ps rho i := by
    intro i notX notY
    have same := linked_other ps X Y i (vx+vy) notX notY
    cases entry : ps[i]? with
    | none => simp [vertexPotential,same,entry]
    | some value =>
      by_cases root : value < 0
      · simp [vertexPotential,same,entry,root,promote,notX]
      · have nonnegative : 0 ≤ value := by omega
        have inside : value.toNat < ps.length := by
          have bound := valid.forest.inside i value entry nonnegative
          omega
        have newBound : promote rho X (Nat.log2 (-(vx+vy)).toNat) value.toNat ≤ ps.length := by
          have rootBound := historical_rank_bound nextValid nextHistory value.toNat (by simpa [linked] using inside)
          simpa only [linked,List.length_set] using rootBound.trans (Nat.log2_le_self _)
        have parent : ps[i]? = some (value.toNat : Int) := by
          rw [Int.toNat_of_nonneg nonnegative]
          exact entry
        have oldEdge := history.1 i value.toNat parent
        have growth := (merge_rank_pointwise ps rho history.2 X Y vx vy fx fy nx ny smaller value.toNat).1
        have potential : nodePotential ps.length (rho i)
            (promote rho X (Nat.log2 (-(vx+vy)).toNat) value.toNat) ≤
            nodePotential ps.length (rho i) (rho value.toNat) := by
          by_cases zero : rho i = 0
          · simp [zero,nodePotential_zero]
          · exact nodePotential_parent_mono ps.length (rho i) (rho value.toNat) _ (by omega) oldEdge growth newBound
        simpa only [vertexPotential,same,entry,if_neg root,promote,if_neg notX] using potential
  unfold forestPotential
  rw [show (linked ps X Y (vx+vy)).length = ps.length from by simp [linked]]
  apply sum_map_one_error _ List.nodup_range X (List.mem_range.mpr ix) _ _ _ winner
  intro i member notX
  by_cases same : i = Y
  · subst i; exact loser
  · exact other i notX same

open Proofs.UfUniteCall

theorem unite_potential {ps : List Int} {rank rho : Nat → Nat} {groups : Int}
    (valid : Valid ps groups rank) (history : History ps rho)
    (r1 r2 : Nat) (root1 : ∃ w, ps[r1]? = some w ∧ w < 0)
    (root2 : ∃ w, ps[r2]? = some w ∧ w < 0) :
    ∃ nextRho, History (uniteVec ps r1 r2) nextRho ∧
      forestPotential (uniteVec ps r1 r2) nextRho ≤ forestPotential ps rho+alpha ps.length := by
  by_cases same : r1 = r2
  · refine ⟨rho,by simpa [uniteVec,same] using history,?_⟩
    simpa only [uniteVec,if_pos same] using Nat.le_add_right (forestPotential ps rho) (alpha ps.length)
  · obtain ⟨v1,f1,n1⟩ := root1
    obtain ⟨v2,f2,n2⟩ := root2
    by_cases swap : 0-ps.getD r1 0 < 0-ps.getD r2 0
    · have smaller : -v1 ≤ -v2 := by
        have compare : -v1 < -v2 := by
          simpa only [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2,zero_sub] using swap
        omega
      have hist := merge_preserves ps rho history.1 history.2 r2 r1 v2 v1 f2 f1 n2 n1 (Ne.symm same) smaller
      have pot := forest_linked ps rank rho groups valid history r2 r1 v2 v1 f2 f1 n2 n1 (Ne.symm same) smaller
      refine ⟨promote rho r2 (Nat.log2 (-(v2+v1)).toNat),?_⟩
      simp only [uniteVec,if_neg same,uniteX,uniteY,if_pos swap]
      rw [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2]
      simpa only [History,linked,Int.add_comm] using And.intro hist pot
    · have smaller : -v2 ≤ -v1 := by
        have compare : ¬ (-v1 < -v2) := by
          simpa only [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2,zero_sub] using swap
        omega
      have hist := merge_preserves ps rho history.1 history.2 r1 r2 v1 v2 f1 f2 n1 n2 same smaller
      have pot := forest_linked ps rank rho groups valid history r1 r2 v1 v2 f1 f2 n1 n2 same smaller
      refine ⟨promote rho r1 (Nat.log2 (-(v1+v2)).toNat),?_⟩
      simp only [uniteVec,if_neg same,uniteX,uniteY,if_neg swap]
      rw [getD_of ps r1 v1 f1,getD_of ps r2 v2 f2]
      exact ⟨hist,pot⟩

open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.UfReceiverState Proofs.UfReceiverTrace
open Proofs.CppLoop (Outcome)
open Proofs.UfBalancedReceiver (root_kept)
open Proofs.DoublingNested (i32)

-- This allowance bounds potential growth, not executable work.
noncomputable def potentialAllowance (n : Nat) : Operation → Nat
  | .unite _ _ => alpha n
  | _ => 0

noncomputable def potentialAllowances (n : Nat) (ops : List Operation) : Nat :=
  (ops.map (potentialAllowance n)).sum

theorem potential_step (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank rho : Nat → Nat) (represented : Represents s layout ps count rank)
    (history : History ps rho) (op : Operation) (allowed : op.allowed ps.length) :
    ∃ fuel out vec nextCount nextRank nextRho answer,
      call fuel s layout op = .finished (out,.scalar answer) ∧
      Represents out layout vec nextCount nextRank ∧ History vec nextRho ∧ vec.length = ps.length ∧
      forestPotential vec nextRho ≤ forestPotential ps rho+potentialAllowance ps.length op := by
  have math : Valid ps count rank := by
    obtain ⟨buf,cb,nb,inv⟩ := represented
    exact inv.math
  cases op with
  | root a =>
    obtain ⟨fuel,out,r,vec,ran,c,rep⟩ := root_step s layout ps count rank represented a allowed
    exact ⟨fuel,out,vec,count,rank,rho,(r : Int),ran,rep,history_compressed history c,c.length,
      by simpa [potentialAllowance] using forest_compressed math history c⟩
  | size a =>
    obtain ⟨fuel,out,r,vec,ran,c,rep⟩ := size_step s layout ps count rank represented a allowed
    exact ⟨fuel,out,vec,count,rank,rho,((component ps a).length : Int),ran,rep,history_compressed history c,c.length,
      by simpa [potentialAllowance] using forest_compressed math history c⟩
  | same a b =>
    obtain ⟨fuel,out,r1,r2,middle,vec,ran,c1,c2,connected,rep⟩ := same_step s layout ps count rank represented a b allowed.1 allowed.2
    have hist1 := history_compressed history c1
    have compressed := (forest_compressed (math.compressed c1) hist1 c2).trans (forest_compressed math history c1)
    exact ⟨fuel,out,vec,count,rank,rho,(if r1=r2 then 1 else 0),ran,rep,history_compressed hist1 c2,c2.length.trans c1.length,
      by simpa [potentialAllowance] using compressed⟩
  | unite a b =>
    obtain ⟨fuel,out,r1,r2,middle,two,vec,nextRank,ran,c1,c2,finalEq,connected,length,rep⟩ :=
      unite_step s layout ps count rank represented a b allowed.1 allowed.2
    have hist1 := history_compressed history c1
    have hist2 := history_compressed hist1 c2
    obtain ⟨nextRho,hist,pot⟩ := unite_potential ((math.compressed c1).compressed c2) hist2 r1 r2
      (root_kept c2 (root_kept c1 c1.root)) (root_kept c2 c2.root)
    have finalHist : History vec nextRho := by rw [finalEq]; exact hist
    have compressed := (forest_compressed (math.compressed c1) hist1 c2).trans (forest_compressed math history c1)
    have len2 := c2.length.trans c1.length
    rw [len2] at pot
    have finalPot : forestPotential vec nextRho ≤ forestPotential ps rho+alpha ps.length := by
      rw [finalEq]
      exact pot.trans (Nat.add_le_add_right compressed _)
    exact ⟨fuel,out,vec,Proofs.UfFieldsUnite.countAfter count r1 r2,nextRank,nextRho,(uniteX two r1 r2 : Int),
      ran,rep,finalHist,length,finalPot⟩
  | numGroups =>
    obtain ⟨fuel,out,ran,rep⟩ := getter_step s layout ps count rank represented
    exact ⟨fuel,out,ps,count,rank,rho,count,ran,rep,history,rfl,by simp [potentialAllowance]⟩

theorem potential_calls (ops : List Operation) (s : NState) (layout : Layout)
    (ps : List Int) (count : Int) (rank rho : Nat → Nat)
    (represented : Represents s layout ps count rank) (history : History ps rho)
    (allowed : ∀ op ∈ ops, op.allowed ps.length) :
    ∃ fuels out vec nextCount nextRank nextRho answers,
      runCalls fuels ops s layout = .finished (out,answers) ∧
      Represents out layout vec nextCount nextRank ∧ History vec nextRho ∧ vec.length = ps.length ∧
      forestPotential vec nextRho ≤ forestPotential ps rho+potentialAllowances ps.length ops ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  induction ops generalizing s ps count rank rho with
  | nil => exact ⟨[],s,ps,count,rank,rho,[],rfl,represented,history,rfl,by simp [potentialAllowances],rfl,rfl⟩
  | cons op ops ih =>
    obtain ⟨fuel,middle,vec1,count1,rank1,rho1,answer,ran,rep,hist,length1,headPot⟩ :=
      potential_step s layout ps count rank rho represented history op (allowed op (by simp))
    have tailAllowed : ∀ other ∈ ops, other.allowed vec1.length := by
      intro other member
      rw [length1]
      exact allowed other (by simp [member])
    obtain ⟨fuels,out,vec,count2,rank2,rho2,answers,tailRun,finalRep,finalHist,length2,tailPot,fl,al⟩ :=
      ih middle vec1 count1 rank1 rho1 rep hist tailAllowed
    rw [length1] at tailPot
    have total : forestPotential vec rho2 ≤ forestPotential ps rho+potentialAllowances ps.length (op::ops) := by
      change forestPotential vec rho2 ≤ forestPotential ps rho+
        (potentialAllowance ps.length op+potentialAllowances ps.length ops)
      omega
    refine ⟨fuel::fuels,out,vec,count2,rank2,rho2,answer::answers,?_,finalRep,finalHist,
      length2.trans length1,total,by simp [fl],by simp [al]⟩
    simp only [runCalls,ran,bind,Outcome.bind,tailRun,pure]

theorem constructed_potential_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
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
      Represents out (layoutOf caller) vec count rank ∧ History vec historyRank ∧ vec.length = n ∧ forestPotential vec historyRank ≤ potentialAllowances n ops ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,rep⟩ := construct_sized caller heap valid models lengths strict base en n small scalar type value
  obtain ⟨fuels,out,vec,count,rank,rho,answers,ran,finalRep,hist,length,pot,fl,al⟩ :=
    potential_calls ops receiver (layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) (fun _ => 0)
      rep (initial_history n) (by simpa using allowed)
  simp only [forest_zero,List.length_replicate,Nat.zero_add] at pot
  exact ⟨receiver,fuels,out,vec,count,rank,rho,answers,constructed,ran,finalRep,hist,by simpa using length,pot,fl,al⟩

theorem default_potential_calls (caller : NState) (heap : Proofs.CppRootModel.Heap)
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
      Represents out (layoutOf caller) vec count rank ∧ History vec historyRank ∧ vec.length = 0 ∧ forestPotential vec historyRank ≤ potentialAllowances 0 ops ∧
      fuels.length = ops.length ∧ answers.length = ops.length := by
  obtain ⟨receiver,constructed,rep⟩ := construct_default caller heap valid models lengths strict base
  obtain ⟨fuels,out,vec,count,rank,rho,answers,ran,finalRep,hist,length,pot,fl,al⟩ :=
    potential_calls ops receiver (layoutOf caller) [] 0 (fun _ => 0) (fun _ => 0)
      rep (initial_history 0) allowed
  simp only [forest_zero,List.length_nil,Nat.zero_add] at pot
  exact ⟨receiver,fuels,out,vec,count,rank,rho,answers,constructed,ran,finalRep,hist,length,pot,fl,al⟩

open Proofs.UfPotential (alpha)

theorem allowance_count (n : Nat) (ops : List Operation) :
    potentialAllowances n ops =
      ((ops.filter (fun op => match op with | .unite _ _ => true | _ => false)).length)*alpha n := by
  induction ops with
  | nil => simp [potentialAllowances]
  | cons op ops ih =>
    cases op <;> simp [potentialAllowances,potentialAllowance,Nat.add_mul,Nat.add_comm] at * <;> omega

end Proofs.UfForestPotential
