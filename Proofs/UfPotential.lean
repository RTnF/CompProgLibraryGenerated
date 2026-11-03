import Proofs.UfGlobalPopulation

namespace Proofs.UfPotential
open Proofs.UfHistoricalRank

theorem merge_level_upper (a b : Nat) (positive : 0 < a) (smaller : b ≤ a) :
    Nat.log2 (a+b) ≤ Nat.log2 a+1 := by
  have upper := (Nat.log2_lt (by omega : a ≠ 0)).mp (Nat.lt_succ_self (Nat.log2 a))
  have next : 2^(Nat.log2 a+2) = 2^(Nat.log2 a+1)*2 := by
    rw [show Nat.log2 a+2 = (Nat.log2 a+1)+1 by omega,pow_succ]
  have total : a+b < 2^(Nat.log2 a+2) := by rw [next]; omega
  have bound := (Nat.log2_lt (by omega : a+b ≠ 0)).mpr total
  omega

theorem winner_rank_upper (ps : List Int) (rho : Nat → Nat) (roots : RootRanks ps rho)
    (X Y : Nat) (vx vy : Int) (fx : ps[X]? = some vx) (_fy : ps[Y]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (smaller : -vy ≤ -vx) :
    Nat.log2 (-(vx+vy)).toNat ≤ rho X+1 := by
  have total : (-(vx+vy)).toNat = (-vx).toNat+(-vy).toNat := by omega
  rw [roots X vx fx nx,total]
  exact merge_level_upper _ _ (by omega) (by omega)

-- The standard two-argument Ackermann recurrence, also used by the pinned
-- Mathlib/Computability/Ackermann.lean. No Computability imports are needed.
def ack : Nat → Nat → Nat
  | 0,n => n+1
  | m+1,0 => ack m 1
  | m+1,n+1 => ack m (ack (m+1) n)

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n+1 := by rw [ack]
@[simp] theorem ack_succ_zero (m : Nat) : ack (m+1) 0 = ack m 1 := by rw [ack]
@[simp] theorem ack_succ_succ (m n : Nat) : ack (m+1) (n+1) = ack m (ack (m+1) n) := by rw [ack]

@[simp] theorem ack_one (n : Nat) : ack 1 n = n+2 := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

theorem ack_positive : ∀ m n, 0 < ack m n
  | 0,n => by simp
  | m+1,0 => by rw [ack_succ_zero]; exact ack_positive m 1
  | m+1,n+1 => by rw [ack_succ_succ]; exact ack_positive m (ack (m+1) n)

theorem ack_succ_gt_one : ∀ m n, 1 < ack (m+1) n
  | 0,n => by simp
  | m+1,0 => by rw [ack_succ_zero]; exact ack_succ_gt_one m 1
  | m+1,n+1 => by rw [ack_succ_succ]; exact ack_succ_gt_one m (ack (m+2) n)

theorem ack_right_strict : ∀ m, StrictMono (ack m)
  | 0,a,b,h => by simpa using h
  | m+1,0,n+1,_ => by
    rw [ack_succ_zero,ack_succ_succ]
    exact ack_right_strict m (ack_succ_gt_one m n)
  | m+1,a+1,b+1,h => by
    rw [ack_succ_succ,ack_succ_succ]
    exact ack_right_strict m (ack_right_strict (m+1) (by omega : a < b))

theorem ack_right_growth (m n : Nat) : n < ack m n := by
  induction n with
  | zero => exact ack_positive m 0
  | succ n ih =>
    have increase : ack m n < ack m (n+1) := ack_right_strict m (by omega)
    omega

theorem ack_level_increase : ∀ m n, ack m n < ack (m+1) n
  | 0,n => by simp
  | m+1,0 => by simpa only [ack_succ_zero] using ack_level_increase m 1
  | m+1,n+1 => by
    rw [ack_succ_succ,ack_succ_succ]
    exact (ack_level_increase m (ack (m+1) n)).trans
      (ack_right_strict (m+1) (ack_level_increase (m+1) n))

theorem ack_left_mono (n : Nat) : Monotone (fun m => ack m n) := by
  intro a b inside
  induction b,inside using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ b inside ih => exact ih.trans (Nat.le_of_lt (ack_level_increase b n))

theorem ack_level_growth (m : Nat) : m+2 ≤ ack m 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have increase := ack_level_increase m 1
    omega

theorem ack_unbounded (n : Nat) : ∃ m, n < ack m 1 := by
  exact ⟨n,by have bound := ack_level_growth n; omega⟩

noncomputable def alpha (n : Nat) : Nat := Nat.find (ack_unbounded n)

theorem alpha_spec (n : Nat) : n < ack (alpha n) 1 := Nat.find_spec (ack_unbounded n)

theorem alpha_le {n m : Nat} (bound : n < ack m 1) : alpha n ≤ m :=
  Nat.find_min' (ack_unbounded n) bound

theorem alpha_mono {a b : Nat} (inside : a ≤ b) : alpha a ≤ alpha b :=
  alpha_le (by have bound := alpha_spec b; omega)

theorem diagonal_unbounded (n : Nat) : ∃ m, n < ack m m := ⟨n,ack_right_growth n n⟩
noncomputable def diagonalAlpha (n : Nat) : Nat := Nat.find (diagonal_unbounded n)

theorem fixed_vs_diagonal (m : Nat) : ack m m ≤ ack (m+2) 1 := by
  have grows := ack_level_growth (m+1)
  calc
    ack m m ≤ ack (m+1) m := ack_left_mono m (by omega)
    _ ≤ ack (m+1) (ack (m+1) 1) := (ack_right_strict (m+1)).monotone (by omega)
    _ = ack (m+2) 1 := by conv_rhs => rw [ack_succ_succ,ack_succ_zero]

theorem alpha_diagonal_bound (n : Nat) : alpha n ≤ diagonalAlpha n+2 := by
  have cutoff := Nat.find_spec (diagonal_unbounded n)
  exact alpha_le (cutoff.trans_le (fixed_vs_diagonal (diagonalAlpha n)))

def iterateNat (f : Nat → Nat) : Nat → Nat → Nat
  | 0,x => x
  | j+1,x => f (iterateNat f j x)

theorem repeat_mono_start (f : Nat → Nat) (mono : Monotone f) (j : Nat) :
    Monotone (iterateNat f j) := by
  induction j with
  | zero => intro a b h; exact h
  | succ j ih => intro a b h; exact mono (ih h)

theorem ack_repeat (m n : Nat) : ack (m+1) n = iterateNat (ack m) (n+1) 1 := by
  induction n with
  | zero => rw [ack_succ_zero]; rfl
  | succ n ih => rw [ack_succ_succ,ih]; rfl

noncomputable def level (n r p : Nat) : Nat :=
  Nat.findGreatest (fun k => ack k r ≤ p) (alpha n)

theorem level_spec (n r p : Nat) (edge : r < p) : ack (level n r p) r ≤ p :=
  Nat.findGreatest_spec (P := fun k => ack k r ≤ p) (n := alpha n) (Nat.zero_le _) (by simp; omega : ack 0 r ≤ p)

theorem level_below_alpha (n r p : Nat) (positive : 0 < r) (edge : r < p) (bound : p ≤ n) :
    level n r p < alpha n := by
  have upper : level n r p ≤ alpha n := Nat.findGreatest_le (P := fun k => ack k r ≤ p) _
  have spec := level_spec n r p edge
  have cutoff := (alpha_spec n).trans_le ((ack_right_strict (alpha n)).monotone (by omega : 1 ≤ r))
  by_contra notBelow
  have eq : level n r p = alpha n := by omega
  rw [eq] at spec
  omega

theorem level_next (n r p : Nat) (positive : 0 < r) (edge : r < p) (bound : p ≤ n) :
    p < ack (level n r p+1) r := by
  have below := level_below_alpha n r p positive edge bound
  have absent : ¬ ack (level n r p+1) r ≤ p :=
    Nat.findGreatest_is_greatest (P := fun k => ack k r ≤ p) (n := alpha n) (Nat.lt_succ_self _) (by omega)
  omega

theorem level_mono_parent (n r : Nat) {p q : Nat} (growth : p ≤ q) :
    level n r p ≤ level n r q := by
  unfold level
  apply Nat.findGreatest_mono_left
  intro k h
  exact h.trans growth

noncomputable def index (n r p : Nat) : Nat :=
  Nat.findGreatest (fun j => iterateNat (ack (level n r p)) j r ≤ p) r

theorem index_bounds (n r p : Nat) (positive : 0 < r) (edge : r < p) :
    1 ≤ index n r p ∧ index n r p ≤ r := by
  have spec := level_spec n r p edge
  exact ⟨Nat.le_findGreatest (P := fun j => iterateNat (ack (level n r p)) j r ≤ p) (n := r) (m := 1) (by omega) spec,Nat.findGreatest_le (P := fun j => iterateNat (ack (level n r p)) j r ≤ p) _⟩

theorem index_spec (n r p : Nat) (positive : 0 < r) (edge : r < p) :
    iterateNat (ack (level n r p)) (index n r p) r ≤ p :=
  Nat.findGreatest_spec (P := fun j => iterateNat (ack (level n r p)) j r ≤ p) (n := r) (by omega : 1 ≤ r) (level_spec n r p edge)

theorem index_mono_parent (n r : Nat) {p q : Nat} (growth : p ≤ q)
    (sameLevel : level n r p = level n r q) : index n r p ≤ index n r q := by
  simp only [index,← sameLevel]
  apply Nat.findGreatest_mono_left
  intro j h
  exact h.trans growth

noncomputable def nodePotential (n r p : Nat) : Nat :=
  (alpha n-level n r p)*r-index n r p

theorem index_fits_coefficient (n r p : Nat) (positive : 0 < r) (edge : r < p) (bound : p ≤ n) :
    index n r p ≤ (alpha n-level n r p)*r := by
  have below := level_below_alpha n r p positive edge bound
  have indices := index_bounds n r p positive edge
  have product := Nat.mul_le_mul_right r (show 1 ≤ alpha n-level n r p by omega)
  simp only [Nat.one_mul] at product
  omega

theorem nodePotential_account (n r p : Nat) (positive : 0 < r) (edge : r < p) (bound : p ≤ n) :
    nodePotential n r p+index n r p = (alpha n-level n r p)*r :=
  Nat.sub_add_cancel (index_fits_coefficient n r p positive edge bound)

theorem nodePotential_upper (n r p : Nat) : nodePotential n r p ≤ alpha n*r := by
  have coeff := Nat.mul_le_mul_right r (Nat.sub_le (alpha n) (level n r p))
  exact (Nat.sub_le _ _).trans coeff

theorem nodePotential_level_drop (n r p q : Nat) (positive : 0 < r)
    (edgeP : r < p) (edgeQ : r < q) (boundP : p ≤ n) (boundQ : q ≤ n)
    (growth : level n r p < level n r q) : nodePotential n r q < nodePotential n r p := by
  have pBelow := level_below_alpha n r p positive edgeP boundP
  have qBelow := level_below_alpha n r q positive edgeQ boundQ
  have pIndex := index_bounds n r p positive edgeP
  have qIndex := index_bounds n r q positive edgeQ
  have pAccount := nodePotential_account n r p positive edgeP boundP
  have qAccount := nodePotential_account n r q positive edgeQ boundQ
  have coefficient : alpha n-level n r q+1 ≤ alpha n-level n r p := by omega
  have product := Nat.mul_le_mul_right r coefficient
  simp only [Nat.add_mul,Nat.one_mul] at product
  omega

theorem nodePotential_index_drop (n r p q : Nat) (positive : 0 < r)
    (edgeP : r < p) (edgeQ : r < q) (boundP : p ≤ n) (boundQ : q ≤ n)
    (same : level n r p = level n r q) (growth : index n r p < index n r q) :
    nodePotential n r q < nodePotential n r p := by
  have pAccount := nodePotential_account n r p positive edgeP boundP
  have qAccount := nodePotential_account n r q positive edgeQ boundQ
  rw [← same] at qAccount
  omega

theorem nodePotential_parent_mono (n r p q : Nat) (positive : 0 < r) (edge : r < p)
    (growth : p ≤ q) (bound : q ≤ n) : nodePotential n r q ≤ nodePotential n r p := by
  have levels := level_mono_parent n r growth
  by_cases same : level n r p = level n r q
  · have indices := index_mono_parent n r growth same
    have pAccount := nodePotential_account n r p positive edge (by omega)
    have qAccount := nodePotential_account n r q positive (by omega) bound
    rw [← same] at qAccount
    omega
  · exact Nat.le_of_lt (nodePotential_level_drop n r p q positive edge (by omega) (by omega) bound (by omega))

theorem nodePotential_zero (n p : Nat) : nodePotential n 0 p = 0 := by simp [nodePotential]

theorem merge_rank_pointwise (ps : List Int) (rho : Nat → Nat) (roots : RootRanks ps rho)
    (X Y : Nat) (vx vy : Int) (fx : ps[X]? = some vx) (fy : ps[Y]? = some vy)
    (nx : vx < 0) (ny : vy < 0) (smaller : -vy ≤ -vx) (i : Nat) :
    rho i ≤ promote rho X (Nat.log2 (-(vx+vy)).toNat) i ∧
      promote rho X (Nat.log2 (-(vx+vy)).toNat) i ≤ rho i+1 := by
  by_cases same : i = X
  · subst i
    have lower := size_gives_growth ps rho roots X Y vx vy fx fy nx ny smaller
    have upper := winner_rank_upper ps rho roots X Y vx vy fx fy nx ny smaller
    simpa [promote] using And.intro lower.1 upper
  · simp [promote,same]

open Proofs.UfClassInvariant Proofs.UfFindCall Proofs.UfRootCall Proofs.UfCompression

theorem compression_node_potential {ps vec : List Int} {groups : Int} {rank rho : Nat → Nat}
    (valid : Valid ps groups rank) (history : History ps rho) {a root i p : Nat}
    (compressed : Compressed ps vec a root) (path : PathSet ps a root i)
    (parent : ps[i]? = some (p : Int)) (positive : 0 < rho i) :
    vec[i]? = some (root : Int) ∧
      nodePotential ps.length (rho i) (rho root) ≤ nodePotential ps.length (rho i) (rho p) := by
  have reaches := path_reaches_root compressed path
  have tail : Reach ps p root := by
    cases reaches with
    | refl i => exact False.elim (path.2 rfl)
    | step i j root edge rest =>
      have same := Option.some.inj (parent.symm.trans edge)
      have eq : p = j := by omega
      subst p
      exact rest
  have edgeRank := history.1 i p parent
  have growth := reach_mono history.1 tail
  obtain ⟨w,found,negative⟩ := compressed.root
  have rootInside := (List.getElem?_eq_some_iff.mp found).1
  have logarithmic := historical_rank_bound valid history root rootInside
  have bounded : rho root ≤ ps.length := logarithmic.trans (Nat.log2_le_self _)
  exact ⟨(compressed.entries i).1 path,
    nodePotential_parent_mono ps.length (rho i) (rho p) (rho root) positive edgeRank growth bounded⟩

theorem compression_node_potential_all {ps vec : List Int} {groups : Int} {rank rho : Nat → Nat}
    (valid : Valid ps groups rank) (history : History ps rho) {a root i p : Nat}
    (compressed : Compressed ps vec a root) (path : PathSet ps a root i)
    (parent : ps[i]? = some (p : Int)) :
    vec[i]? = some (root : Int) ∧
      nodePotential ps.length (rho i) (rho root) ≤ nodePotential ps.length (rho i) (rho p) := by
  by_cases zero : rho i = 0
  · refine ⟨(compressed.entries i).1 path,?_⟩
    simp [zero,nodePotential_zero]
  · exact compression_node_potential valid history compressed path parent (by omega)

open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.UfReceiverState Proofs.UfReceiverTrace

theorem root_call_potential (s : NState) (layout : Layout) (ps : List Int) (count : Int)
    (rank rho : Nat → Nat) (rep : Represents s layout ps count rank) (hist : History ps rho)
    (a : Nat) (inside : a < ps.length) :
    ∃ (fuel : Nat) (out : NState) (root : Nat) (vec : List Int),
      call fuel s layout (.root a) = .finished (out,.scalar (root : Int)) ∧
      Represents out layout vec count rank ∧
      ∀ (i p : Nat), PathSet ps a root i → ps[i]? = some (p : Int) →
        vec[i]? = some (root : Int) ∧
        nodePotential ps.length (rho i) (rho root) ≤ nodePotential ps.length (rho i) (rho p) := by
  have math : Valid ps count rank := by
    obtain ⟨buf,cb,nb,inv⟩ := rep
    exact inv.math
  obtain ⟨fuel,out,root,vec,ran,compressed,post⟩ := root_step s layout ps count rank rep a inside
  refine ⟨fuel,out,root,vec,ran,post,?_⟩
  intro i p path parent
  exact compression_node_potential_all math hist compressed path parent

end Proofs.UfPotential
