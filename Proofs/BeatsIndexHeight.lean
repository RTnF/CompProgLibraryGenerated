import Proofs.BeatsCapCtor
namespace Proofs.BeatsRep
open Proofs.BeatsModel

theorem index_root_of_power (h k L : Nat) (bound : (k+2)*2^(h+1) ≤ L+1) :
    2*k+2 < L := by
  have pow : 2^1 ≤ 2^(h+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have mul := Nat.mul_le_mul_left (k+2) pow
  change (k+2)*2 ≤ (k+2)*2^(h+1) at mul
  omega

theorem idx_of_height (t : BT) (k L : Nat) (bound : (k+2)*2^(t.height+1) ≤ L+1) :
    IdxOK t k L := by
  induction t generalizing k with
  | leaf nd =>
    exact index_root_of_power 0 k L bound
  | node nd tg l r ihl ihr =>
    have hl : 2^(l.height+1) ≤ 2^(max l.height r.height+1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hr : 2^(r.height+1) ≤ 2^(max l.height r.height+1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have left := Nat.mul_le_mul (by omega : 2*k+1+2 ≤ 2*(k+2)) hl
    have right := Nat.mul_le_mul (by omega : 2*k+2+2 ≤ 2*(k+2)) hr
    have eq : 2*(k+2)*2^(max l.height r.height+1) =
        (k+2)*2^((BT.node nd tg l r).height+1) := by
      simp only [BT.height, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [eq] at left right
    exact ⟨index_root_of_power _ k L bound,
      ihl _ (Nat.le_trans left bound), ihr _ (Nat.le_trans right bound)⟩

theorem original_range_child_indices (t : BT) (n : Nat) (shape : Shape 0 n t.skel)
    (range : 4*n < 2147483648) : IdxOK t 0 2147483647 := by
  have height := height_le_power_width 29 t 0 n shape
    (by change n-0 ≤ 536870912; omega)
  have pow : 2^(t.height+1) ≤ 2^30 := Nat.pow_le_pow_right (by decide) (by omega)
  apply idx_of_height
  have scaled := Nat.mul_le_mul_left 2 pow
  exact scaled

theorem constructor_index_bounds (n k : Nat) (range : 4*n < 2147483648)
    (scanned : k < 4*n) :
    k < 2147483648 ∧ 8*n+8 ≤ 4294967296 ∧ 2*k+2 < 8*n+8 := by
  omega

theorem idx_min : ∀ (sk : Sk) (k A B : Nat),
    IdxOKs sk k A → IdxOKs sk k B → IdxOKs sk k (min A B)
  | .leaf,k,A,B,a,b => by change 2*k+2 < min A B; change 2*k+2 < A at a; change 2*k+2 < B at b; omega
  | .node l r,k,A,B,a,b => by
      exact ⟨by have := a.1; have := b.1; omega,
        idx_min l _ A B a.2.1 b.2.1, idx_min r _ A B a.2.2 b.2.2⟩

theorem Capacities.shrink {b : Proofs.BeatsExec.BS} {L L' S : Nat}
    (h : Capacities b L S) (smaller : L' ≤ L) : Capacities b L' S :=
  ⟨Nat.le_trans smaller h.l0,Nat.le_trans smaller h.l1,Nat.le_trans smaller h.l2,
   Nat.le_trans smaller h.l3,Nat.le_trans smaller h.l4,Nat.le_trans smaller h.l5,
   Nat.le_trans smaller h.l6,Nat.le_trans smaller h.l7,Nat.le_trans smaller h.l8,
   h.lsk,h.lsl,h.lsr,Nat.le_trans smaller h.lent⟩

-- Arrays can have more than INT_MAX entries while actual operation indices
-- still fit in signed int. Use a lower representation bound for the methods.
theorem BRepS.cap_indices {n L S : Nat} {ys : List Int} {b : Proofs.BeatsExec.BS}
    {t : BT} {H : Heap} (r : BRepS n L S ys b t H) (range : 4*n < 2147483648) :
    BRepS n (min L 2147483647) S ys b t H where
  agree := r.agree
  shape := r.shape
  leaf := r.leaf
  inv := r.inv
  hrel := r.hrel
  valid := r.valid
  lens := Capacities.shrink r.lens (Nat.min_le_left _ _)
  idx := idx_min t.skel 0 L 2147483647 r.idx (original_range_child_indices t n r.shape range)
  lenok := r.lenok
  sp := r.sp
  ne := by
    have original := r.ne
    have inner := innerS_eq r.shape
    unfold innerOf at original ⊢
    omega
  nM := r.nM

end Proofs.BeatsRep
