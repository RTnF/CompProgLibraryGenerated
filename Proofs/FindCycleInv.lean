import Proofs.LowlinkInv

namespace Proofs.FindCycleInv
open Proofs.PrimMath (Rtc)
open Proofs.LowlinkInv (upd upd_same upd_ne AdjH)

/-- The CSR graph: monotone offsets, arcs stay inside `[0, n)`. -/
structure FGH (n : Nat) (hd tg : Nat → Nat) : Prop where
  mono : ∀ x, x < n → hd x ≤ hd (x + 1)
  adj_lt : ∀ x w, AdjH hd tg x w → x < n ∧ w < n

/-- The state of the iterative search: colours (0 white, 1 grey, 2 black), arc iterators, finishing times (ghost), the
stack, and the number of finished vertices (ghost). -/
structure FS where
  C : Nat → Int
  It : Nat → Int
  Fi : Nat → Int
  Sk : Nat → Nat
  sp : Nat
  nb : Nat

structure FInv (n : Nat) (hd tg : Nat → Nat) (st : FS) : Prop where
  c_rng : ∀ a, st.C a = 0 ∨ st.C a = 1 ∨ st.C a = 2
  c_lt : ∀ a, st.C a ≠ 0 → a < n
  sk_gray : ∀ i, i < st.sp → st.C (st.Sk i) = 1
  gray_sk : ∀ a, st.C a = 1 → ∃ i, i < st.sp ∧ st.Sk i = a
  sk_inj : ∀ i j, i < st.sp → j < st.sp → st.Sk i = st.Sk j → i = j
  sk_arc : ∀ i, i + 1 < st.sp → AdjH hd tg (st.Sk i) (st.Sk (i + 1))
  it_rng : ∀ a, st.C a ≠ 0 → (hd a : Int) ≤ st.It a ∧ st.It a ≤ (hd (a + 1) : Int)
  it_scan : ∀ a, st.C a ≠ 0 → ∀ q : Nat, hd a ≤ q → (q : Int) < st.It a → st.C (tg q) ≠ 0
  gray_scan : ∀ i, i < st.sp → ∀ q : Nat, hd (st.Sk i) ≤ q → (q : Int) < st.It (st.Sk i) →
    (st.C (tg q) = 2 ∧ st.Fi (tg q) < (st.nb : Int)) ∨ (i + 1 < st.sp ∧ tg q = st.Sk (i + 1))
  bl_fin : ∀ a, st.C a = 2 → 0 ≤ st.Fi a ∧ st.Fi a < (st.nb : Int)
  bl_done : ∀ a, st.C a = 2 → st.It a = (hd (a + 1) : Int) ∧
    ∀ q : Nat, hd a ≤ q → q < hd (a + 1) → st.C (tg q) = 2 ∧ st.Fi (tg q) < st.Fi a

theorem FInv.sp_le {n : Nat} {hd tg : Nat → Nat} {st : FS} (I : FInv n hd tg st) : st.sp ≤ n := by
  have hnd : ((List.range st.sp).map st.Sk).Nodup := by
    apply Proofs.PrimMath.nodup_map_inj List.nodup_range
    intro x hx y hy h
    exact I.sk_inj x y (List.mem_range.mp hx) (List.mem_range.mp hy) h
  have hsub : (List.range st.sp).map st.Sk ⊆ List.range n := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have := I.sk_gray i (List.mem_range.mp hi)
    exact List.mem_range.mpr (I.c_lt _ (by omega))
  have := List.Nodup.length_le_of_subset hnd hsub
  simpa using this

end Proofs.FindCycleInv
