import Proofs.TreeRootMath
import Proofs.TopoSortMath

namespace Proofs.TreePathMath
open Proofs.TreeRootMath
open Proofs.TopoSortMath (HeadOK)

/-- `itr g i x`: apply `g` to `x` `i` times. -/
def itr (g : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | i + 1, x => g (itr g i x)

/-- A vertex `u` with an arc leaving it has `u < n`. -/
theorem arcs_lt (H T : List Nat) (n : Nat) (HK : HeadOK H T n) (u p : Nat) (hp : p ∈ arcs H u) : u < n := by
  classical
  apply Classical.byContradiction
  intro hge
  have hge' : n ≤ u := by omega
  have h0 : H.getD u 0 = if u = n then T.length else 0 := by
    by_cases hu : u = n
    · subst hu; rw [if_pos rfl]; exact HK.last
    · rw [if_neg hu]
      have : H.length ≤ u := by rw [HK.len]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
  have h1 : H.getD (u + 1) 0 = 0 := by
    have : H.length ≤ u + 1 := by rw [HK.len]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
  unfold arcs at hp
  rw [h1] at hp
  have : 0 - H.getD u 0 = 0 := Nat.zero_sub _
  rw [this] at hp
  simp at hp

/-- The chain of parents from `to` in the output of `tree_root`: it has `m = dep[to]` steps and reaches `root`, never before. -/
theorem tree_path_chain (H T : List Nat) (Cs : List Int) (n root Cb : Nat) (HK : HeadOK H T n) (r : St)
    (S : TreeSpec H T Cs n root Cb r) (tg : Nat) (htg : tg < n) (hr : 0 ≤ r.par.getD tg 0) :
    ∃ (ch : Nat → Nat) (m : Nat), m = (r.dep.getD tg 0).toNat ∧ m < n ∧ ch 0 = tg ∧ ch m = root ∧
      (∀ i, i < m → ch i ≠ root) ∧ (∀ i, i ≤ m → ch i < n) ∧
      (∀ i, i < m → ch i < r.par.length ∧ r.par.getD (ch i) 0 = ((ch (i + 1) : Nat) : Int)) := by
  obtain ⟨hPl, hDl, hCl, hproot, hdroot, hcroot, hreach, hstep, hdep⟩ := S
  let g : Nat → Nat := fun x => (r.par.getD x 0).toNat
  let ch : Nat → Nat := fun i => itr g i tg
  have chs : ∀ i, ch (i + 1) = g (ch i) := fun i => rfl
  obtain ⟨hd0, hdn, _⟩ := hdep tg htg hr
  refine ⟨ch, (r.dep.getD tg 0).toNat, rfl, by omega, rfl, ?_⟩
  -- the invariant along the chain
  have inv : ∀ i, i ≤ (r.dep.getD tg 0).toNat →
      ch i < n ∧ 0 ≤ r.par.getD (ch i) 0 ∧ r.dep.getD (ch i) 0 = r.dep.getD tg 0 - (i : Int) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨htg, hr, by show r.dep.getD tg 0 = _; simp⟩
    | succ i ih =>
      intro hi
      obtain ⟨hlt, hnn, hdv⟩ := ih (by omega)
      have hne : ch i ≠ root := by
        intro he
        rw [he, hdroot] at hdv
        omega
      obtain ⟨p, hp, _, hnn2, hdd, _⟩ := hstep (ch i) hlt hnn hne
      have hu : (r.par.getD (ch i) 0).toNat < n := arcs_lt H T n HK _ p hp
      refine ⟨?_, ?_, ?_⟩
      · rw [chs]; exact hu
      · rw [chs]; exact hnn2
      · rw [chs]
        show r.dep.getD (r.par.getD (ch i) 0).toNat 0 = _
        omega
  have hmroot : ch (r.dep.getD tg 0).toNat = root := by
    obtain ⟨hlt, hnn, hdv⟩ := inv _ (Nat.le_refl _)
    apply Classical.byContradiction
    intro hne
    obtain ⟨p, hp, _, hnn2, hdd, _⟩ := hstep _ hlt hnn hne
    have hu : (r.par.getD (ch (r.dep.getD tg 0).toNat) 0).toNat < n := arcs_lt H T n HK _ p hp
    obtain ⟨hd1, _, _⟩ := hdep _ hu hnn2
    omega
  refine ⟨hmroot, ?_, ?_, ?_⟩
  · intro i hi he
    obtain ⟨_, _, hdv⟩ := inv i (by omega)
    rw [he, hdroot] at hdv
    omega
  · intro i hi
    exact (inv i hi).1
  · intro i hi
    obtain ⟨hlt, hnn, _⟩ := inv i (by omega)
    refine ⟨by omega, ?_⟩
    rw [chs]
    show r.par.getD (ch i) 0 = (((r.par.getD (ch i) 0).toNat : Nat) : Int)
    omega

end Proofs.TreePathMath
