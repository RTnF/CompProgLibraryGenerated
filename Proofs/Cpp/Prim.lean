import Proofs.Cpp.Gen.Prim
import Proofs.Cpp.Lib.Basic
import Proofs.Math.PrimBridge
import Proofs.Math.PrimExec

/-! # `prim` (library/graph/prim.hpp)

Prim's algorithm with a linear minimum scan on CSR arrays. The outer loop keeps the invariant `PInv` of
`Proofs.PrimStep` (the picked vertices `D` and their costs, as a ghost: `OSt`); the minimum scan (`SInv`), the fallback
to the first unpicked vertex of a new component (`FInv`) and the relaxation of the arcs of the picked vertex (`relaxL`)
are described on the arrays, and `PInv_step` advances the invariant (`outer_step`). `Proofs.PrimBridge.prim_msf` then
gives a minimum spanning forest. The theorems are stated for `Cost = long long` (`Int`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen
open Proofs.BellmanFordMath (Edge)
open Proofs.DijkstraMath (Eall)
open Proofs.DijkstraOldExec (doneOf outEdges)
open Proofs.PrimStep Proofs.PrimRelax

namespace Proofs.Cpp.Prim

def natA (a : Array Int) : List Nat := a.toList.map Int.toNat

/-- The edges of the CSR arrays. -/
abbrev EdL (head target cost : Array Int) (n : Nat) : List Proofs.BellmanFordMath.Edge := Eall n (Proofs.DijkstraOldExec.outEdges (natA head) (natA target) cost.toList)

/-- The outer state: the arrays hold a model state with the vertices `D` picked in order and their costs `cs`. -/
def OInv (head target cost : Array Int) (n : Nat) (inf : Int) (t : Nat) (d dn : Array Int) : Prop :=
  ∃ D cs, PInv n inf (EdL head target cost n) d.toList (natA dn) D cs ∧ D.length = t ∧
    dn.size = n ∧ ∀ k : Nat, 0 ≤ dn[k]!

/-- The minimum scan over the vertices `< k` of the arrays `d`, `dn`. -/
def SInv (d dn : Array Int) (inf : Int) (k : Nat) (best bd : Int) : Prop :=
  (best = -1 ∧ bd = inf ∧ ∀ v : Nat, v < k → dn[v]! = 0 → inf ≤ d[v]!) ∨
  (∃ b : Nat, best = b ∧ b < k ∧ dn[b]! = 0 ∧ d[b]! = bd ∧ bd < inf ∧ ∀ v : Nat, v < k → dn[v]! = 0 → bd ≤ d[v]!)

/-- The fallback scan: the first vertex not yet picked, with cost 0. -/
def FInv (dn : Array Int) (inf : Int) (k : Nat) (best bd : Int) : Prop :=
  (best = -1 ∧ bd = inf ∧ ∀ v : Nat, v < k → dn[v]! ≠ 0) ∨ (∃ b : Nat, best = b ∧ b < k ∧ dn[b]! = 0 ∧ bd = 0)

theorem natA_getD (a : Array Int) (k : Nat) : (natA a).getD k 0 = (a[k]!).toNat := by
  unfold natA
  by_cases h : k < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a k h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a k h]

theorem get_toList (a : Array Int) (i : Int) : get a i = a.toList.getD i.toNat 0 := by
  rw [get_eq]
  by_cases h : i.toNat < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a i.toNat h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a i.toNat h]

theorem nat_val (a : Array Int) (ha : ∀ k : Nat, 0 ≤ a[k]!) (k : Nat) :
    get a (k : Int) = (((natA a).getD k 0 : Nat) : Int) := by
  rw [get_eq, natA_getD]; simp; have := ha k; omega

theorem toList_set (a : Array Int) (i : Int) (x : Int) : (set a i x).toList = a.toList.set i.toNat x := by
  unfold Proofs.Cpp.set; simp [Array.set!, Array.toList_setIfInBounds]

theorem cur_eq {N : Int} {pref suff : List Int} {c : Int} (h : range 0 N = pref ++ c :: suff) :
    c = (pref.length : Int) ∧ (pref.length : Int) < N := by
  have e := range_cursor h
  have l := range_prefix_length h
  simp at e l; exact ⟨e, l⟩

theorem scan_step (d dn : Array Int) (inf : Int) (k : Nat) (best bd : Int) (S : SInv d dn inf k best bd) :
    (get dn k = 0 → get d k < bd → SInv d dn inf (k + 1) k (get d k)) ∧
    (get dn k = 0 → ¬get d k < bd → SInv d dn inf (k + 1) best bd) ∧
    (¬get dn k = 0 → SInv d dn inf (k + 1) best bd) := by
  simp only [get_eq, Int.toNat_natCast]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · right
    refine ⟨k, rfl, by omega, h1, rfl, ?_, fun v hv hdv => ?_⟩
    · rcases S with ⟨-, rfl, -⟩ | ⟨b, -, -, -, -, hb, -⟩ <;> omega
    · by_cases hvk : v = k
      · subst hvk; exact Int.le_refl _
      · rcases S with ⟨-, rfl, hall⟩ | ⟨b, -, -, -, -, -, hall⟩
        · have := hall v (by omega) hdv; omega
        · have := hall v (by omega) hdv; omega
  · rcases S with ⟨h1', h2', hall⟩ | ⟨b, hb1, hb2, hb3, hb4, hb5, hall⟩
    · refine Or.inl ⟨h1', h2', fun v hv hdv => ?_⟩
      by_cases hvk : v = k
      · subst hvk; omega
      · exact hall v (by omega) hdv
    · refine Or.inr ⟨b, hb1, by omega, hb3, hb4, hb5, fun v hv hdv => ?_⟩
      by_cases hvk : v = k
      · subst hvk; omega
      · exact hall v (by omega) hdv
  · rcases S with ⟨h1', h2', hall⟩ | ⟨b, hb1, hb2, hb3, hb4, hb5, hall⟩
    · refine Or.inl ⟨h1', h2', fun v hv hdv => ?_⟩
      by_cases hvk : v = k
      · subst hvk; exact absurd hdv h1
      · exact hall v (by omega) hdv
    · refine Or.inr ⟨b, hb1, by omega, hb3, hb4, hb5, fun v hv hdv => ?_⟩
      by_cases hvk : v = k
      · subst hvk; exact absurd hdv h1
      · exact hall v (by omega) hdv

theorem fb_step (dn : Array Int) (inf : Int) (k : Nat) (best bd : Int) (F : FInv dn inf k best bd) :
    (best < 0 → get dn k = 0 → FInv dn inf (k + 1) k 0) ∧
    (best < 0 → ¬get dn k = 0 → FInv dn inf (k + 1) best bd) ∧
    (¬best < 0 → FInv dn inf (k + 1) best bd) := by
  simp only [get_eq, Int.toNat_natCast]
  refine ⟨fun _ h2 => Or.inr ⟨k, rfl, by omega, h2, rfl⟩, fun h1 h2 => ?_, fun h1 => ?_⟩
  · rcases F with ⟨e1, e2, hall⟩ | ⟨b, rfl, -, -, -⟩
    · refine Or.inl ⟨e1, e2, fun v hv => ?_⟩
      by_cases hvk : v = k
      · subst hvk; exact h2
      · exact hall v (by omega)
    · omega
  · rcases F with ⟨rfl, -, -⟩ | ⟨b, hb1, hb2, hb3, hb4⟩
    · omega
    · exact Or.inr ⟨b, hb1, by omega, hb3, hb4⟩

theorem outEdges_get (H T : List Nat) (C : List Int) (b j : Nat) (hj : j < (outEdges H T C b).length) :
    (outEdges H T C b)[j] = (b, T.getD (H.getD b 0 + j) 0, C.getD (H.getD b 0 + j) 0) := by
  simp [outEdges]

theorem relax_step (head target cost : Array Int) (hhead : ∀ k : Nat, 0 ≤ head[k]!)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!) (b j : Nat) (dn1 d1 d : Array Int) (hdn1 : ∀ k : Nat, 0 ≤ dn1[k]!)
    (hj : j < (outEdges (natA head) (natA target) cost.toList b).length)
    (h : d.toList = ((outEdges (natA head) (natA target) cost.toList b).take j).foldl (relaxL (natA dn1)) d1.toList) :
    let q := get head (b : Int) + j
    (get dn1 (get target q) = 0 → get cost q < get d (get target q) →
      (set d (get target q) (get cost q)).toList =
        ((outEdges (natA head) (natA target) cost.toList b).take (j + 1)).foldl (relaxL (natA dn1)) d1.toList) ∧
    (get dn1 (get target q) = 0 → ¬get cost q < get d (get target q) →
      d.toList = ((outEdges (natA head) (natA target) cost.toList b).take (j + 1)).foldl (relaxL (natA dn1)) d1.toList) ∧
    (¬get dn1 (get target q) = 0 →
      d.toList = ((outEdges (natA head) (natA target) cost.toList b).take (j + 1)).foldl (relaxL (natA dn1)) d1.toList) := by
  intro q
  set p := (natA head).getD b 0 + j
  have hq : q = (p : Int) := by simp only [q]; rw [nat_val head hhead]; simp [p]
  set w := (natA target).getD p 0
  have hw : get target (p : Int) = (w : Int) := nat_val target htarget p
  have gc : get cost (p : Int) = cost.toList.getD p 0 := by rw [get_toList]; simp
  have gd : get d (w : Int) = d.toList.getD w 0 := by rw [get_toList]; simp
  have gn : get dn1 (w : Int) = 0 ↔ (natA dn1).getD w 0 = 0 := by
    rw [get_eq, Int.toNat_natCast, natA_getD]; have := hdn1 w; omega
  rw [List.take_succ, List.getElem?_eq_getElem hj, outEdges_get _ _ _ b j hj]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil, ← h]
  rw [hq, hw, gc, gd]
  unfold relaxL
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · rw [if_pos ⟨gn.mp h1, h2⟩, toList_set, Int.toNat_natCast]
  · rw [if_neg (fun hh => h2 hh.2)]
  · rw [if_neg (fun hh => h1 (gn.mpr hh.1))]

theorem set_nonneg (a : Array Int) (ha : ∀ k : Nat, 0 ≤ a[k]!) (i x : Int) (hx : 0 ≤ x) :
    ∀ k : Nat, 0 ≤ (set a i x)[k]! := by
  intro k
  by_cases hi : i.toNat < a.size
  · rw [getElemBang_set _ _ _ _ hi]; split
    · exact hx
    · exact ha k
  · have : set a i x = a := by
      unfold Proofs.Cpp.set; simp [Array.set!, Array.setIfInBounds, hi]
    rw [this]; exact ha k

theorem relax_vc (head target cost : Array Int) (hhead : ∀ k : Nat, 0 ≤ head[k]!)
    (htarget : ∀ k : Nat, 0 ≤ target[k]!) (best : Int) (hb : 0 ≤ best) (prefI suff : List Int) (cur : Int)
    (hr : range 0 (get head (best + 1) - get head best) = prefI ++ cur :: suff)
    (dn d1 d : Array Int) (hdn : ∀ k : Nat, 0 ≤ dn[k]!)
    (h : d.toList = ((outEdges (natA head) (natA target) cost.toList best.toNat).take prefI.length).foldl
      (relaxL (natA (set dn best 1))) d1.toList) :
    (get (set dn best 1) (get target (get head best + cur)) = 0 →
      get cost (get head best + cur) < get d (get target (get head best + cur)) →
      (set d (get target (get head best + cur)) (get cost (get head best + cur))).toList =
        ((outEdges (natA head) (natA target) cost.toList best.toNat).take (prefI.length + 1)).foldl
          (relaxL (natA (set dn best 1))) d1.toList) ∧
    (get (set dn best 1) (get target (get head best + cur)) = 0 →
      ¬get cost (get head best + cur) < get d (get target (get head best + cur)) →
      d.toList = ((outEdges (natA head) (natA target) cost.toList best.toNat).take (prefI.length + 1)).foldl
          (relaxL (natA (set dn best 1))) d1.toList) ∧
    (¬get (set dn best 1) (get target (get head best + cur)) = 0 →
      d.toList = ((outEdges (natA head) (natA target) cost.toList best.toNat).take (prefI.length + 1)).foldl
          (relaxL (natA (set dn best 1))) d1.toList) := by
  obtain ⟨rfl, hl⟩ := cur_eq hr
  have e : best = ((best.toNat : Nat) : Int) := by omega
  have hdn1 : ∀ k : Nat, 0 ≤ (set dn best 1)[k]! := set_nonneg dn hdn best 1 (by omega)
  have hj : prefI.length < (outEdges (natA head) (natA target) cost.toList best.toNat).length := by
    rw [Proofs.DijkstraOldExec.outEdges_length]
    rw [e, show ((best.toNat : Nat) : Int) + 1 = ((best.toNat + 1 : Nat) : Int) by simp, nat_val head hhead,
      nat_val head hhead] at hl
    omega
  have R := relax_step head target cost hhead htarget best.toNat prefI.length (set dn best 1) d1 d hdn1 hj h
  rw [← e] at R
  exact R

/-- The fallback finds a vertex not picked yet while fewer than `n` are picked. -/
theorem fb_found {n : Nat} {inf : Int} {E : List Proofs.BellmanFordMath.Edge} {Dd : List Int} {dn : Array Int}
    {D : List Nat} {cs : List Int} (I : PInv n inf E Dd (natA dn) D cs) (hlt : D.length < n)
    (hdn : ∀ k : Nat, 0 ≤ dn[k]!) (best bd : Int) (F : FInv dn inf n best bd) :
    ∃ b : Nat, best = b ∧ b < n ∧ dn[b]! = 0 ∧ bd = 0 := by
  rcases F with ⟨-, -, hall⟩ | h
  · exfalso
    have hsub : List.range n ⊆ D := by
      intro v hv
      have hvn := List.mem_range.mp hv
      have h1 := hall v hvn
      have h2 := natA_getD dn v
      rw [I.done, Proofs.DijkstraOldExec.doneOf_getD n D v hvn] at h2
      by_contra hvD
      rw [if_neg hvD] at h2
      have := hdn v; omega
    have := List.Nodup.length_le_of_subset List.nodup_range hsub
    simp at this; omega
  · exact h

/-- The outer invariant after `t` picks at tick count `c`. -/
def OSt (head target cost : Array Int) (n : Nat) (inf : Int) (t0 t : Nat) (d dn : Array Int) (c : Nat) : Prop :=
  ∃ D cs, PInv n inf (EdL head target cost n) d.toList (natA dn) D cs ∧ D.length = t ∧ dn.size = n ∧
    (∀ k : Nat, 0 ≤ dn[k]!) ∧ c + degSum n (natA head) D ≤ t0 + 1 + t * (1 + 2 * n) + degSum n (natA head) []

/-- The edge facts the model needs: heads and tails are vertices, costs in `[0, inf)`. -/
def EdOK (head target cost : Array Int) (n : Nat) (inf : Int) : Prop :=
  ∀ e ∈ EdL head target cost n, e.1 < n ∧ e.2.1 < n ∧ 0 ≤ e.2.2 ∧ e.2.2 < inf

theorem natA_set (a : Array Int) (i : Int) (x : Int) : natA (set a i x) = (natA a).set i.toNat x.toNat := by
  unfold natA; rw [toList_set, List.map_set]

theorem notin_of (n : Nat) (D : List Nat) (dn : Array Int) (hdone : natA dn = doneOf n D)
    (hnn : ∀ k : Nat, 0 ≤ dn[k]!) (v : Nat) (hv : v < n) : dn[v]! = 0 ↔ v ∉ D := by
  have h := natA_getD dn v
  rw [hdone, Proofs.DijkstraOldExec.doneOf_getD n D v hv] at h
  have := hnn v
  constructor
  · intro h0 hvD; rw [if_pos hvD, h0] at h; simp at h
  · intro hvD; rw [if_neg hvD] at h; omega

theorem dd_getD (d : Array Int) (v : Nat) : d.toList.getD v 0 = d[v]! := by
  by_cases h : v < d.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos d v h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg d v h]

theorem outer_step (head target cost : Array Int) (n : Nat) (inf : Int) (hE : EdOK head target cost n inf)
    (hinf0 : 0 ≤ inf) (t0 t : Nat) (d dn : Array Int) (so : Nat)
    (O : OSt head target cost n inf t0 t d dn so) (best bd : Int) (hb0 : 0 ≤ best) (hbn : best.toNat < n)
    (hcase : (bd < inf ∧ dn[best.toNat]! = 0 ∧ d[best.toNat]! = bd ∧ ∀ v : Nat, v < n → dn[v]! = 0 → bd ≤ d[v]!) ∨
      (dn[best.toNat]! = 0 ∧ bd = 0 ∧ ∀ v : Nat, v < n → dn[v]! = 0 → inf ≤ d[v]!))
    (r : Array Int)
    (hr : r.toList = (outEdges (natA head) (natA target) cost.toList best.toNat).foldl
      (relaxL (natA (set dn best 1))) (set d best bd).toList)
    (c : Nat) (hc : c ≤ so + 1 + 2 * n + ((natA head).getD (best.toNat + 1) 0 - (natA head).getD best.toNat 0)) :
    OSt head target cost n inf t0 (t + 1) r (set dn best 1) c := by
  obtain ⟨D, cs, I, hlen, hsz, hnn, hc0⟩ := O
  set b := best.toNat with hbdef
  have hD := I.done
  have hb1 : dn[b]! = 0 := by rcases hcase with ⟨-, h, -⟩ | ⟨h, -⟩ <;> exact h
  have hbD : b ∉ D := (notin_of n D dn hD hnn b hbn).mp hb1
  have hdn' : natA (set dn best 1) = doneOf n (D ++ [b]) := by
    rw [natA_set, hD, ← hbdef]; exact Proofs.DijkstraOldExec.doneOf_push n D b hbn
  have hd' : (set d best bd).toList = d.toList.set b bd := toList_set d best bd
  have hbnd := I.bnd b hbn
  rw [dd_getD] at hbnd
  have hbd0 : 0 ≤ bd ∧ bd ≤ inf := by
    rcases hcase with ⟨-, -, h, -⟩ | ⟨-, h, -⟩
    · rw [← h]; exact hbnd
    · rw [h]; exact ⟨Int.le_refl 0, hinf0⟩
  have hcase' : (bd < inf ∧ d.toList.getD b 0 = bd ∧ ∀ x, x < n → x ∉ D → bd ≤ d.toList.getD x 0) ∨
      (bd = 0 ∧ ∀ x, x < n → x ∉ D → inf ≤ d.toList.getD x 0) := by
    rcases hcase with ⟨h1, -, h3, h4⟩ | ⟨-, h2, h3⟩
    · exact Or.inl ⟨h1, by rw [dd_getD]; exact h3, fun x hx hxD => by
        rw [dd_getD]; exact h4 x hx ((notin_of n D dn hD hnn x hx).mpr hxD)⟩
    · exact Or.inr ⟨h2, fun x hx hxD => by rw [dd_getD]; exact h3 x hx ((notin_of n D dn hD hnn x hx).mpr hxD)⟩
  have hL : ∀ e ∈ outEdges (natA head) (natA target) cost.toList b, e ∈ EdL head target cost n ∧ e.1 = b := by
    intro e he
    refine ⟨Proofs.DijkstraMath.mem_Eall n _ b hbn e he, ?_⟩
    simp only [outEdges, List.mem_map] at he
    obtain ⟨q, -, rfl⟩ := he; rfl
  have hLcov : ∀ e ∈ EdL head target cost n, e.1 = b → e ∈ outEdges (natA head) (natA target) cost.toList b := by
    intro e he heb
    obtain ⟨u, -, hu⟩ := Proofs.DijkstraMath.mem_Eall_inv n _ e he
    have : e.1 = u := by
      simp only [outEdges, List.mem_map] at hu
      obtain ⟨q, -, rfl⟩ := hu; rfl
    rw [← heb, this]; exact hu
  have I' := PInv_step I _ b bd hE hL hLcov hbn hbD hbd0.1 hbd0.2 hinf0 hcase'
  have hdeg := degSum_push n (natA head) D b hbn hbD
  refine ⟨D ++ [b], cs ++ [bd], ?_, by simp [hlen], by simp [hsz], set_nonneg dn hnn best 1 (by omega), ?_⟩
  · rw [hr, hdn', hd']; exact I'
  · rw [Nat.add_mul, Nat.one_mul]; omega

theorem range_deg (head target cost : Array Int) (hhead : ∀ k : Nat, 0 ≤ head[k]!) (best : Int) (hb : 0 ≤ best) :
    (range 0 (get head (best + 1) - get head best)).length =
      (outEdges (natA head) (natA target) cost.toList best.toNat).length ∧
    (outEdges (natA head) (natA target) cost.toList best.toNat).length =
      (natA head).getD (best.toNat + 1) 0 - (natA head).getD best.toNat 0 := by
  obtain ⟨b, rfl⟩ : ∃ b : Nat, best = (b : Int) := ⟨best.toNat, by omega⟩
  rw [Proofs.DijkstraOldExec.outEdges_length, range_length]
  rw [show (b : Int) + 1 = ((b + 1 : Nat) : Int) by simp, nat_val head hhead, nat_val head hhead]
  simp only [Int.toNat_natCast]
  exact ⟨by omega, trivial⟩

theorem sinv_none (d dn : Array Int) (inf : Int) (k : Nat) (best bd : Int) (S : SInv d dn inf k best bd)
    (h : best < 0) : ∀ v : Nat, v < k → dn[v]! = 0 → inf ≤ d[v]! := by
  rcases S with ⟨-, -, h3⟩ | ⟨b, hb, -⟩
  · exact h3
  · omega

theorem outer_init (head target cost dist done : Array Int) (n : Nat) (inf : Int) (hinf0 : 0 ≤ inf)
    (hd : dist.size = n ∧ ∀ j : Nat, j < n → dist[j]! = inf)
    (hdn : done.size = n ∧ ∀ j : Nat, j < n → done[j]! = 0) (t0 : Nat) :
    OSt head target cost n inf t0 0 dist done (t0 + 1) := by
  have hdone : natA done = doneOf n [] := by
    apply List.ext_getElem
    · simp [natA, doneOf, hdn.1]
    · intro i h1 h2
      have hi : i < n := by simpa [natA, hdn.1] using h1
      have := hdn.2 i hi
      simp [natA, doneOf, getElem!_pos done i (by omega)] at this ⊢
      simp [this]
  refine ⟨[], [], ?_, rfl, hdn.1, fun k => ?_, by simp⟩
  · rw [hdone]
    exact PInv_init n inf _ dist.toList (by simp [hd.1]) (fun j hj => by rw [dd_getD]; exact hd.2 j hj) hinf0
  · by_cases hk : k < n
    · rw [hdn.2 k hk]
    · rw [getElem!_neg done k (by omega)]; simp

theorem prim_spec (head target cost dist done : Array Int) (n : Nat) (inf : Int)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!) (hE : EdOK head target cost n inf)
    (hinf0 : 0 ≤ inf) (hd : dist.size = n ∧ ∀ j : Nat, j < n → dist[j]! = inf)
    (hdn : done.size = n ∧ ∀ j : Nat, j < n → done[j]! = 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.prim (Cost := Int) head target cost dist done n inf
    ⦃⇓ r c => ⌜∃ s, OSt head target cost n inf t0 n r.2.1 r.2.2 s ∧
      r.1 = ((List.range n).map (fun v => r.2.1[v]!)).sum ∧ c = s + n⌝⦄ := by
  mvcgen [cp.prim]
  case inv1 =>
    exact ⇓⟨xs, d, dn⟩ c => ⌜OSt head target cost n inf t0 xs.prefix.length d dn c⌝
  case inv2 =>
    rename_i ob _ _ so _ _
    exact ⇓⟨xs, best, bd⟩ c => ⌜SInv ob.1 ob.2 inf xs.prefix.length best bd ∧ c = so + 1 + xs.prefix.length⌝
  case inv3 =>
    rename_i ob _ _ _ _ _ _ _ _ _ _ s2 _
    exact ⇓⟨xs, best, bd⟩ c => ⌜FInv ob.2 inf xs.prefix.length best bd ∧ c = s2 + xs.prefix.length⌝
  case inv4 =>
    rename_i bst _ dn1 d1 _ _ s3 _
    exact ⇓⟨xs, d⟩ c => ⌜d.toList = ((outEdges (natA head) (natA target) cost.toList bst.toNat).take xs.prefix.length).foldl
      (relaxL (natA dn1)) d1.toList ∧ c = s3 + xs.prefix.length⌝
  case inv5 =>
    rename_i bst _ _ _ dn1 d1 _ _ s3 _
    exact ⇓⟨xs, d⟩ c => ⌜d.toList = ((outEdges (natA head) (natA target) cost.toList bst.toNat).take xs.prefix.length).foldl
      (relaxL (natA dn1)) d1.toList ∧ c = s3 + xs.prefix.length⌝
  case inv6 =>
    rename_i _ _ r _ _ s4 _
    exact ⇓⟨xs, t⟩ c => ⌜t = ((List.range xs.prefix.length).map (fun v => r.1[v]!)).sum ∧ c = s4 + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  -- the minimum scan
  all_goals (try (obtain ⟨S, hc⟩ := ‹SInv _ _ _ _ _ _ ∧ _›
                  obtain ⟨rfl, -⟩ := cur_eq ‹range 0 (n : Int) = _ ++ _ :: _›
                  have D := scan_step _ _ _ _ _ _ S
                  first
                  | exact ⟨D.1 ‹_› ‹_›, by omega⟩
                  | exact ⟨D.2.1 ‹_› (Int.not_lt.mpr ‹_›), by omega⟩
                  | exact ⟨D.2.2 ‹_›, by omega⟩))
  -- the fallback scan
  all_goals (try (obtain ⟨F, hc⟩ := ‹FInv _ _ _ _ _ ∧ _ = _ + _›
                  obtain ⟨rfl, -⟩ := cur_eq ‹range 0 (n : Int) = _ ++ _ :: _›
                  have D := fb_step _ _ _ _ _ F
                  first
                  | exact ⟨D.1 ‹_› ‹_›, by omega⟩
                  | exact ⟨D.2.1 ‹_› ‹_›, by omega⟩
                  | exact ⟨D.2.2 (Int.not_lt.mpr ‹_›), by omega⟩))
  · exact Or.inl ⟨rfl, rfl, fun v hv => absurd hv (by omega)⟩
  · obtain ⟨S, -⟩ := ‹SInv _ _ _ _ _ _ ∧ _›
    rcases S with ⟨h1, h2, -⟩ | ⟨b, hb, -⟩
    · exact Or.inl ⟨h1, h2, fun v hv => absurd hv (by omega)⟩
    · have := ‹_ < (0 : Int)›; omega
  -- the relaxation of the arcs of the picked vertex
  all_goals (try (obtain ⟨D, cs, I, hlen, hsz, hnn, hc0⟩ := ‹OSt _ _ _ _ _ _ _ _ _ _›
                  obtain ⟨hd, hc⟩ := ‹_ = List.foldl (relaxL _) _ _ ∧ _›
                  have R := relax_vc head target cost hhead htarget _
                    (by first
                        | assumption
                        | (obtain ⟨-, ht⟩ := cur_eq ‹range 0 (n : Int) = _ ++ _ :: _›
                           obtain ⟨b, hb, -⟩ := fb_found I (by omega) hnn _ _ (‹FInv _ _ _ _ _ ∧ _›).1
                           rw [hb]; omega)) _ _ _
                    ‹range 0 (get head (_ + 1) - get head _) = _ ++ _ :: _› _ _ _ hnn hd
                  first
                  | exact ⟨R.1 ‹_› ‹_›, by omega⟩
                  | exact ⟨R.2.1 ‹_› (Int.not_lt.mpr ‹_›), by omega⟩
                  | exact ⟨R.2.2 ‹_›, by omega⟩))
  -- one pick: the fallback branch, then the direct branch
  · obtain ⟨hr, hc⟩ := ‹_ = List.foldl (relaxL _) _ _ ∧ _›
    obtain ⟨F, hc2⟩ := ‹FInv _ _ _ _ _ ∧ _›
    obtain ⟨S, hc1⟩ := ‹SInv _ _ _ _ _ _ ∧ _›
    have O := ‹OSt _ _ _ _ _ _ _ _ _ _›
    obtain ⟨D, cs, I, hlen, -, hnn, -⟩ := id O
    obtain ⟨-, ht⟩ := cur_eq ‹range 0 (n : Int) = _ ++ _ :: _›
    obtain ⟨b, hb, hbn, hb1, hbd⟩ := fb_found I (by omega) hnn _ _ F
    have hb0 : (0 : Int) ≤ (b : Int) := Int.natCast_nonneg b
    rw [← hb] at hb0
    obtain ⟨e1, e2⟩ := range_deg head target cost hhead _ hb0
    rw [e1, List.take_length] at hr
    rw [e1] at hc
    have hnone := sinv_none _ _ _ _ _ _ S ‹_ < (0 : Int)›
    have hbt := congrArg Int.toNat hb
    simp only [Int.toNat_natCast] at hbt
    refine outer_step head target cost n inf hE hinf0 t0 _ _ _ _ O _ _ hb0 (by rw [hbt]; exact hbn)
      (Or.inr ⟨by rw [hbt]; exact hb1, hbd, hnone⟩) _ hr _ (by omega)
  · obtain ⟨hr, hc⟩ := ‹_ = List.foldl (relaxL _) _ _ ∧ _›
    obtain ⟨S, hc1⟩ := ‹SInv _ _ _ _ _ _ ∧ _›
    have O := ‹OSt _ _ _ _ _ _ _ _ _ _›
    have hb0 := ‹(0 : Int) ≤ _›
    obtain ⟨e1, e2⟩ := range_deg head target cost hhead _ hb0
    rw [e1, List.take_length] at hr
    rw [e1] at hc
    rcases S with ⟨h1, -, -⟩ | ⟨b, hb, hbn, hb1, hb2, hb3, hb4⟩
    · omega
    · have hbt := congrArg Int.toNat hb
      simp only [Int.toNat_natCast] at hbt
      refine outer_step head target cost n inf hE hinf0 t0 _ _ _ _ O _ _ hb0 (by rw [hbt]; exact hbn)
        (Or.inl ⟨hb3, by rw [hbt]; exact hb1, by rw [hbt]; exact hb2, hb4⟩) _ hr _ (by omega)
  · obtain rfl := ‹_ = t0›
    exact outer_init head target cost dist done n inf hinf0 hd hdn _
  · obtain ⟨hb, hc⟩ := ‹_ = (List.map _ _).sum ∧ _›
    obtain ⟨rfl, -⟩ := cur_eq ‹range 0 (n : Int) = _ ++ _ :: _›
    refine ⟨?_, by omega⟩
    rw [hb, List.range_succ, List.map_append, List.sum_append]
    simp [get_eq]
  · obtain ⟨hb, hc⟩ := ‹_ = (List.map _ _).sum ∧ _›
    exact ⟨_, ‹OSt _ _ _ _ _ _ _ _ _ _›, hb, hc⟩

/-- `prim(head, target, cost, dist, done, n, inf)` on a symmetric graph in CSR form with costs in `[0, min(Cm, inf))`
(`EdOK`; every arc has its reverse): the returned total is the weight of a minimum spanning forest
(`Proofs.PrimBridge.IsMSF`); at most `2 + n (2 + 2n) + m` steps for `m` arcs (`degSum` of no picked vertex, at most
`head[n]`). The theorem is stated for `Cost = long long` (`Int`). -/
theorem prim_correct (head target cost dist done : Array Int) (n : Nat) (inf Cm : Int)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!) (hE : EdOK head target cost n inf)
    (hinf0 : 0 ≤ inf) (hCm : 0 ≤ Cm) (hEC : ∀ e ∈ EdL head target cost n, e.2.2 ≤ Cm)
    (hsym : ∀ e ∈ EdL head target cost n, (e.2.1, e.1, e.2.2) ∈ EdL head target cost n)
    (hd : dist.size = n ∧ ∀ j : Nat, j < n → dist[j]! = inf)
    (hdn : done.size = n ∧ ∀ j : Nat, j < n → done[j]! = 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.prim (Cost := Int) head target cost dist done n inf
    ⦃⇓ r c => ⌜0 ≤ r.1 ∧ Proofs.PrimBridge.IsMSF n Cm.toNat ((EdL head target cost n).map Proofs.PrimBridge.toArc)
        r.1.toNat ∧ c ≤ t0 + 1 + n * (1 + 2 * n) + degSum n (natA head) [] + n⌝⦄ := by
  obtain ⟨r, c, hrun, s, O, htot, hc⟩ := run_of_triple
    (prim_spec head target cost dist done n inf hhead htarget hE hinf0 hd hdn t0)
  apply triple_of_run r c hrun
  obtain ⟨D, cs, I, hlen, -, -, hc0⟩ := O
  have hpk := pk_bounds I Cm hCm (fun e he => ⟨(hE e he).2.2.1, hEC e he⟩)
  have hEd : ∀ e ∈ EdL head target cost n, e.1 < n ∧ e.2.1 < n ∧ 0 ≤ e.2.2 ∧ e.2.2 ≤ Cm :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1, hEC e he⟩
  obtain ⟨hmsf, hcast⟩ := Proofs.PrimBridge.prim_msf I hlen hCm hEd hsym (fun x hx => (hpk x hx).1)
  have hsum : r.1 = cs.sum := by
    rw [htot, ← Proofs.PrimExec.pS_eq I hlen]
    unfold Proofs.PrimExec.pS
    congr 1; apply List.map_congr_left; intro v _; exact (dd_getD _ v).symm
  have h0 : 0 ≤ r.1 := by rw [hsum, ← hcast]; omega
  refine ⟨h0, ?_, by omega⟩
  have : r.1.toNat = (cs.map Int.toNat).sum := by rw [hsum, ← hcast]; simp
  rw [this]; exact hmsf

end Proofs.Cpp.Prim
