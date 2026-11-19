import Proofs.Cpp.Gen.Dijkstra
import Proofs.Cpp.Lib.Basic
import Proofs.Math.DijkstraPMath
import Proofs.Math.TreeRootMath

/-! # `dijkstra` (library/graph/dijkstra.hpp)

Dijkstra's algorithm with a linear minimum scan on CSR arrays. The translated loops keep the arrays equal to the pure
model of `Proofs.DijkstraMath` / `Proofs.DijkstraPMath` (`djIter`, `pIter`; the scan `scanStep`, the relaxation
`relaxP`), whose theorems give the result. The relaxation looks at the edges of the finalised vertices, at most all `m`
edges (`W_eq`). The theorems are stated for `Cost = long long` (`Int`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen
open Proofs.BellmanFordMath Proofs.DijkstraMath Proofs.DijkstraPMath

namespace Proofs.Cpp.Dijkstra

def natL (a : Array Int) : List Nat := a.toList.map Int.toNat

/-- The edges leaving `b` in the CSR arrays, as model edges `(b, target, cost)`. -/
def outE (head target cost : Array Int) (b : Nat) : List Edge :=
  (List.range' ((natL head).getD b 0) ((natL head).getD (b + 1) 0 - (natL head).getD b 0)).map
    (fun p => (b, (natL target).getD p 0, cost.toList.getD p 0))

/-- The arrays hold the model state: distances `f`, finalised vertices `D`, parents `p` on `[0, n)`. -/
def RelDP (n : Nat) (f p : Nat → Int) (dist par : Array Int) : Prop :=
  dist.size = n ∧ par.size = n ∧ (∀ j : Nat, j < n → dist[j]! = f j) ∧ (∀ j : Nat, j < n → par[j]! = p j)

def Rel (n : Nat) (f : Nat → Int) (D : List Nat) (p : Nat → Int) (dist done par : Array Int) : Prop :=
  RelDP n f p dist par ∧ done.size = n ∧ (∀ j : Nat, j < n → (done[j]! = 0 ↔ j ∉ D))

section
variable (head target cost : Array Int) (n : Nat) (inf : Int) (dist par : Array Int)

abbrev d0 : Nat → Int := fun j => if j < n then dist.toList.getD j 0 else inf
abbrev p0 : Nat → Int := fun j => par.toList.getD j 0
abbrev DJ (t : Nat) : (Nat → Int) × List Nat := djIter inf (outE head target cost) n (d0 n inf dist) t
abbrev PI (t : Nat) : Nat → Int := pIter inf (outE head target cost) n (d0 n inf dist) (p0 par) t
/-- The scan state after the vertices `< k` in step `t`. -/
abbrev SC (t k : Nat) : Option Nat × Int :=
  (List.range k).foldl (scanStep inf (DJ head target cost n inf dist t).1 (DJ head target cost n inf dist t).2) (none, inf)
/-- The vertex picked in step `t`. -/
abbrev PK (t : Nat) : Option Nat := (scanRes inf n (DJ head target cost n inf dist t).1 (DJ head target cost n inf dist t).2).1
/-- The distances and parents after the first `j` edges of the picked vertex `b` in step `t`. -/
abbrev IN (t b j : Nat) : (Nat → Int) × (Nat → Int) :=
  ((outE head target cost b).take j).foldl (relaxP inf) ((DJ head target cost n inf dist t).1, PI head target cost n inf dist par t)

def W : Nat → Nat
  | 0 => 0
  | t + 1 => W t + match PK head target cost n inf dist (t) with
    | none => 0
    | some b => (outE head target cost b).length

end

/-- The edge costs are nonnegative. -/
def CostNN (cost : Array Int) : Prop := ∀ q : Nat, 0 ≤ cost.toList.getD q 0

/-- The heads of the edges are vertices. -/
def HeadsLt (target : Array Int) (n : Nat) : Prop := ∀ q : Nat, (natL target).getD q 0 < n

/-- The scan state as the pair `(best, bd)`. -/
def SRel (s : Option Nat × Int) (best bd : Int) : Prop :=
  bd = s.2 ∧ best = (match s.1 with | none => -1 | some b => (b : Int))

theorem natL_getD (a : Array Int) (k : Nat) : (natL a).getD k 0 = (a[k]!).toNat := by
  unfold natL
  by_cases h : k < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a k h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a k h]

theorem get_toList (a : Array Int) (i : Int) : get a i = a.toList.getD i.toNat 0 := by
  rw [get_eq]
  by_cases h : i.toNat < a.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos a i.toNat h]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg a i.toNat h]

theorem nat_val (a : Array Int) (ha : ∀ k : Nat, 0 ≤ a[k]!) (k : Nat) :
    get a (k : Int) = (((natL a).getD k 0 : Nat) : Int) := by
  rw [get_eq, natL_getD]; simp; have := ha k; omega

theorem cur_eq {N : Int} {pref suff : List Int} {c : Int} (h : range 0 N = pref ++ c :: suff) :
    c = (pref.length : Int) ∧ (pref.length : Int) < N := by
  have e := range_cursor h
  have l := range_prefix_length h
  simp at e l; exact ⟨e, l⟩

section
variable {head target cost dist par : Array Int} {n : Nat} {inf : Int}

theorem SC_succ (t k : Nat) : SC head target cost n inf dist t (k + 1) =
    scanStep inf (DJ head target cost n inf dist t).1 (DJ head target cost n inf dist t).2
      (SC head target cost n inf dist t k) k := by
  simp only [SC, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- One step of the minimum scan. -/
theorem scan_vc (t k : Nat) (hk : k < n) (dd dn pp : Array Int)
    (R : Rel n (DJ head target cost n inf dist t).1 (DJ head target cost n inf dist t).2
      (PI head target cost n inf dist par t) dd dn pp) (best bd : Int)
    (S : SRel (SC head target cost n inf dist t k) best bd) :
    (get dn k = 0 → get dd k < bd → SRel (SC head target cost n inf dist t (k + 1)) k (get dd k)) ∧
    (get dn k = 0 → ¬get dd k < bd → SRel (SC head target cost n inf dist t (k + 1)) best bd) ∧
    (¬get dn k = 0 → SRel (SC head target cost n inf dist t (k + 1)) best bd) := by
  obtain ⟨⟨-, -, hd, -⟩, -, hdn⟩ := R
  obtain ⟨hbd, hb⟩ := S
  have gd : get dd (k : Int) = (DJ head target cost n inf dist t).1 k := by rw [get_eq, Int.toNat_natCast, hd k hk]
  have gn : get dn (k : Int) = 0 ↔ k ∉ (DJ head target cost n inf dist t).2 := by
    rw [get_eq, Int.toNat_natCast]; exact hdn k hk
  rw [SC_succ, gd]
  unfold scanStep
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · rw [if_pos ⟨gn.mp h1, by rw [← hbd]; exact h2⟩]; exact ⟨rfl, rfl⟩
  · rw [if_neg (fun h => h2 (by rw [hbd]; exact h.2))]; exact ⟨hbd, hb⟩
  · rw [if_neg (fun h => h1 (gn.mpr h.1))]; exact ⟨hbd, hb⟩

end

section
variable {head target cost dist par : Array Int} {n : Nat} {inf : Int}

theorem outE_len (b : Nat) : (outE head target cost b).length = (natL head).getD (b + 1) 0 - (natL head).getD b 0 := by
  simp [outE]

theorem outE_get (b j : Nat) (hj : j < (outE head target cost b).length) :
    (outE head target cost b)[j] = (b, (natL target).getD ((natL head).getD b 0 + j) 0,
      cost.toList.getD ((natL head).getD b 0 + j) 0) := by
  simp [outE]

theorem outE_mem (hC : ∀ q : Nat, 0 ≤ cost.toList.getD q 0) (b : Nat) :
    ∀ e ∈ outE head target cost b, e.1 = b ∧ 0 ≤ e.2.2 := by
  intro e he
  simp only [outE, List.mem_map] at he
  obtain ⟨q, -, rfl⟩ := he
  exact ⟨rfl, hC q⟩

/-- The scan found the vertex `b` of the model. -/
theorem picked (best bd : Int) (t : Nat)
    (S : SRel (SC head target cost n inf dist t n) best bd) (h0 : 0 ≤ best) :
    ∃ b, PK head target cost n inf dist t = some b ∧ best = (b : Int) ∧ b < n ∧
      b ∉ (DJ head target cost n inf dist t).2 ∧ bd = (DJ head target cost n inf dist t).1 b ∧ bd < inf := by
  obtain ⟨hbd, hb⟩ := S
  have P := scan_inv inf (DJ head target cost n inf dist t).1 (DJ head target cost n inf dist t).2 n
  change PickInv _ _ _ n (SC head target cost n inf dist t n) at P
  cases hs : (SC head target cost n inf dist t n).1 with
  | none => rw [hs] at hb; simp at hb; omega
  | some b =>
    rw [hs] at hb
    obtain ⟨h1, h2, h3, h4, -⟩ := P.some b hs
    exact ⟨b, hs, hb, h1, h2, by rw [hbd, h3], by rw [hbd]; exact h4⟩

/-- One edge of the picked vertex: the arrays follow `relaxP`. -/
theorem relax_vc (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (hT : ∀ q : Nat, (natL target).getD q 0 < n) (hC : ∀ q : Nat, 0 ≤ cost.toList.getD q 0)
    (t b j : Nat) (bd : Int) (hbd : bd = (DJ head target cost n inf dist t).1 b) (hinf : bd < inf)
    (hj : j < (outE head target cost b).length) (d p : Array Int)
    (R : RelDP n (IN head target cost n inf dist par t b j).1 (IN head target cost n inf dist par t b j).2 d p) :
    (bd + get cost (get head (b : Int) + j) < get d (get target (get head (b : Int) + j)) →
      RelDP n (IN head target cost n inf dist par t b (j + 1)).1 (IN head target cost n inf dist par t b (j + 1)).2
        (set d (get target (get head (b : Int) + j)) (bd + get cost (get head (b : Int) + j)))
        (set p (get target (get head (b : Int) + j)) b)) ∧
    (¬bd + get cost (get head (b : Int) + j) < get d (get target (get head (b : Int) + j)) →
      RelDP n (IN head target cost n inf dist par t b (j + 1)).1 (IN head target cost n inf dist par t b (j + 1)).2
        d p) := by
  obtain ⟨hs, hps, hd, hp⟩ := R
  set q := (natL head).getD b 0 + j
  set w := (natL target).getD q 0
  have hq : get head (b : Int) + (j : Int) = (q : Int) := by rw [nat_val head hhead]; simp [q]
  have hw : get target (q : Int) = (w : Int) := nat_val target htarget q
  have hc : get cost (q : Int) = cost.toList.getD q 0 := by rw [get_toList]; simp
  have hwn : w < n := hT q
  set st := IN head target cost n inf dist par t b j
  have hst1 : IN head target cost n inf dist par t b (j + 1) = relaxP inf st (b, w, cost.toList.getD q 0) := by
    show ((outE head target cost b).take (j + 1)).foldl _ _ = _
    rw [List.take_succ, List.getElem?_eq_getElem hj, outE_get b j hj]; simp [st, IN, q, w]
  have hb : st.1 b = bd := by
    simp only [st, IN]
    rw [foldP_fst, hbd]
    exact (relax_fold_cases inf b _ _ (fun e he => outE_mem hC b e (List.mem_of_mem_take he))).1
  have gdw : get d (w : Int) = st.1 w := by rw [get_eq, Int.toNat_natCast, hd w hwn]
  rw [hq, hw, hc, gdw, hst1]
  unfold relaxP
  refine ⟨fun hlt => ?_, fun hlt => ?_⟩
  · rw [if_pos ⟨by rw [hb]; omega, by rw [hb]; exact hlt⟩]
    refine ⟨by simp [hs], by simp [hps], fun k hk => ?_, fun k hk => ?_⟩
    · rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp only [Int.toNat_natCast, upd, hb]
      split <;> simp_all
    · rw [getElemBang_set _ _ _ _ (by simp; omega)]; simp only [Int.toNat_natCast, updI]
      split <;> simp_all
  · rw [if_neg (fun h => hlt (by rw [← hb]; exact h.2))]
    exact ⟨hs, hps, hd, hp⟩

end

theorem deg_of (head : Array Int) (hhead : ∀ k : Nat, 0 ≤ head[k]!) (target cost : Array Int) (b j : Nat)
    (h : (j : Int) < get head ((b : Int) + 1) - get head (b : Int)) : j < (outE head target cost b).length := by
  rw [outE_len]
  rw [show (b : Int) + 1 = ((b + 1 : Nat) : Int) by simp, nat_val head hhead, nat_val head hhead] at h
  omega

section
variable {head target cost dist par : Array Int} {n : Nat} {inf : Int}

theorem none_of (t : Nat) (best bd : Int) (S : SRel (SC head target cost n inf dist t n) best bd) (h : best < 0) :
    PK head target cost n inf dist t = none := by
  obtain ⟨-, hb⟩ := S
  show (SC head target cost n inf dist t n).1 = none
  cases hs : (SC head target cost n inf dist t n).1 with
  | none => rfl
  | some b => rw [hs] at hb; simp at hb; omega

theorem step_none (t : Nat) (hpk : PK head target cost n inf dist t = none) :
    DJ head target cost n inf dist (t + 1) = DJ head target cost n inf dist t ∧
    PI head target cost n inf dist par (t + 1) = PI head target cost n inf dist par t ∧
    W head target cost n inf dist (t + 1) = W head target cost n inf dist t := by
  refine ⟨?_, ?_, ?_⟩
  · show djIter _ _ _ _ (t + 1) = _
    rw [djIter_succ]; unfold djStep; rw [show (scanRes _ _ _ _).1 = none from hpk]
  · show pIter _ _ _ _ _ (t + 1) = _
    rw [pIter_succ]; unfold pStep; rw [show (scanRes _ _ _ _).1 = none from hpk]
  · simp only [W]; rw [hpk]; rfl

theorem range_deg (hhead : ∀ k : Nat, 0 ≤ head[k]!) (b : Nat) :
    (range 0 (get head ((b : Int) + 1) - get head (b : Int))).length = (outE head target cost b).length := by
  rw [range_length, outE_len, show (b : Int) + 1 = ((b + 1 : Nat) : Int) by simp, nat_val head hhead, nat_val head hhead]
  omega

theorem step_some (t b : Nat) (hpk : PK head target cost n inf dist t = some b) (hbn : b < n)
    (dn : Array Int) (hdn : dn.size = n ∧ ∀ j : Nat, j < n → (dn[j]! = 0 ↔ j ∉ (DJ head target cost n inf dist t).2))
    (d p : Array Int)
    (RI : RelDP n (IN head target cost n inf dist par t b (outE head target cost b).length).1
      (IN head target cost n inf dist par t b (outE head target cost b).length).2 d p) :
    Rel n (DJ head target cost n inf dist (t + 1)).1 (DJ head target cost n inf dist (t + 1)).2
      (PI head target cost n inf dist par (t + 1)) d (set dn b 1) p ∧
    W head target cost n inf dist (t + 1) = W head target cost n inf dist t + (outE head target cost b).length := by
  have hIN : IN head target cost n inf dist par t b (outE head target cost b).length =
      relaxOutP inf (outE head target cost) b ((DJ head target cost n inf dist t).1, PI head target cost n inf dist par t) := by
    simp [IN, relaxOutP]
  have hDJ : DJ head target cost n inf dist (t + 1) =
      (relaxOut inf (outE head target cost) b (DJ head target cost n inf dist t).1, (DJ head target cost n inf dist t).2 ++ [b]) := by
    show djIter _ _ _ _ (t + 1) = _
    rw [djIter_succ]; unfold djStep; rw [show (scanRes _ _ _ _).1 = some b from hpk]
  have hPI : PI head target cost n inf dist par (t + 1) =
      (relaxOutP inf (outE head target cost) b ((DJ head target cost n inf dist t).1, PI head target cost n inf dist par t)).2 := by
    show pIter _ _ _ _ _ (t + 1) = _
    rw [pIter_succ]; unfold pStep; rw [show (scanRes _ _ _ _).1 = some b from hpk]
  rw [hIN] at RI
  refine ⟨⟨?_, by simp [hdn.1], fun j hj => ?_⟩, by simp only [W]; rw [hpk]⟩
  · rw [hDJ, hPI]; dsimp only
    rw [← relaxOutP_fst inf (outE head target cost) b ((DJ head target cost n inf dist t).1, PI head target cost n inf dist par t)]
    exact RI
  · rw [getElemBang_set _ _ _ _ (by simp; omega), hDJ]
    simp only [Int.toNat_natCast, List.mem_append, List.mem_singleton]
    by_cases hjb : j = b
    · subst hjb; simp
    · simp only [hjb, ite_false, or_false]; exact hdn.2 j hj

end

theorem dijkstra_spec (head target cost dist done par : Array Int) (n : Nat) (inf : Int)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (hT : HeadsLt target n) (hC : CostNN cost) (hs : dist.size = n ∧ par.size = n ∧ done.size = n)
    (hdone : ∀ j : Nat, j < n → done[j]! = 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.dijkstra (Cost := Int) head target cost dist done par n inf
    ⦃⇓ r c => ⌜Rel n (DJ head target cost n inf dist n).1 (DJ head target cost n inf dist n).2
        (PI head target cost n inf dist par n) r.1 r.2.1 r.2.2 ∧
      c = t0 + 1 + n * (1 + n) + W head target cost n inf dist n⌝⦄ := by
  mvcgen [cp.dijkstra]
  case inv1 =>
    exact ⇓⟨xs, d, dn, p⟩ c => ⌜Rel n (DJ head target cost n inf dist xs.prefix.length).1
      (DJ head target cost n inf dist xs.prefix.length).2 (PI head target cost n inf dist par xs.prefix.length) d dn p ∧
      c = t0 + 1 + xs.prefix.length * (1 + n) + W head target cost n inf dist xs.prefix.length⌝
  case inv2 =>
    rename_i pt _ _ _ _ _ _ _ _ _ _ _
    exact ⇓⟨xs, b, bd⟩ c => ⌜SRel (SC head target cost n inf dist pt.length xs.prefix.length) b bd ∧
      c = t0 + 1 + pt.length * (1 + n) + W head target cost n inf dist pt.length + 1 + xs.prefix.length⌝
  case inv3 =>
    rename_i pt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⇓⟨xs, d, p⟩ c => ⌜(∀ b, PK head target cost n inf dist pt.length = some b →
      RelDP n (IN head target cost n inf dist par pt.length b xs.prefix.length).1
        (IN head target cost n inf dist par pt.length b xs.prefix.length).2 d p) ∧
      c = t0 + 1 + pt.length * (1 + n) + W head target cost n inf dist pt.length + 1 + n + xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  -- the scan
  all_goals (try (obtain ⟨R, hc0⟩ := ‹Rel n _ _ _ _ _ _ ∧ _›
                  obtain ⟨S, hc⟩ := ‹SRel (SC _ _ _ _ _ _ _ _) _ _ ∧ _›
                  obtain ⟨rfl, hk⟩ := cur_eq ‹range 0 (n : Int) = _ ++ _ :: _›
                  have D := scan_vc _ _ (by omega) _ _ _ R _ _ S
                  first
                  | exact ⟨D.1 ‹_› ‹_›, by omega⟩
                  | exact ⟨D.2.1 ‹_› (Int.not_lt.mpr ‹_›), by omega⟩
                  | exact ⟨D.2.2 ‹_›, by omega⟩))
  -- the relaxation of the edges of the picked vertex
  all_goals (try (obtain ⟨RI, hc⟩ := ‹(∀ b, PK _ _ _ _ _ _ _ = some b → _) ∧ _›
                  obtain ⟨S, hc1⟩ := ‹SRel (SC _ _ _ _ _ _ _ _) _ _ ∧ _›
                  obtain ⟨b, hpk, hbest, hbn, -, hbd, hinf⟩ := picked _ _ _ S ‹(0 : Int) ≤ _›
                  obtain ⟨rfl, hk⟩ := cur_eq ‹range 0 (get head (_ + 1) - get head _) = _ ++ _ :: _›
                  simp +zetaDelta only at hk
                  rw [hbest] at hk
                  try rw [hbest]
                  have hj := deg_of head hhead target cost b _ hk
                  have D := relax_vc hhead htarget hT hC _ b _ _ hbd hinf hj _ _ (RI b hpk)
                  refine ⟨fun b' hb' => ?_, by omega⟩
                  rw [hpk] at hb'; cases hb'
                  first
                  | (have hlt := ‹_ + get cost _ < _›; rw [hbest] at hlt; exact D.1 hlt)
                  | (have hlt := ‹_ ≤ _ + get cost _›; rw [hbest] at hlt; exact D.2 (Int.not_lt.mpr hlt))))
  · exact ⟨⟨rfl, rfl⟩, (‹Rel n _ _ _ _ _ _ ∧ _›).2⟩
  · obtain ⟨R, hc0⟩ := ‹Rel n _ _ _ _ _ _ ∧ _›
    obtain ⟨S, hc⟩ := ‹SRel (SC _ _ _ _ _ _ _ _) _ _ ∧ _›
    exact ⟨fun b _ => R.1, hc⟩
  · obtain ⟨R, hc0⟩ := ‹Rel n _ _ _ _ _ _ ∧ _›
    obtain ⟨S, hc1⟩ := ‹SRel (SC _ _ _ _ _ _ _ _) _ _ ∧ _›
    obtain ⟨b, hpk, hbest, hbn, -, -, -⟩ := picked _ _ _ S ‹(0 : Int) ≤ _›
    obtain ⟨RI, hc⟩ := ‹(∀ b, PK _ _ _ _ _ _ _ = some b → _) ∧ _›
    have RI' := RI b hpk
    rw [hbest, range_deg (target := target) (cost := cost) hhead] at RI'
    rw [hbest, range_deg (target := target) (cost := cost) hhead] at hc
    rw [hbest]
    have D := step_some _ b hpk hbn _ R.2 _ _ RI'
    exact ⟨D.1, by rw [D.2, Nat.add_mul, Nat.one_mul]; omega⟩
  · obtain ⟨R, hc0⟩ := ‹Rel n _ _ _ _ _ _ ∧ _›
    obtain ⟨S, hc⟩ := ‹SRel (SC _ _ _ _ _ _ _ _) _ _ ∧ _›
    obtain ⟨e1, e2, e3⟩ := step_none (par := par) _ (none_of _ _ _ S ‹_›)
    rw [e1, e2, e3]
    exact ⟨R, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  · refine ⟨⟨⟨hs.1, hs.2.1, fun j hj => ?_, fun j hj => ?_⟩, hs.2.2, fun j hj => ?_⟩, by simp [W]; omega⟩
    · show dist[j]! = if j < n then dist.toList.getD j 0 else inf
      rw [if_pos hj]
      simp [List.getD_eq_getElem?_getD, hj, hs.1, getElem!_pos dist j (by omega)]
    · show par[j]! = par.toList.getD j 0
      simp [List.getD_eq_getElem?_getD, hj, hs.2.1, getElem!_pos par j (by omega)]
    · simp [DJ, djIter, hdone j hj]
  · obtain ⟨R, hc⟩ := ‹Rel n _ _ _ _ _ _ ∧ _›
    exact ⟨R, hc⟩

theorem W_eq (head target cost dist : Array Int) (n : Nat) (inf : Int) (t : Nat) :
    W head target cost n inf dist t =
      ((DJ head target cost n inf dist t).2.map (fun v => (outE head target cost v).length)).sum := by
  induction t with
  | zero => simp [W, DJ, djIter]
  | succ t ih =>
    cases hpk : PK head target cost n inf dist t with
    | none =>
      obtain ⟨e1, -, e3⟩ := step_none (par := dist) t hpk
      rw [e3, e1, ih]
    | some b =>
      have hDJ : DJ head target cost n inf dist (t + 1) = (relaxOut inf (outE head target cost) b
          (DJ head target cost n inf dist t).1, (DJ head target cost n inf dist t).2 ++ [b]) := by
        show djIter _ _ _ _ (t + 1) = _
        rw [djIter_succ]; unfold djStep; rw [show (scanRes _ _ _ _).1 = some b from hpk]
      simp only [W]; rw [hpk, ih, hDJ]; simp

/-- `dijkstra(head, target, cost, dist, done, parent, n, inf)` on CSR arrays with nonnegative costs (`Cost = long long`):
the output distances are those of the model `djIter`, which are sound and, when `inf` exceeds every walk from a
source, the shortest distances (`Proofs.DijkstraMath.dijkstra_spec`); every changed parent is the start of an edge
that gives the distance (`Proofs.DijkstraPMath.pIter_inv`); at most `1 + n (1 + n) + m` steps for `m = head[n]`. -/
theorem dijkstra_correct (head target cost dist done par : Array Int) (n : Nat) (inf : Int)
    (hhead : ∀ k : Nat, 0 ≤ head[k]!) (htarget : ∀ k : Nat, 0 ≤ target[k]!)
    (hmono : ∀ i, i < n → (natL head).getD i 0 ≤ (natL head).getD (i + 1) 0)
    (hT : HeadsLt target n) (hC : CostNN cost) (hs : dist.size = n ∧ par.size = n ∧ done.size = n)
    (hdone : ∀ j : Nat, j < n → done[j]! = 0) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.dijkstra (Cost := Int) head target cost dist done par n inf
    ⦃⇓ r c => ⌜(∀ j : Nat, j < n → r.1[j]! = (DJ head target cost n inf dist n).1 j) ∧
        Sound inf (Eall n (outE head target cost)) (d0 n inf dist) (DJ head target cost n inf dist n).1 ∧
        ((∀ w y c k, d0 n inf dist w < inf → Walk (Eall n (outE head target cost)) w y c k → d0 n inf dist w + c < inf) →
          ∀ w y c k, d0 n inf dist w < inf → Walk (Eall n (outE head target cost)) w y c k →
            (DJ head target cost n inf dist n).1 y ≤ d0 n inf dist w + c) ∧
        (∀ j : Nat, j < n → r.2.2[j]! = PI head target cost n inf dist par n j) ∧
        ParInv (outE head target cost) (DJ head target cost n inf dist n).2 (DJ head target cost n inf dist n).1
          (PI head target cost n inf dist par n) (p0 par) ∧
        c ≤ t0 + 1 + n * (1 + n) + (natL head).getD n 0⌝⦄ := by
  obtain ⟨r, c, hrun, R, hc⟩ := run_of_triple
    (dijkstra_spec head target cost dist done par n inf hhead htarget hT hC hs hdone t0)
  apply triple_of_run r c hrun
  have G : Graph n (outE head target cost) := ⟨fun u _ e he => by
    simp only [outE, List.mem_map] at he
    obtain ⟨q, -, rfl⟩ := he
    exact ⟨rfl, hT q, hC q⟩⟩
  have hd0 : ∀ w, d0 n inf dist w < inf → w < n := by
    intro w hw; by_contra h; simp [d0, h] at hw
  obtain ⟨hS, hCm⟩ := Proofs.DijkstraMath.dijkstra_spec n inf (outE head target cost) G (d0 n inf dist) hd0
  have hP := pIter_inv n inf (outE head target cost) G (d0 n inf dist) hd0 (p0 par) n
  have hI := (djIter_inv n inf (outE head target cost) G (d0 n inf dist) hd0 n).1
  have hW : W head target cost n inf dist n ≤ (natL head).getD n 0 := by
    rw [W_eq]
    have hle := Proofs.TreeRootMath.sum_nodup_le (fun v => (outE head target cost v).length) n
      (DJ head target cost n inf dist n).2 hI.nodup hI.lt
    have e : ((List.range n).map (fun v => (outE head target cost v).length)) =
        (List.range n).map (fun v => (natL head).getD (v + 1) 0 - (natL head).getD v 0) := by
      apply List.map_congr_left; intro v _; exact outE_len v
    rw [e] at hle
    have htel := Proofs.TreeRootMath.sum_outdeg (natL head) n hmono
    omega
  exact ⟨R.1.2.2.1, hS, hCm, R.1.2.2.2, hP, by omega⟩

end Proofs.Cpp.Dijkstra
