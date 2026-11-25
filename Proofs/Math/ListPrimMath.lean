import Proofs.Cpp.Lib.Basic
import Proofs.Math.PrimStep
import Proofs.Math.PrimBridge

/-! # Prim's algorithm with a lazy priority queue (the math of `ListGraph::prim`)

The relaxation of the edges of the picked vertex on arrays (`astep`, the loop body of `prim_span`) and its
correspondence with the list relaxation `relaxL` of `Proofs.PrimRelax` (with `Dn = doneOf n D`). -/

namespace Proofs.ListPrimMath

open Proofs.Cpp
open Proofs.BellmanFordMath (Edge)
open Proofs.PrimRelax (relaxL relaxL_getD)

/-- One relaxation of the loop body: `if (!used[to] && c < dist[to]) { dist[to] = c; pq.emplace(dist[to], to); }`. -/
def astep (used : Array Bool) (st : Array Int × List (Int × Int)) (p : Int × Int) : Array Int × List (Int × Int) :=
  if (!(Cpp.get used p.1) && decide (p.2 < Cpp.get st.1 p.1)) then
    (Cpp.set st.1 p.1 p.2, st.2 ++ [(Cpp.get (Cpp.set st.1 p.1 p.2) p.1, p.1)])
  else st

theorem toList_set (d : Array Int) (i : Nat) (a : Int) (h : i < d.size) :
    (Cpp.set d (i : Int) a).toList = d.toList.set i a := by
  simp [Cpp.set, Array.set!_eq_setIfInBounds, Array.setIfInBounds, h]

theorem getD_toList (d : Array Int) (x : Nat) : d.toList.getD x 0 = d[x]! := by
  by_cases h : x < d.size
  · simp [List.getD_eq_getElem?_getD, h, getElem!_pos]
  · simp [List.getD_eq_getElem?_getD, h, getElem!_neg]

/-- The array step is the list relaxation of the edge `(v, to, c)`. -/
theorem astep_list (used : Array Bool) (Dn : List Nat) (d : Array Int) (Q : List (Int × Int)) (v : Nat)
    (p : Int × Int) (h0 : 0 ≤ p.1) (hn : p.1.toNat < d.size)
    (hu : used[p.1.toNat]! = decide (Dn.getD p.1.toNat 0 ≠ 0)) :
    (astep used (d, Q) p).1.toList = relaxL Dn d.toList (v, p.1.toNat, p.2) := by
  obtain ⟨t, c⟩ := p
  simp only at h0 hn hu
  obtain ⟨t, rfl⟩ : ∃ t' : Nat, t = (t' : Int) := ⟨t.toNat, by omega⟩
  simp only [Int.toNat_natCast] at hn hu
  unfold astep relaxL
  simp only [get_natCast, Int.toNat_natCast, getD_toList, hu]
  by_cases h1 : Dn.getD t 0 = 0
  · have h1' : Dn[t]?.getD 0 = 0 := by simpa [List.getD_eq_getElem?_getD] using h1
    by_cases h2 : c < d[t]!
    · simp [h1', h2, toList_set d t c hn]
    · simp [h1', h2]
  · have h1' : ¬ Dn[t]?.getD 0 = 0 := by simpa [List.getD_eq_getElem?_getD] using h1
    simp [h1']

theorem astep_size (used : Array Bool) (st : Array Int × List (Int × Int)) (p : Int × Int) :
    (astep used st p).1.size = st.1.size := by
  unfold astep; split <;> simp

theorem fold_list (used : Array Bool) (Dn : List Nat) (v : Nat) (ps : List (Int × Int)) :
    ∀ (d : Array Int) (Q : List (Int × Int)), (∀ p ∈ ps, 0 ≤ p.1 ∧ p.1.toNat < d.size) →
      (∀ x < d.size, used[x]! = decide (Dn.getD x 0 ≠ 0)) →
      (ps.foldl (astep used) (d, Q)).1.toList =
        (ps.map (fun p => ((v, p.1.toNat, p.2) : Edge))).foldl (relaxL Dn) d.toList := by
  induction ps with
  | nil => intro d Q _ _; rfl
  | cons p ps ih =>
    intro d Q hr hu
    simp only [List.foldl_cons, List.map_cons]
    obtain ⟨h0, hn⟩ := hr p (by simp)
    have e := astep_list used Dn d Q v p h0 hn (hu _ hn)
    have hsz := astep_size used (d, Q) p
    have := ih (astep used (d, Q) p).1 (astep used (d, Q) p).2
      (fun p' hp' => by rw [hsz]; exact hr p' (by simp [hp'])) (fun x hx => hu x (by rw [hsz] at hx; exact hx))
    rw [e] at this
    exact this

/-- What the relaxations push and change. -/
theorem fold_props (used : Array Bool) (ps : List (Int × Int)) :
    ∀ (d : Array Int) (Q : List (Int × Int)), (∀ p ∈ ps, 0 ≤ p.1 ∧ p.1.toNat < d.size) →
      let r := ps.foldl (astep used) (d, Q)
      ∃ P, r.2 = Q ++ P ∧ P.length ≤ ps.length ∧
        (∀ q ∈ P, (∃ p ∈ ps, q = (p.2, p.1)) ∧ r.1[q.2.toNat]! ≤ q.1) ∧
        (∀ x : Nat, r.1[x]! ≤ d[x]!) ∧ (∀ x : Nat, r.1[x]! ≠ d[x]! → (r.1[x]!, (x : Int)) ∈ P) := by
  induction ps with
  | nil => intro d Q _; exact ⟨[], by simp, by simp, by simp, fun _ => le_rfl, fun _ h => absurd rfl h⟩
  | cons p ps ih =>
    intro d Q hr
    simp only [List.foldl_cons]
    obtain ⟨h0, hn⟩ := hr p (by simp)
    obtain ⟨t, c⟩ := p
    simp only at h0 hn
    obtain ⟨t, rfl⟩ : ∃ t' : Nat, t = (t' : Int) := ⟨t.toNat, by omega⟩
    simp only [Int.toNat_natCast] at hn
    have hset : ∀ x, (Cpp.set d (t : Int) c)[x]! = if x = t then c else d[x]! := by
      intro x; rw [getElemBang_set _ _ _ _ (by simpa using hn)]; simp
    by_cases hf : (!(Cpp.get used (t : Int)) && decide (c < Cpp.get d (t : Int))) = true
    · have hst : astep used (d, Q) ((t : Int), c) = (Cpp.set d (t : Int) c, Q ++ [(c, (t : Int))]) := by
        unfold astep; rw [if_pos hf]; simp [hset]
      have hlt : c < d[t]! := by simp at hf; exact of_decide_eq_true hf.2
      rw [hst]
      have hsz : (Cpp.set d (t : Int) c).size = d.size := by simp
      obtain ⟨P, hP, hlen, hq, hle, hch⟩ := ih _ (Q ++ [(c, (t : Int))])
        (fun p' hp' => by rw [hsz]; exact hr p' (by simp [hp']))
      refine ⟨(c, (t : Int)) :: P, by rw [hP]; simp, by simp; omega, ?_, ?_, ?_⟩
      · intro q hq'
        simp at hq'
        rcases hq' with rfl | hq'
        · refine ⟨⟨(t, c), by simp, rfl⟩, ?_⟩
          have := hle t; rw [hset] at this; simpa using this
        · obtain ⟨⟨p', hp', e⟩, h2⟩ := hq q hq'
          exact ⟨⟨p', by simp [hp'], e⟩, h2⟩
      · intro x; have := hle x; rw [hset] at this; split at this
        · rename_i e; subst e; omega
        · exact this
      · intro x hx
        by_cases e : (List.foldl (astep used) (Cpp.set d (t : Int) c, Q ++ [(c, (t : Int))]) ps).1[x]! =
            (Cpp.set d (t : Int) c)[x]!
        · rw [hset] at e
          by_cases ex : x = t
          · subst ex; simp at e; rw [e]; simp
          · rw [if_neg ex] at e; exact absurd e hx
        · exact List.mem_cons_of_mem _ (hch x e)
    · have hst : astep used (d, Q) ((t : Int), c) = (d, Q) := by
        unfold astep; rw [if_neg hf]
      rw [hst]
      obtain ⟨P, hP, hlen, hq, hle, hch⟩ := ih d Q (fun p' hp' => hr p' (by simp [hp']))
      refine ⟨P, hP, by simp; omega, fun q hq' => ?_, hle, hch⟩
      obtain ⟨⟨p', hp', e⟩, h2⟩ := hq q hq'
      exact ⟨⟨p', by simp [hp'], e⟩, h2⟩

/-! ## The invariant of `prim_span` -/

open Proofs.PrimStep (PInv PInv_step)
open Proofs.DijkstraOldExec (doneOf doneOf_getD)

/-- The arcs `(v, to, c)` of all rows, from the pairs `(to, c)` of each row. -/
def EdOf (n : Nat) (out : Nat → List (Int × Int)) : List Edge :=
  (List.range n).flatMap (fun v => (out v).map (fun p => ((v, p.1.toNat, p.2) : Edge)))

def ValidP (n : Nat) (U : Int) (out : Nat → List (Int × Int)) : Prop :=
  ∀ v < n, ∀ p ∈ out v, 0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < U

/-- `used` marks exactly the picked vertices `D`. -/
def SR (n : Nat) (D : List Nat) (dist : Array Int) (used : Array Bool) : Prop :=
  dist.size = n ∧ used.size = n ∧ ∀ x < n, used[x]! = decide (x ∈ D)

/-- The queue: its pairs are valid keys of their vertices, and every unpicked vertex with a finite distance has
its current pair in it. -/
def QI (n : Nat) (U : Int) (D : List Nat) (dist : Array Int) (Q : List (Int × Int)) : Prop :=
  (∀ q ∈ Q, 0 ≤ q.2 ∧ q.2 < n ∧ dist[q.2.toNat]! ≤ q.1 ∧ 0 ≤ q.1 ∧ q.1 < U) ∧
  (∀ x < n, x ∉ D → dist[x]! < U → (dist[x]!, (x : Int)) ∈ Q)

theorem perm_mem' {α : Type} {Q Q' : List α} {a b : α} (h : Q.Perm (a :: Q')) (hb : b ∈ Q') : b ∈ Q :=
  h.mem_iff.mpr (by simp [hb])

theorem perm_mem_ne' {α : Type} {Q Q' : List α} {a b : α} (h : Q.Perm (a :: Q')) (hb : b ∈ Q) (hne : b ≠ a) :
    b ∈ Q' := by
  have := h.mem_iff.mp hb; simp at this
  rcases this with e | e
  · exact absurd e hne
  · exact e

/-- A pair that is stale or of a picked vertex is dropped. -/
theorem qi_stale {n : Nat} {U : Int} {D : List Nat} {dist : Array Int} {used : Array Bool}
    {Q Q' : List (Int × Int)} {x : Int × Int} (hS : SR n D dist used) (hQI : QI n U D dist Q)
    (hQ : Q.Perm (x :: Q')) (hc : (Cpp.get used x.2 || decide (Cpp.get dist x.2 < x.1)) = true) :
    QI n U D dist Q' := by
  refine ⟨fun q hq => hQI.1 q (perm_mem' hQ hq), fun y hy hyD hlt => ?_⟩
  refine perm_mem_ne' hQ (hQI.2 y hy hyD hlt) ?_
  intro e
  have hx := hQI.1 x (hQ.mem_iff.mpr List.mem_cons_self)
  rw [← e] at hc
  simp only [get_eq, Int.toNat_natCast] at hc
  rw [hS.2.2 y hy] at hc
  simp [hyD] at hc

theorem mem_EdOf {n : Nat} {out : Nat → List (Int × Int)} {e : Edge} :
    e ∈ EdOf n out ↔ e.1 < n ∧ ∃ p ∈ out e.1, e = (e.1, p.1.toNat, p.2) := by
  unfold EdOf
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨v, hv, p, hp, rfl⟩; exact ⟨hv, p, hp, rfl⟩
  · rintro ⟨hv, p, hp, he⟩; exact ⟨e.1, hv, p, hp, he.symm⟩

/-- Picking `v` at the key `k` and relaxing its edges keeps the invariant. `Dd` is the distance list of the
invariant before the pick; the array is `Dd` with `v` set to `k`. -/
theorem fresh_step {n : Nat} {U : Int} {out : Nat → List (Int × Int)} (hV : ValidP n U out) (hU : 0 ≤ U)
    {D : List Nat} {cs : List Int} {Dd : List Int} {dist : Array Int} {used : Array Bool} {Q' : List (Int × Int)}
    {v : Nat} {k : Int} (hS : SR n D dist used) (hI : PInv n U (EdOf n out) Dd (doneOf n D) D cs)
    (hdist : dist.toList = Dd.set v k) (hvn : v < n) (hvD : v ∉ D) (hk0 : 0 ≤ k) (hkU : k ≤ U)
    (hcase : (k < U ∧ Dd.getD v 0 = k ∧ ∀ x, x < n → x ∉ D → k ≤ Dd.getD x 0) ∨
      (k = 0 ∧ ∀ x, x < n → x ∉ D → U ≤ Dd.getD x 0))
    (hQ1 : ∀ q ∈ Q', 0 ≤ q.2 ∧ q.2 < n ∧ dist[q.2.toNat]! ≤ q.1 ∧ 0 ≤ q.1 ∧ q.1 < U)
    (hQ2 : ∀ x < n, x ∉ D → x ≠ v → dist[x]! < U → (dist[x]!, (x : Int)) ∈ Q') :
    let used' := Cpp.set used (v : Int) true
    let r := (out v).foldl (astep used') (dist, Q')
    SR n (D ++ [v]) r.1 used' ∧ PInv n U (EdOf n out) r.1.toList (doneOf n (D ++ [v])) (D ++ [v]) (cs ++ [k]) ∧
      QI n U (D ++ [v]) r.1 r.2 ∧ r.2.length ≤ Q'.length + (out v).length := by
  intro used' r
  obtain ⟨hds, hus, hu⟩ := hS
  have hrange : ∀ p ∈ out v, 0 ≤ p.1 ∧ p.1.toNat < dist.size := by
    intro p hp; obtain ⟨h1, h2, _, _⟩ := hV v hvn p hp; exact ⟨h1, by rw [hds]; omega⟩
  have hus' : used'.size = n := by simp [used', hus]
  have hu' : ∀ x < n, used'[x]! = decide (x ∈ D ++ [v]) := by
    intro x hx
    simp only [used']
    rw [getElemBang_set _ _ _ _ (by simp; omega)]
    by_cases e : x = v
    · subst e; simp
    · simp [e, hu x hx]
  have hdn : ∀ x < dist.size, used'[x]! = decide ((doneOf n (D ++ [v])).getD x 0 ≠ 0) := by
    intro x hx
    rw [hds] at hx
    rw [hu' x hx, doneOf_getD n _ x hx]
    by_cases h : x ∈ D ++ [v] <;> simp [h]
  have hlist := fold_list used' (doneOf n (D ++ [v])) v (out v) dist Q' hrange hdn
  obtain ⟨P, hP, hlen, hqP, hle, hch⟩ := fold_props used' (out v) dist Q' hrange
  have hsz : r.1.size = n := by
    have : ∀ (ps : List (Int × Int)) (st : Array Int × List (Int × Int)),
        (ps.foldl (astep used') st).1.size = st.1.size := by
      intro ps; induction ps with
      | nil => intro st; rfl
      | cons p ps ih => intro st; simp only [List.foldl_cons]; rw [ih, astep_size]
    simp only [r]; rw [this]; exact hds
  -- the invariant from PInv_step
  have hstep := PInv_step hI ((out v).map (fun p => ((v, p.1.toNat, p.2) : Edge))) v k
    (fun e he => by
      obtain ⟨h1, p, hp, he'⟩ := mem_EdOf.mp he
      obtain ⟨a1, a2, a3, a4⟩ := hV _ h1 p hp
      rw [he']; exact ⟨h1, by simp; omega, a3, a4⟩)
    (fun e he => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      exact ⟨mem_EdOf.mpr ⟨hvn, p, hp, rfl⟩, rfl⟩)
    (fun e he he1 => by
      obtain ⟨_, p, hp, he'⟩ := mem_EdOf.mp he
      rw [he1] at hp he'
      exact List.mem_map.mpr ⟨p, hp, by rw [he']⟩)
    hvn hvD hk0 hkU hU hcase
  refine ⟨⟨hsz, hus', hu'⟩, ?_, ⟨?_, ?_⟩, by rw [hP]; simp; omega⟩
  · have : r.1.toList = ((out v).map (fun p => ((v, p.1.toNat, p.2) : Edge))).foldl
        (relaxL (doneOf n (D ++ [v]))) (Dd.set v k) := by rw [← hdist]; exact hlist
    rw [this]; exact hstep
  · intro q hq
    rw [hP] at hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨a1, a2, a3, a4, a5⟩ := hQ1 q hq
      exact ⟨a1, a2, le_trans (hle _) a3, a4, a5⟩
    · obtain ⟨⟨p, hp, rfl⟩, h2⟩ := hqP _ hq
      obtain ⟨a1, a2, a3, a4⟩ := hV v hvn p hp
      exact ⟨a1, a2, h2, a3, a4⟩
  · intro x hx hxD hlt
    rw [hP]
    have hxD0 : x ∉ D := fun h => hxD (by simp [h])
    have hxv : x ≠ v := fun h => hxD (by simp [h])
    by_cases e : r.1[x]! = dist[x]!
    · rw [e] at hlt ⊢
      exact List.mem_append_left _ (hQ2 x hx hxD0 hxv hlt)
    · exact List.mem_append_right _ (hch x e)

/-- The state between picks (`A`): the invariant on the array, and the queue invariant. -/
def SpanA (n : Nat) (U : Int) (out : Nat → List (Int × Int)) (D : List Nat) (cs : List Int) (dist : Array Int)
    (used : Array Bool) (Q : List (Int × Int)) : Prop :=
  SR n D dist used ∧ PInv n U (EdOf n out) dist.toList (doneOf n D) D cs ∧ QI n U D dist Q

/-- The state at the start of a span (`B`): the root `i` has distance 0 and is the only pair of the queue; every
other unpicked vertex has distance at least `U`. -/
def SpanB (n : Nat) (U : Int) (out : Nat → List (Int × Int)) (D : List Nat) (cs : List Int) (dist : Array Int)
    (used : Array Bool) (Q : List (Int × Int)) (i : Nat) : Prop :=
  SR n D dist used ∧ ∃ Dd0, PInv n U (EdOf n out) Dd0 (doneOf n D) D cs ∧ dist.toList = Dd0.set i 0 ∧
    i ∉ D ∧ i < n ∧ (∀ x < n, x ∉ D → U ≤ Dd0.getD x 0) ∧ Q = [(0, (i : Int))]

theorem set_getD_self (l : List Int) (v : Nat) (hv : v < l.length) : l.set v (l.getD v 0) = l := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_set]
    split
    · rename_i e; subst e; simp [List.getD_eq_getElem?_getD, hv]
    · rfl

/-- A fresh pop in state `A`. -/
theorem freshA {n : Nat} {U : Int} {out : Nat → List (Int × Int)} (hV : ValidP n U out) (hU : 0 ≤ U)
    {D : List Nat} {cs : List Int} {dist : Array Int} {used : Array Bool} {Q Q' : List (Int × Int)}
    {x : Int × Int} (hA : SpanA n U out D cs dist used Q) (hQ : Q.Perm (x :: Q')) (hmin : ∀ q ∈ Q, x.1 ≤ q.1)
    (hc : ¬ (Cpp.get used x.2 || decide (Cpp.get dist x.2 < x.1)) = true) :
    let v := x.2.toNat
    let used' := Cpp.set used (v : Int) true
    let r := (out v).foldl (astep used') (dist, Q')
    Cpp.get dist x.2 = x.1 ∧ SpanA n U out (D ++ [v]) (cs ++ [x.1]) r.1 used' r.2 ∧
      r.2.length ≤ Q'.length + (out v).length ∧ v < n ∧ v ∉ D := by
  intro v used' r
  obtain ⟨hS, hI, hQI⟩ := hA
  have hxQ : x ∈ Q := hQ.mem_iff.mpr List.mem_cons_self
  obtain ⟨h0, hn, hle, hk0, hkU⟩ := hQI.1 x hxQ
  have hvi : (v : Int) = x.2 := Int.toNat_of_nonneg h0
  have hvn : v < n := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
  obtain ⟨hcu, hcd⟩ := hc
  have hdv : dist[v]! = x.1 := by simp only [get_eq] at hcd; simp only [v]; omega
  have hvD : v ∉ D := by
    intro h; apply hcu; rw [get_eq]; simp only [v] at h ⊢; rw [hS.2.2 _ (by omega)]; simp [h]
  have hgetD : dist.toList.getD v 0 = x.1 := by rw [getD_toList]; exact hdv
  have hfresh := fresh_step hV hU (Dd := dist.toList) (k := x.1) hS hI
    (by rw [← hgetD, set_getD_self _ _ (by simp [hS.1]; omega)]) hvn hvD hk0 (le_of_lt hkU)
    (Or.inl ⟨hkU, hgetD, fun y hy hyD => by
      rw [getD_toList]
      by_cases hlt : dist[y]! < U
      · exact hmin _ (hQI.2 y hy hyD hlt)
      · omega⟩)
    (fun q hq => hQI.1 q (perm_mem' hQ hq))
    (fun y hy hyD hyv hlt => perm_mem_ne' hQ (hQI.2 y hy hyD hlt) (by
      intro e; apply hyv; have := congrArg Prod.snd e; simp at this; omega))
  obtain ⟨h1, h2, h3, h4⟩ := hfresh
  exact ⟨by rw [get_eq]; exact hdv, ⟨h1, h2, h3⟩, h4, hvn, hvD⟩

/-- The pop in state `B`: the root itself. -/
theorem freshB {n : Nat} {U : Int} {out : Nat → List (Int × Int)} (hV : ValidP n U out) (hU : 0 ≤ U)
    {D : List Nat} {cs : List Int} {dist : Array Int} {used : Array Bool} {Q : List (Int × Int)} {i : Nat}
    (hB : SpanB n U out D cs dist used Q i) :
    let used' := Cpp.set used (i : Int) true
    let r := (out i).foldl (astep used') (dist, [])
    Q = [(0, (i : Int))] ∧ Cpp.get dist (i : Int) = 0 ∧ Cpp.get used (i : Int) = false ∧
      SpanA n U out (D ++ [i]) (cs ++ [0]) r.1 used' r.2 ∧ r.2.length ≤ (out i).length ∧ i < n ∧ i ∉ D := by
  intro used' r
  obtain ⟨hS, Dd0, hI, hdist, hiD, hin, hall, hQ⟩ := hB
  have hlen0 : Dd0.length = n := hI.ddl
  have hget : ∀ y : Nat, dist[y]! = if y = i then 0 else Dd0.getD y 0 := by
    intro y
    rw [← getD_toList, hdist]
    by_cases e : y = i
    · subst e; simp [List.getD_eq_getElem?_getD, hlen0, hin]
    · simp [e, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm e)]
  have hfresh := fresh_step hV hU (k := 0) (Q' := []) hS hI hdist hin hiD le_rfl hU (Or.inr ⟨rfl, hall⟩)
    (fun q hq => by simp at hq) (fun y hy hyD hyi hlt => by
      rw [hget, if_neg hyi] at hlt; have := hall y hy hyD; omega)
  obtain ⟨h1, h2, h3, h4⟩ := hfresh
  refine ⟨hQ, by rw [get_natCast, hget]; simp, ?_, ⟨h1, h2, h3⟩, by simpa using h4, hin, hiD⟩
  rw [get_natCast, hS.2.2 i hin]; simp [hiD]

/-! ## The measure -/

/-- `Σ_{x < k, ¬ used[x]} (deg x + 1)`. -/
def restU (out : Nat → List (Int × Int)) (used : Array Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => restU out used k + if used[k]! then 0 else (out k).length + 1

theorem restU_set (out : Nat → List (Int × Int)) (used : Array Bool) (v : Nat) (hv : v < used.size)
    (hu : used[v]! = false) (k : Nat) :
    restU out used k = restU out (Cpp.set used (v : Int) true) k + if v < k then (out v).length + 1 else 0 := by
  induction k with
  | zero => simp [restU]
  | succ k ih =>
    simp only [restU, ih]
    rw [getElemBang_set _ _ _ _ (by simpa using hv)]
    by_cases e : k = v
    · subst e; simp [hu]
    · simp only [Int.toNat_natCast, e, ↓reduceIte]
      have hvk : v < k + 1 ↔ v < k := by omega
      by_cases hk : used[k]! = true
      · by_cases h2 : v < k
        · simp [hk, h2, hvk.mpr h2]
        · simp [hk, h2, (not_congr hvk).mpr h2]
      · by_cases h2 : v < k
        · simp [hk, h2, hvk.mpr h2]; omega
        · simp [hk, h2, (not_congr hvk).mpr h2]

theorem restU_le (out : Nat → List (Int × Int)) (used : Array Bool) (k : Nat) :
    restU out used k ≤ restU out (Array.replicate used.size false) k := by
  induction k with
  | zero => simp [restU]
  | succ k ih =>
    simp only [restU]
    have : (Array.replicate used.size false)[k]! = false := by
      by_cases h : k < used.size
      · simp [h]
      · simp [h]
    rw [this]; split <;> simp <;> omega

theorem astep_len (used : Array Bool) (st : Array Int × List (Int × Int)) (p : Int × Int) :
    (astep used st p).2.length ≤ st.2.length + 1 := by
  unfold astep; split <;> simp

theorem fold_astep_len (used : Array Bool) (ps : List (Int × Int)) (st : Array Int × List (Int × Int)) :
    (ps.foldl (astep used) st).2.length ≤ st.2.length + ps.length := by
  induction ps generalizing st with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (astep used st p); have := astep_len used st p; omega

theorem restU_ge (out : Nat → List (Int × Int)) (used : Array Bool) (x n : Nat) (hx : x < n)
    (hu : used[x]! = false) : (out x).length + 1 ≤ restU out used n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [restU]
    by_cases e : x = n
    · subst e; simp [hu]
    · have := ih (by omega); split <;> omega

end Proofs.ListPrimMath
