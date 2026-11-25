import Proofs.Cpp.Gen.GraphList
import Proofs.Cpp.GraphListEdge
import Proofs.Cpp.Lib.Basic

/-! # `ListGraph<Cost, E>` (library/graph/graph_list.hpp)

The adjacency lists `adj` (row `v` holds the edges out of `v` in insertion order), the counts `n_` and `m_`, and
the caches of the shortest path computations (`shortest_path_dist`, `shortest_path_parent`, maps from a start
vertex to its arrays; the algorithms that fill them are separate members). The construction and the edge
additions are proved for `E = Edge<T>` (the default argument, with its id counter); the other members for any `E`.
Costs: the documented worst case of `std::unordered_map` (`size + 1` steps per lookup or `clear`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.GraphList

/-- The empty array of the model (`([] : List α).toArray`). -/
@[simp] theorem empty_eq {α : Type} : (Array.empty : Array α) = ([] : List α).toArray := rfl

/-- The maps of a graph are empty (after construction or `reset_shortest`). -/
def Fresh {Cost E : Type} (g : cp.ListGraph Cost E) : Prop :=
  g.shortest_path_dist = [] ∧ g.shortest_path_parent = []

/-- `ListGraph()`: no vertices. -/
theorem init_0_spec {Cost E : Type} (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.ListGraph.init_0 (Cost := Cost) (E := E))
    ⦃⇓ g c => ⌜g.n_ = 0 ∧ g.m_ = 0 ∧ g.adj = Array.empty ∧ Fresh g ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.ListGraph.init_0]
  simp_all +zetaDelta [Fresh, Cpp.replicate]

/-- `ListGraph(n)`: `n` vertices without edges. -/
theorem init_int_spec {Cost E : Type} (n : Int) (hn : 0 ≤ n) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ (cp.ListGraph.init_int (Cost := Cost) (E := E) n)
    ⦃⇓ g c => ⌜g.n_ = n ∧ g.m_ = 0 ∧ g.adj = Array.replicate n.toNat Array.empty ∧ Fresh g ∧ c = t0 + 1 + n.toNat⌝⦄ := by
  mvcgen [cp.ListGraph.init_int]
  simp_all +zetaDelta [Fresh, Cpp.replicate]

/-- `g[i]`: the row of `i` (the graph is unchanged; writes through the returned reference are outside the model). -/
theorem op_index_spec {Cost E : Type} [Inhabited E] (g : cp.ListGraph Cost E) (i : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.op_index g i
    ⦃⇓ r c => ⌜r.1 = Cpp.get g.adj i ∧ r.2 = g ∧ c = t0 + 1⌝⦄ := by
  mvcgen [cp.ListGraph.op_index]
  simp_all +zetaDelta

/-- The graph with empty maps. -/
def reset {Cost E : Type} (g : cp.ListGraph Cost E) : cp.ListGraph Cost E :=
  { g with shortest_path_dist := [], shortest_path_parent := [] }

theorem reset_shortest_spec {Cost E : Type} (g : cp.ListGraph Cost E) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.reset_shortest g
    ⦃⇓ r c => ⌜r = reset g ∧
      c = t0 + 3 + g.shortest_path_dist.length + g.shortest_path_parent.length⌝⦄ := by
  mvcgen [cp.ListGraph.reset_shortest, Cpp.umapClear]
  simp_all +zetaDelta [reset]
  omega

theorem add_node_spec {Cost E : Type} (g : cp.ListGraph Cost E) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.add_node g
    ⦃⇓ r c => ⌜r = reset { g with n_ := g.n_ + 1, adj := g.adj.push Array.empty } ∧
      c = t0 + 5 + g.shortest_path_dist.length + g.shortest_path_parent.length⌝⦄ := by
  mvcgen [cp.ListGraph.add_node, cp.ListGraph.reset_shortest, Cpp.umapClear]
  simp_all +zetaDelta [reset]
  omega

/-- The rows with the edge `e` appended to the row of `u`. -/
def addTo {E : Type} [Inhabited E] (adj : Array (Array E)) (u : Int) (e : E) : Array (Array E) :=
  Cpp.set adj u ((Cpp.get adj u).push e)

section Edge

variable {T : Type} [Inhabited T]

/-- The state of the `Edge<T>` constructors (its id counter). -/
abbrev Counter (T : Type) := ConstructState.State (cp.Edge T)

/-- `add_edge(from, to, cost)` with `E = Edge<T>`: the edge `⟨from, to, id, cost⟩` with the next id is appended
to the row of `from`; `m_` grows by 1 and the maps are cleared. -/
theorem add_edge_cost_spec (g : cp.ListGraph T (cp.Edge T)) (u v : Int) (cost : T) (s : Counter T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.add_edge g u v cost s
    ⦃⇓ r c => ⌜r.2 = reset { g with m_ := g.m_ + 1, adj := addTo g.adj u ⟨u, v, s.Edge_next_id, cost⟩ } ∧
      r.1.Edge_next_id = s.Edge_next_id + 1 ∧
      c = t0 + 6 + g.shortest_path_dist.length + g.shortest_path_parent.length⌝⦄ := by
  mvcgen [cp.ListGraph.add_edge, cp.ListGraph.reset_shortest, Cpp.umapClear, Construct.make,
    cp.Edge.init_int_int_T]
  simp_all +zetaDelta [reset, addTo]
  omega

/-- `add_edge(from, to)` with `E = Edge<T>`: the cost is `1`. -/
theorem add_edge_spec [One T] (g : cp.ListGraph T (cp.Edge T)) (u v : Int) (s : Counter T) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.add_edge g u v () s
    ⦃⇓ r c => ⌜r.2 = reset { g with m_ := g.m_ + 1, adj := addTo g.adj u ⟨u, v, s.Edge_next_id, 1⟩ } ∧
      r.1.Edge_next_id = s.Edge_next_id + 1 ∧
      c = t0 + 6 + g.shortest_path_dist.length + g.shortest_path_parent.length⌝⦄ := by
  mvcgen [cp.ListGraph.add_edge, cp.ListGraph.reset_shortest, Cpp.umapClear, Construct.make,
    cp.Edge.init_int_int]
  simp_all +zetaDelta [reset, addTo]
  omega

/-- `add_bidirectional_edge(from, to, cost)`: `from -> to` (id `k`) to the row of `from`, then `to -> from`
(id `k + 1`) to the row of `to`; `m_` grows by 2. -/
theorem add_bidirectional_edge_cost_spec (g : cp.ListGraph T (cp.Edge T)) (u v : Int) (cost : T) (s : Counter T)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.add_bidirectional_edge g u v cost s
    ⦃⇓ r c => ⌜r.2 = reset { g with m_ := g.m_ + 2, adj := addTo (addTo g.adj u ⟨u, v, s.Edge_next_id, cost⟩) v ⟨v, u, s.Edge_next_id + 1, cost⟩ } ∧
      r.1.Edge_next_id = s.Edge_next_id + 2 ∧
      c = t0 + 8 + g.shortest_path_dist.length + g.shortest_path_parent.length⌝⦄ := by
  mvcgen [cp.ListGraph.add_bidirectional_edge, cp.ListGraph.reset_shortest, Cpp.umapClear, Construct.make,
    cp.Edge.init_int_int_T]
  simp_all +zetaDelta [reset, addTo]
  omega

theorem add_bidirectional_edge_spec [One T] (g : cp.ListGraph T (cp.Edge T)) (u v : Int) (s : Counter T)
    (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.add_bidirectional_edge g u v () s
    ⦃⇓ r c => ⌜r.2 = reset { g with m_ := g.m_ + 2, adj := addTo (addTo g.adj u ⟨u, v, s.Edge_next_id, 1⟩) v ⟨v, u, s.Edge_next_id + 1, 1⟩ } ∧
      r.1.Edge_next_id = s.Edge_next_id + 2 ∧
      c = t0 + 8 + g.shortest_path_dist.length + g.shortest_path_parent.length⌝⦄ := by
  mvcgen [cp.ListGraph.add_bidirectional_edge, cp.ListGraph.reset_shortest, Cpp.umapClear, Construct.make,
    cp.Edge.init_int_int]
  simp_all +zetaDelta [reset, addTo]
  omega

end Edge

/-! ## Reading the caches -/

/-- `distance(from, to)` after the distances from `from` were computed (`D` is the cached array). -/
theorem distance_int_int_spec {Cost E : Type} [Inhabited Cost] (g : cp.ListGraph Cost E) (u v : Int)
    (D : Array Cost) (hD : umapFind g.shortest_path_dist u = some D) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.distance_int_int g u v
    ⦃⇓ r c => ⌜r.1 = Cpp.get D v ∧ r.2 = g ∧ c = t0 + 2 + g.shortest_path_dist.length⌝⦄ := by
  mvcgen [cp.ListGraph.distance_int_int, Cpp.umapIndex]
  all_goals simp_all +zetaDelta
  all_goals simp +arith

/-- `distance(from)`: a copy of the cached array of `from`; for a start without computed distances the map gets the
key with an empty array, which is returned. -/
theorem distance_int_spec {Cost E : Type} [Inhabited Cost] (g : cp.ListGraph Cost E) (u : Int) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.distance_int g u
    ⦃⇓ r c => ⌜r.1 = (umapFind g.shortest_path_dist u).getD Array.empty ∧
      r.2 = { g with shortest_path_dist := match umapFind g.shortest_path_dist u with
        | some _ => g.shortest_path_dist
        | none => g.shortest_path_dist ++ [(u, Array.empty)] } ∧
      c = t0 + 2 + g.shortest_path_dist.length + r.1.size⌝⦄ := by
  mvcgen [cp.ListGraph.distance_int, Cpp.umapIndex]
  all_goals simp_all +zetaDelta
  all_goals first | (simp +arith; done) | exact ⟨rfl, by simp +arith⟩

/-- The parent chain `cur, P[cur], P[P[cur]], …` up to (not including) `-1`. -/
inductive Chain (P : Array Int) : Int → List Int → Prop
  | stop : Chain P (-1) []
  | step (cur : Int) (L : List Int) : cur ≠ -1 → Chain P (Cpp.get P cur) L → Chain P cur (cur :: L)

theorem chain_det {P : Array Int} {c : Int} {L L' : List Int} (h : Chain P c L) (h' : Chain P c L') : L = L' := by
  induction h generalizing L' with
  | stop => cases h' with
    | stop => rfl
    | step _ _ hne _ => exact absurd rfl hne
  | step cur L hne _ ih => cases h' with
    | stop => exact absurd rfl hne
    | step _ L2 _ h2 => rw [ih h2]

theorem chain_cons {P : Array Int} {c : Int} {L : List Int} (h : Chain P c L) (hc : c ≠ -1) :
    ∃ L', L = c :: L' ∧ Chain P (Cpp.get P c) L' := by
  cases h with
  | stop => exact absurd rfl hc
  | step _ L' _ h' => exact ⟨L', rfl, h'⟩

open Classical in
/-- The length of the chain from `c` (0 when there is none). -/
noncomputable def clen (P : Array Int) (c : Int) : Nat :=
  if h : ∃ L, Chain P c L then (Classical.choose h).length else 0

theorem clen_of {P : Array Int} {c : Int} {L : List Int} (h : Chain P c L) : clen P c = L.length := by
  have hex : ∃ L, Chain P c L := ⟨L, h⟩
  unfold clen
  rw [dite_cond_eq_true (eq_true hex), chain_det (Classical.choose_spec hex) h]

theorem step_cost (s t0 S k k' : Nat) (hk : k' = k) (hs : s = t0 + 1 + S * (k + 3)) :
    s + 1 + 1 + (k' + 1) = t0 + 1 + (S + 1) * (k + 3) := by
  subst hk hs; rw [Nat.add_mul]; omega

/-- `shortest_path(from, to)`: when the parents `P` of `from` are cached and the chain from `to` reaches `-1`
(`Chain P to L`), the result is the chain reversed (it ends with `to`); the graph is unchanged. -/
theorem shortest_path_spec {Cost E : Type} (g : cp.ListGraph Cost E) (u v : Int) (P : Array Int)
    (hP : umapFind g.shortest_path_parent u = some P) (L : List Int) (hL : Chain P v L)
    (hfuel : L.length < 2 ^ 64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.shortest_path g u v
    ⦃⇓ r c => ⌜r.1.toList = L.reverse ∧ r.2 = g ∧
      c = t0 + 2 + L.length * (g.shortest_path_parent.length + 5)⌝⦄ := by
  mvcgen [cp.ListGraph.shortest_path, Cpp.umapIndex]
  case vc1.inv =>
    exact ⟨fun ⟨sp, path, cur⟩ c => ⌜sp = g.shortest_path_parent ∧ ∃ L1 L2, L = L1 ++ L2 ∧
             path.toList = L1.reverse.reverse ∧ Chain P cur L2 ∧
             c = t0 + 1 + L1.length * (g.shortest_path_parent.length + 3)⌝,
           fun ⟨sp, path, cur⟩ c => ⌜sp = g.shortest_path_parent ∧ path.toList = L ∧
             c = t0 + 2 + L.length * (g.shortest_path_parent.length + 3)⌝,
           fun ⟨_, _, cur⟩ => clen P cur⟩
  all_goals simp +zetaDelta at *
  case vc2.step.isTrue =>
    rename_i h1 h0
    obtain ⟨hsp, L2, hL2, hch, hc⟩ := h1
    rw [h0] at hch
    cases hch with
    | stop =>
      refine ⟨hsp, by simp [hL2], ?_⟩
      rw [hL2, hc]; simp; omega
    | step _ _ hne _ => exact absurd rfl hne
  case vc3.step.isFalse.h_1 =>
    rename_i row hrow _ _ h1 h0
    obtain ⟨hsp, L2, hL2, hch, hc⟩ := h1
    rw [hsp, hP] at hrow
    cases hrow
    obtain ⟨L3, rfl, hnext⟩ := chain_cons hch h0
    refine ⟨⟨hsp, L3, hL2, hnext, ?_⟩, ?_⟩
    · exact step_cost _ _ _ _ _ (congrArg List.length hsp) hc
    · rw [clen_of hnext, clen_of (Chain.step _ _ h0 hnext)]; simp
  case vc4.step.isFalse.h_2 =>
    rename_i hnone _ _ h1 _
    rw [h1.1, hP] at hnone
    cases hnone
  case vc5.pre =>
    exact ⟨⟨hL, ‹_›⟩, by rw [clen_of hL]; exact hfuel⟩
  case vc6.post.success =>
    rename_i r _ _ _ _ h0 _
    obtain ⟨hsp, hpath, hc⟩ := h0
    refine ⟨by simp [hpath], by cases g; simp_all, ?_⟩
    have hsz : r.2.1.size = L.length := by rw [← Array.length_toList, hpath]
    rw [hc, hsz, Nat.mul_add, Nat.mul_add]; omega

end Proofs.Cpp.GraphList
