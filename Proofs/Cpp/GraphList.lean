import Proofs.Cpp.Gen.GraphList
import Proofs.Cpp.GraphListEdge
import Proofs.Cpp.Lib.Basic
import Proofs.Math.ParentChain
import Proofs.Math.ListDijkstraMath
import Proofs.Math.ListBellmanFordMath

/-! # `ListGraph<Cost, E>` (library/graph/graph_list.hpp)

The adjacency lists `adj` (row `v` holds the edges out of `v` in insertion order), the counts `n_` and `m_`, and
the caches of the shortest path computations (`shortest_path_dist`, `shortest_path_parent`, maps from a start
vertex to its arrays; the algorithms that fill them are separate members). The construction and the edge
additions are proved for `E = Edge<T>` (the default argument, with its id counter); the other members for any `E`.
Costs: the documented worst case of `std::unordered_map` (`size + 1` steps per lookup or `clear`). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen Proofs.ParentChain

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

/-! ## `dijkstra` (`Cost = long long`) -/

section Dijkstra
open Proofs.ListDijkstraMath

local instance : Cpp.NumericTraits "Cost" Int := Cpp.intNumericTraits "Cost" 64 true

def U : Int := 2 ^ 61 - 1

@[spec] theorem unr_spec {E : Type} {Q : PostCond Int PS} :
    ⦃fun t => Q.1 U (t + 1)⦄ (cp.ListGraph.UNREACHABLE (Cost := Int) (E := E)) ⦃Q⦄ := by
  mvcgen [cp.ListGraph.UNREACHABLE]

/-- The comparison of `std::priority_queue<std::pair<long long, int>, …, std::greater<>>`. -/
abbrev G : Int × Int → Int × Int → Bool :=
  fun a b => pairLt (fun a b : Int => decide (a < b)) (fun a b : Int => decide (a < b)) b a

theorem G_irr (a : Int × Int) : G a a = false := by
  simp [G, pairLt]

theorem G_trans (a b c : Int × Int) (h1 : G a b = true) (h2 : G b c = true) : G a c = true := by
  simp [G, pairLt] at *; omega

theorem G_min {x y : Int × Int} (h : G x y = false) : x.1 ≤ y.1 := by
  simp [G, pairLt] at h; omega

theorem perm_eraseIdx {α : Type} {q : List α} {i : Nat} {x : α} (h : q[i]? = some x) :
    q.Perm (x :: q.eraseIdx i) := by
  have hi : i < q.length := by
    rcases Nat.lt_or_ge i q.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have hx : q[i] = x := by rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h
  have e : q = q.take i ++ x :: q.drop (i + 1) := by
    rw [← hx, List.getElem_cons_drop]; exact (List.take_append_drop i q).symm
  rw [List.eraseIdx_eq_take_drop_succ]
  conv => lhs; rw [e]
  exact List.perm_middle

/-- The top of a nonempty queue and the queue after `pop`. -/
theorem top_pop (Q : List (Int × Int)) (x : Int × Int) (h : pqBest G Q = some x) :
    Q.Perm (x :: Q.eraseIdx (pqBestIdx G Q)) ∧ ∀ q ∈ Q, x.1 ≤ q.1 := by
  have hne : Q ≠ [] := by intro e; subst e; simp [pqBest] at h
  obtain ⟨y, h1, h2, h3⟩ := pqBest_spec G G_irr G_trans Q hne
  rw [h] at h2; cases h2
  exact ⟨perm_eraseIdx h1, fun q hq => G_min (h3 q hq)⟩

/-- The pair `(to, cost)` of an edge. -/
def toPair {E : Type} [Field "to" E Int] [Field "cost" E Int] (e : E) : Int × Int :=
  (Field.get (member := "to") e, Field.get (member := "cost") e)

/-- The edges `(to, cost)` of each vertex. -/
def outOf {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (adj : Array (Array E)) (x : Nat) :
    List (Int × Int) := (adj[x]!).toList.map toPair

theorem relax_len (v : Int) (st : Array Int × Array Int × List (Int × Int)) (e : Int × Int) :
    (relax v st e).2.2.length ≤ st.2.2.length + 1 := by
  unfold relax; split <;> simp

theorem fold_len (v : Int) (es : List (Int × Int)) (st : Array Int × Array Int × List (Int × Int)) :
    (es.foldl (relax v) st).2.2.length ≤ st.2.2.length + es.length := by
  induction es generalizing st with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (relax v st e); have := relax_len v st e; omega


/-- `Σ_{x < n} (deg x + 1) = n + m`. -/
abbrev R0 {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E) : Nat :=
  rest (outOf g.adj) [] g.n_.toNat

/-- The step bound of one queue operation or relaxation: the queues have fewer than `2 R0 + 2` pairs. -/
abbrev K {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E) : Nat :=
  Nat.log2 (2 * R0 g + 2) + 3

/-- The steps before the main loop. -/
abbrev C1 {E : Type} (g : cp.ListGraph Int E) : Nat := 4 + g.shortest_path_dist.length + 2 * g.n_.toNat

/-- The invariant of the main loop with its potential `K (2 restS + |Q|)`. -/
def Cont {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E) (s : Nat)
    (t0 : Nat) (st : Array Int × Array Int × List (Int × Int)) (c : Nat) : Prop :=
  (∃ D L, Inv g.n_.toNat s U (outOf g.adj) st.1 st.2.1 st.2.2 D L) ∧ t0 + C1 g ≤ c ∧
    c + K g * (2 * restS U (outOf g.adj) st.1 st.2.2 g.n_.toNat + st.2.2.length) ≤
      t0 + C1 g + K g * (2 * R0 g + 1)

theorem restS_ge (U : Int) (out : Nat → List (Int × Int)) (d : Array Int) (Q : List (Int × Int)) (x n : Nat)
    (hx : x < n) (h : ¬(d[x]! < U ∧ (d[x]!, (x : Int)) ∉ Q)) : (out x).length + 1 ≤ restS U out d Q n := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [restS]
    by_cases e : x = n
    · subst e; rw [if_neg h]; omega
    · have := ih (by omega); split <;> omega

theorem cont_bound {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] {g : cp.ListGraph Int E}
    {s t0 : Nat} {st : Array Int × Array Int × List (Int × Int)} {c : Nat} (h : Cont g s t0 st c) :
    2 * restS U (outOf g.adj) st.1 st.2.2 g.n_.toNat + st.2.2.length ≤ 2 * R0 g + 1 := by
  obtain ⟨_, h1, h2⟩ := h
  have hK : 0 < K g := by unfold K; omega
  exact Nat.le_of_mul_le_mul_left (by omega) hK

theorem log_bound {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := log2_mono2 a b h

/-- The facts about a pair popped with the distance of its vertex. -/
theorem fresh_facts {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] {g : cp.ListGraph Int E}
    {s t0 : Nat} {b : Array Int × Array Int × List (Int × Int)} {c0 : Nat} (hC : Cont g s t0 b c0)
    {x : Int × Int} (hx : pqBest G b.2.2 = some x) (hfresh : ¬ (get b.1 x.2 < x.1)) :
    0 ≤ x.2 ∧ x.2 < g.n_.toNat ∧ get b.1 x.2 = x.1 ∧
      (b.2.2.eraseIdx (pqBestIdx G b.2.2)).length + (outOf g.adj x.2.toNat).length + 2 ≤ 2 * R0 g + 1 := by
  obtain ⟨hperm, hmin⟩ := top_pop _ _ hx
  have hb := cont_bound hC
  obtain ⟨⟨D, L, hI⟩, _, _⟩ := hC
  have hxQ : x ∈ b.2.2 := hperm.mem_iff.mpr List.mem_cons_self
  obtain ⟨h0, hn, hle, _, _⟩ := hI.qok x hxQ
  have heq : get b.1 x.2 = x.1 := by rw [get_eq] at hfresh ⊢; omega
  refine ⟨h0, by omega, heq, ?_⟩
  have hr := restS_ge U (outOf g.adj) b.1 b.2.2 x.2.toNat g.n_.toNat (by omega) (by
    intro ⟨_, h2⟩; apply h2
    have : (x.2.toNat : Int) = x.2 := Int.toNat_of_nonneg h0
    rw [this, ← get_eq, heq]; exact hxQ)
  have := hperm.length_eq; simp at this
  omega

theorem dijkstra_spec {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int]
    (g : cp.ListGraph Int E) (s : Nat) (hn : g.adj.size = g.n_.toNat) (hn0 : 0 ≤ g.n_) (hs : s < g.n_.toNat)
    (hV : Valid g.n_.toNat (outOf g.adj)) (hnew : umapFind g.shortest_path_dist s = none)
    (hsmall : 2 * R0 g + 1 < 2 ^ 64) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.dijkstra g s
    ⦃⇓ r c => ⌜(∃ d par D L, Inv g.n_.toNat s U (outOf g.adj) d par [] D L ∧
      r = { g with shortest_path_dist := umapPut g.shortest_path_dist s d,
                   shortest_path_parent := umapPut g.shortest_path_parent s par }) ∧
      c ≤ t0 + C1 g + K g * (2 * R0 g + 1) + 3 + g.shortest_path_dist.length + g.shortest_path_parent.length⌝⦄ := by
  mvcgen [cp.ListGraph.dijkstra, Cpp.umapCount, Cpp.pqPush, Cpp.pqTop, Cpp.pqPop, Cpp.umapSet]
  case vc2.inv =>
    exact ⟨fun st c => ⌜Cont g s t0 st c⌝,
           fun st c => ⌜st.2.2 = [] ∧ (∃ D L, Inv g.n_.toNat s U (outOf g.adj) st.1 st.2.1 st.2.2 D L) ∧
             c ≤ t0 + C1 g + K g * (2 * R0 g + 1) + 1⌝,
           fun st => 2 * restS U (outOf g.adj) st.1 st.2.2 g.n_.toNat + st.2.2.length⟩
  case inv1 =>
    rename_i b _ _ _ _ c0 _ _ x _ _ _ _
    exact ⇓⟨xs, st⟩ c => ⌜st = (xs.prefix.map toPair).foldl (relax x.2)
        (b.1, b.2.1, b.2.2.eraseIdx (pqBestIdx G b.2.2)) ∧ c0 ≤ c ∧ c ≤ c0 + K g * (xs.prefix.length + 1)⌝
  case vc8.step.isFalse.h_1.isFalse.isFalse.pre =>
    rename_i b _ _ _ _ c0 hC _ x hx _ _ _
    refine ⟨by simp +zetaDelta, by simp +zetaDelta; omega, ?_⟩
    have := cont_bound hC
    have := log_bound (a := b.2.2.length) (b := 2 * R0 g + 2) (by omega)
    simp +zetaDelta; unfold K; omega
  case vc6.step.isTrue =>
    rename_i b _ _ _ _ c0 hC _ x hx _ _ hfresh pref cur suff hsplit st _ _ _ _ c hinv hcond _ _
    simp at hinv
    obtain ⟨heq, hc0, hc⟩ := hinv
    obtain ⟨h0, hn', hdv, hlen⟩ := fresh_facts hC hx (by simpa using hfresh)
    refine ⟨?_, by (try simp +zetaDelta); omega, ?_⟩
    · rw [List.map_append, List.foldl_append, ← heq]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      unfold relax toPair
      rw [if_pos (by simpa using hcond)]
    · have hpl : pref.length + 1 ≤ (outOf g.adj x.2.toNat).length := by
        have : (outOf g.adj x.2.toNat).length = (get g.adj x.2).toList.length := by simp [outOf, get_eq]
        rw [this]; simp +zetaDelta at hsplit; rw [hsplit]; simp
      have hq := fold_len x.2 (List.map toPair pref) (b.1, b.2.1, b.2.2.eraseIdx (pqBestIdx G b.2.2))
      rw [← heq] at hq
      simp only [List.length_map] at hq
      have := log_bound (a := st.2.2.length + 1) (b := 2 * R0 g + 2) (by omega)
      simp +zetaDelta; unfold K at hc ⊢
      rw [Nat.mul_succ]; omega
  case vc7.step.isFalse =>
    rename_i b _ _ _ _ c0 hC _ x hx _ _ hfresh pref cur suff hsplit st _ _ _ _ c hinv hcond
    simp at hinv
    obtain ⟨heq, hc0, hc⟩ := hinv
    refine ⟨?_, by (try simp +zetaDelta); omega, ?_⟩
    · rw [List.map_append, List.foldl_append, ← heq]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      unfold relax toPair
      rw [if_neg (by simpa using hcond)]
    · simp +zetaDelta; unfold K at hc ⊢; rw [Nat.mul_succ]; omega
  case vc9.step.isFalse.h_1.isFalse.isFalse.post.success =>
    rename_i b _ _ _ _ c0 hC _ x hx _ _ hfresh r _ _ _ _ c hinv
    simp at hinv
    obtain ⟨heq, hc0, hc⟩ := hinv
    obtain ⟨h0, hn', hdv, _⟩ := fresh_facts hC hx (by simpa using hfresh)
    have hb := cont_bound hC
    obtain ⟨⟨D, L, hI⟩, hC2, hC3⟩ := hC
    obtain ⟨hperm, hmin⟩ := top_pop _ _ hx
    obtain ⟨v, hv⟩ : ∃ v : Nat, x.2.toNat = v := ⟨_, rfl⟩
    have hvi : (v : Int) = x.2 := by rw [← hv]; exact Int.toNat_of_nonneg h0
    have hdv' : b.1[v]! = x.1 := by rw [← hdv, get_eq, hv]
    have hQ : b.2.2.Perm ((x.1, (v : Int)) :: b.2.2.eraseIdx (pqBestIdx G b.2.2)) := by rw [hvi]; exact hperm
    have hvD : v ∉ D := not_redone hI (hQ.mem_iff.mpr List.mem_cons_self) hdv'
    have hout : (get g.adj x.2).toList.map toPair = outOf g.adj v := by simp [outOf, get_eq, hv]
    have hvn : v < g.n_.toNat := by omega
    have hr : r = (outOf g.adj v).foldl (relax (v : Int)) (b.1, b.2.1, b.2.2.eraseIdx (pqBestIdx G b.2.2)) := by
      rw [heq, hvi]; simp +zetaDelta [hout]
    obtain ⟨hI', hlen'⟩ := inv_fresh hV hI hQ hmin hdv' hvD
    rw [← hr] at hI' hlen'
    have e1 := rest_eq hI g.n_.toNat le_rfl
    have e2 := rest_eq hI' g.n_.toNat le_rfl
    have e3 := rest_step (outOf g.adj) D v hvD g.n_.toNat
    rw [if_pos hvn] at e3
    have hlq := hperm.length_eq; simp +zetaDelta at hlq
    have hdeg : (get g.adj x.2).size = (outOf g.adj v).length := by rw [← hout]; simp
    simp +zetaDelta at hlen' hc
    -- the potential
    have hA : (2 * restS U (outOf g.adj) r.1 r.2.2 g.n_.toNat + r.2.2.length) + ((outOf g.adj v).length + 1) + 1 ≤
        2 * restS U (outOf g.adj) b.1 b.2.2 g.n_.toNat + b.2.2.length := by omega
    have hK := Nat.mul_le_mul_left (K g) hA
    rw [Nat.mul_add, Nat.mul_add] at hK
    rw [hdeg] at hc
    refine ⟨⟨⟨D ++ [v], x.1, hI'⟩, by (try simp +zetaDelta); omega, ?_⟩, by (try simp +zetaDelta); omega⟩
    simp +zetaDelta
    omega
  case vc5.step.isFalse.h_1.isFalse.isTrue =>
    rename_i b _ _ _ _ c hC _ x hx0 _ _ hst
    have hx : pqBest G b.2.2 = some x := hx0
    have hb := cont_bound hC
    obtain ⟨⟨D, L, hI⟩, hC2, hC3⟩ := hC
    obtain ⟨hperm, hmin⟩ := top_pop _ _ hx
    have hst' : b.1[x.2.toNat]! < x.1 := by
      have := hst; simp +zetaDelta [get_eq] at this; exact of_decide_eq_true this
    have hI' := inv_stale (v := x.2) hI hperm hmin hst'
    have e1 := rest_eq hI g.n_.toNat le_rfl
    have e2 := rest_eq hI' g.n_.toNat le_rfl
    have hlq := hperm.length_eq; simp +zetaDelta at hlq
    have := log_bound (a := b.2.2.length) (b := 2 * R0 g + 2) (by omega)
    have hK : K g * (2 * restS U (outOf g.adj) b.1 (b.2.2.eraseIdx (pqBestIdx G b.2.2)) g.n_.toNat +
        (b.2.2.eraseIdx (pqBestIdx G b.2.2)).length) + K g =
        K g * (2 * restS U (outOf g.adj) b.1 b.2.2 g.n_.toNat + b.2.2.length) := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hKdef : K g = Nat.log2 (2 * R0 g + 2) + 3 := rfl
    have hmeas : 2 * restS U (outOf g.adj) b.1 (b.2.2.eraseIdx (pqBestIdx G b.2.2)) g.n_.toNat +
        (b.2.2.eraseIdx (pqBestIdx G b.2.2)).length <
        2 * restS U (outOf g.adj) b.1 b.2.2 g.n_.toNat + b.2.2.length := by omega
    refine ⟨⟨⟨D, x.1, hI'⟩, by simp +zetaDelta; omega, ?_⟩, by simpa +zetaDelta using hmeas⟩
    simp +zetaDelta
    unfold G at hK
    omega
  case vc3.step.isTrue =>
    rename_i b _ _ _ _ c hC hemp
    obtain ⟨hI, _, h3⟩ := hC
    refine ⟨by simpa +zetaDelta using hemp, hI, by omega⟩
  case vc4.step.isFalse.h_1.isTrue =>
    rename_i h _ _ h'
    simp_all
  case vc11.step.isFalse.h_2 =>
    rename_i b _ _ _ _ c _ hne hnone
    have hne' : b.2.2 ≠ [] := by intro e; simp +zetaDelta [e] at hne
    obtain ⟨y, _, h2, _⟩ := pqBest_spec G G_irr G_trans b.2.2 hne'
    have : pqBest G b.2.2 = none := hnone
    rw [this] at h2; cases h2
  case vc1.isTrue =>
    rename_i h
    simp +zetaDelta [hnew] at h
  case vc10.step.isFalse.h_1.isFalse.isFalse.post.except =>
    simp
  case vc12.isFalse.pre =>
    rename_i hc0 _
    have hU : (0 : Int) < U := by decide
    have hI := inv_init g.n_.toNat s U (outOf g.adj) hs hU
    have e := rest_eq hI g.n_.toNat le_rfl
    have hl1 : Nat.log2 1 = 0 := by decide
    have hR : R0 g = rest (outOf g.adj) [] g.n_.toNat := rfl
    refine ⟨⟨⟨[], 0, ?_⟩, ?_, ?_⟩, ?_⟩
    · simpa +zetaDelta [Cpp.replicate] using hI
    · simp +zetaDelta [C1]; omega
    · simp +zetaDelta [C1, Cpp.replicate] at e ⊢
      rw [← e, ← hR, hl1]; omega
    · simp +zetaDelta [Cpp.replicate, fuel] at e ⊢
      rw [← e]; omega
  case vc13.isFalse.post.success =>
    rename_i r _ _ _ c h
    obtain ⟨hemp, ⟨D, L, hI⟩, hc⟩ := h
    refine ⟨⟨r.1, r.2.1, D, L, by rw [← hemp]; exact hI, by simp +zetaDelta⟩, ?_⟩
    simp +zetaDelta; omega


/-- `dijkstra(s)` when the distances from `s` are already cached: nothing changes. -/
theorem dijkstra_cached_spec {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int]
    (g : cp.ListGraph Int E) (s : Int) (D : Array Int) (hD : umapFind g.shortest_path_dist s = some D) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.dijkstra g s
    ⦃⇓ r c => ⌜r = g ∧ c = t0 + 2 + g.shortest_path_dist.length⌝⦄ := by
  mvcgen [cp.ListGraph.dijkstra, Cpp.umapCount]
  all_goals simp_all +zetaDelta
  all_goals omega

/-- The result of `dijkstra(s)` (nonnegative costs, vertices in range): for every vertex `t`, `distance(s, t)` is
at most the cost of every walk from `s` to `t` (and at most `UNREACHABLE`); when it is below `UNREACHABLE`, the
parents of `s` lead from `t` back to `s` (so `shortest_path(s, t)` returns a walk) along edges whose costs add up to
the distance. -/
theorem dijkstra_correct {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int]
    {n s : Nat} {d par : Array Int} {D : List Nat} {L : Int} {adj : Array (Array E)}
    (hV : Valid n (outOf adj)) (hI : Inv n s U (outOf adj) d par [] D L) (t : Nat) (ht : t < n) :
    d[t]! ≤ U ∧ (∀ w, Walk (outOf adj) s t w → d[t]! ≤ w) ∧
      (d[t]! < U → ∃ C, Chain par t C ∧ WalkB (outOf adj) s C d[t]!) :=
  ⟨hI.dle t ht, fun _ hw => final_le hV hI hw, fun hlt => final_chain hV hI t ht hlt⟩

end Dijkstra

/-! ## `bellman_ford` (`Cost = long long`) -/

section BellmanFord
open Proofs.ListBellmanFordMath

local instance : Cpp.NumericTraits "Cost" Int := Cpp.intNumericTraits "Cost" 64 true

def N : Int := -2 ^ 61

theorem unr_val' : Cpp.ShiftInt.shr (Cpp.NumericTraits.maximum (tag := "Cost") (α := Int)) 2 = U := by decide
theorem neg_val : Cpp.ShiftInt.shr (Cpp.NumericTraits.minimum (tag := "Cost") (α := Int)) 2 = N := by decide

/-- The edge `(from, to, cost)` of an edge value. -/
def tri {E : Type} [Field "from" E Int] [Field "to" E Int] [Field "cost" E Int] (e : E) : Ed :=
  (Field.get (member := "from") e, Field.get (member := "to") e, Field.get (member := "cost") e)

def rowE {E : Type} [Field "from" E Int] [Field "to" E Int] [Field "cost" E Int] (es : Array E) : List Ed :=
  es.toList.map tri

/-- All edges in the scan order of `bellman_ford` (row by row). -/
def allE {E : Type} [Field "from" E Int] [Field "to" E Int] [Field "cost" E Int] (adj : Array (Array E)) :
    List Ed := adj.toList.flatMap rowE

/-- The arrays after both phases. -/
abbrev bfFinal {E : Type} [Field "from" E Int] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E)
    (s : Nat) : Array Int × Array Int :=
  (round2 U N (allE g.adj))^[g.n_.toNat] ((round1 U (allE g.adj))^[g.n_.toNat - 1] (st0 g.n_.toNat s U))

/-- The graph after `bellman_ford(s)`: both arrays cached for `s`. -/
abbrev bfResult {E : Type} [Field "from" E Int] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E)
    (s : Nat) : cp.ListGraph Int E :=
  { g with shortest_path_dist := umapPut g.shortest_path_dist s (bfFinal g s).1,
           shortest_path_parent := umapPut g.shortest_path_parent s (bfFinal g s).2 }

/-- The steps before the first loop. -/
abbrev BB0 {E : Type} (g : cp.ListGraph Int E) : Nat := 3 + g.shortest_path_dist.length + 2 * g.n_.toNat

/-- The steps of one round (both phases): the round, each row, at most 3 per edge. -/
abbrev KB {E : Type} [Field "from" E Int] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E) : Nat :=
  1 + g.adj.size + 3 * (allE g.adj).length

theorem bf_spec {E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int] [Field "cost" E Int]
    (g : cp.ListGraph Int E) (s : Nat) (hnew : umapFind g.shortest_path_dist s = none) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.bellman_ford g s
    ⦃⇓ r c => ⌜r = bfResult g s ∧ c ≤ t0 + BB0 g + (2 * g.n_.toNat) * KB g + 2 + g.shortest_path_dist.length +
      g.shortest_path_parent.length⌝⦄ := by
  mvcgen [cp.ListGraph.bellman_ford, Cpp.umapCount, Cpp.umapSet, cp.ListGraph.UNREACHABLE,
    cp.ListGraph.NEGATIVE_CYCLE]
  case inv1 =>
    exact ⇓⟨xs, st⟩ c => ⌜st = (round1 U (allE g.adj))^[xs.prefix.length] (st0 g.n_.toNat s U) ∧
      c ≤ t0 + BB0 g + xs.prefix.length * KB g⌝
  case inv2 =>
    rename_i xs _ _ _ _ b _ _ c0 _
    exact ⇓⟨ys, st⟩ c => ⌜st = (ys.prefix.flatMap rowE).foldl (step1 U) b ∧
      c ≤ c0 + 1 + ys.prefix.length + 3 * (ys.prefix.flatMap rowE).length⌝
  case inv3 =>
    rename_i row _ _ b _ _ c0 _
    exact ⇓⟨zs, st⟩ c => ⌜st = (zs.prefix.map tri).foldl (step1 U) b ∧ c ≤ c0 + 1 + 3 * zs.prefix.length⌝
  case inv4 =>
    exact ⇓⟨xs, st⟩ c => ⌜st = (round2 U N (allE g.adj))^[xs.prefix.length]
      ((round1 U (allE g.adj))^[g.n_.toNat - 1] (st0 g.n_.toNat s U)) ∧
      c ≤ t0 + BB0 g + (g.n_.toNat - 1) * KB g + xs.prefix.length * KB g⌝
  case inv5 =>
    rename_i xs _ _ _ _ b _ _ c0 _
    exact ⇓⟨ys, st⟩ c => ⌜st = (ys.prefix.flatMap rowE).foldl (step2 U N) b ∧
      c ≤ c0 + 1 + ys.prefix.length + 3 * (ys.prefix.flatMap rowE).length⌝
  case inv6 =>
    rename_i row _ _ b _ _ c0 _
    exact ⇓⟨zs, st⟩ c => ⌜st = (zs.prefix.map tri).foldl (step2 U N) b ∧ c ≤ c0 + 1 + 3 * zs.prefix.length⌝
  case vc2.step.isTrue =>
    rename_i pref cur suff _ b _ _ _ hinv hcond _ _
    simp at hinv ⊢
    obtain ⟨hinv, hc⟩ := hinv
    refine ⟨?_, by omega⟩
    rw [← hinv]
    unfold step1 tri
    rw [unr_val'] at hcond
    rw [if_pos (by simpa +zetaDelta using hcond)]
  case vc3.step.isFalse =>
    rename_i pref cur suff _ b _ _ _ hinv hcond
    simp at hinv ⊢
    obtain ⟨hinv, hc⟩ := hinv
    refine ⟨?_, by omega⟩
    rw [← hinv]
    unfold step1 tri
    rw [unr_val'] at hcond
    rw [if_neg (by simpa +zetaDelta using hcond)]
  case vc11.step.isTrue =>
    rename_i pref cur suff _ b _ _ _ hinv hcond _ _
    simp at hinv ⊢
    obtain ⟨hinv, hc⟩ := hinv
    refine ⟨?_, by omega⟩
    rw [← hinv]
    unfold step2 tri
    rw [unr_val'] at hcond
    rw [if_pos (by simpa +zetaDelta using hcond)]
    simp +zetaDelta [neg_val]
  case vc12.step.isFalse =>
    rename_i pref cur suff _ b _ _ _ hinv hcond
    simp at hinv ⊢
    obtain ⟨hinv, hc⟩ := hinv
    refine ⟨?_, by omega⟩
    rw [← hinv]
    unfold step2 tri
    rw [unr_val'] at hcond
    rw [if_neg (by simpa +zetaDelta using hcond)]
  case vc10.isFalse.pre =>
    simp +zetaDelta [Cpp.replicate, unr_val', BB0]
    omega
  case vc19.isFalse.post.success.pre =>
    rename_i h
    simp +zetaDelta at h ⊢
    obtain ⟨h, hc⟩ := h
    rw [range_length] at h hc
    refine ⟨by rw [h]; congr 1; omega, ?_⟩
    have : (g.n_ - 1 - 0).toNat = g.n_.toNat - 1 := by omega
    rw [this] at hc; omega
  case vc1.isTrue => rename_i h; simp +zetaDelta [hnew] at h
  all_goals (try simp_all +zetaDelta [List.flatMap_append, round1, round2, allE, rowE,
    Function.iterate_succ_apply', unr_val', neg_val])
  all_goals try (
    simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul, List.flatMap_append, List.length_append,
      List.length_cons, List.length_nil, List.length_flatMap] at *
    simp only [KB, allE] at *
    omega)
  case vc8.step.post.success =>
    rename_i h1 h2
    obtain ⟨_, hc1⟩ := h1
    obtain ⟨_, hc2⟩ := h2
    have e1 : (List.map (fun a => a.size) g.adj.toList).sum = (allE g.adj).length := by
      simp [allE, rowE, List.length_flatMap]
    have e2 : g.adj.toList.length = g.adj.size := by simp
    have hK : KB g = 1 + g.adj.size + 3 * (allE g.adj).length := rfl
    rw [Nat.succ_mul]; omega
  case vc17.step.post.success =>
    rename_i h1 h2
    obtain ⟨_, hc1⟩ := h1
    obtain ⟨_, hc2⟩ := h2
    have e1 : (List.map (fun a => a.size) g.adj.toList).sum = (allE g.adj).length := by
      simp [allE, rowE, List.length_flatMap]
    have e2 : g.adj.toList.length = g.adj.size := by simp
    have hK : KB g = 1 + g.adj.size + 3 * (allE g.adj).length := rfl
    rw [Nat.succ_mul]; omega
  case vc20.isFalse.post.success.post.success =>
    rename_i _ h2
    obtain ⟨_, hc⟩ := h2
    simp only [range_length, Int.sub_zero, bfFinal, allE]
    simp
    rw [range_length] at hc
    have hn : (g.n_ - 0).toNat = g.n_.toNat := by omega
    rw [hn] at hc
    have h3 : (g.n_.toNat - 1) * KB g ≤ g.n_.toNat * KB g := Nat.mul_le_mul_right _ (by omega)
    have h4 : 2 * g.n_.toNat * KB g = g.n_.toNat * KB g + g.n_.toNat * KB g := by
      rw [Nat.mul_assoc, Nat.two_mul]
    omega


/-- `bellman_ford(s)` when the distances from `s` are already cached: nothing changes. -/
theorem bellman_ford_cached_spec {E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]
    [Field "cost" E Int] (g : cp.ListGraph Int E) (s : Int) (D : Array Int)
    (hD : umapFind g.shortest_path_dist s = some D) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.bellman_ford g s
    ⦃⇓ r c => ⌜r = g ∧ c = t0 + 2 + g.shortest_path_dist.length⌝⦄ := by
  mvcgen [cp.ListGraph.bellman_ford, Cpp.umapCount]
  case inv1 => exact ⇓ _ => ⌜False⌝
  case inv2 => exact ⇓ _ => ⌜False⌝
  case inv3 => exact ⇓ _ => ⌜False⌝
  case inv4 => exact ⇓ _ => ⌜False⌝
  case inv5 => exact ⇓ _ => ⌜False⌝
  case inv6 => exact ⇓ _ => ⌜False⌝
  all_goals simp_all +zetaDelta
  all_goals omega

/-- The meaning of the cached arrays `bfFinal g s` (`ListBellmanFordMath.bf_correct` with the edges of `g` in
scan order): unreachable vertices get `UNREACHABLE`, vertices that a negative cycle reaches get `NEGATIVE_CYCLE`,
the others the least walk cost, and their parents give such a walk. -/
theorem bellman_ford_correct {E : Type} [Field "from" E Int] [Field "to" E Int] [Field "cost" E Int]
    (g : cp.ListGraph Int E) (s : Nat) (C : Int) (hV : Valid g.n_.toNat C (allE g.adj)) (hs : s < g.n_.toNat)
    (hC : 0 ≤ C) (hU : (g.n_.toNat : Int) * C < U) (hNU : N + C < U)
    (hNEG : N + C < -(((1 + (g.n_.toNat - 1) * (allE g.adj).length : Nat) : Int) * C))
    (v : Nat) (hv : v < g.n_.toNat) :
    ((¬ ∃ w k, Walk (allE g.adj) s v w k) → (bfFinal g s).1[v]! = U) ∧
    (NegReach (allE g.adj) s v → (bfFinal g s).1[v]! = N) ∧
    ((∃ w k, Walk (allE g.adj) s v w k) → ¬ NegReach (allE g.adj) s v →
      (bfFinal g s).1[v]! < U ∧ (∀ w k, Walk (allE g.adj) s v w k → (bfFinal g s).1[v]! ≤ w) ∧
      ∃ Cl, Chain (bfFinal g s).2 v Cl ∧ WalkB (allE g.adj) s Cl (bfFinal g s).1[v]!) :=
  bf_correct hV hs hC hU hNU hNEG v hv

end BellmanFord

end Proofs.Cpp.GraphList
