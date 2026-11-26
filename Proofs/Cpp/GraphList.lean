import Proofs.Cpp.Gen.GraphList
import Proofs.Cpp.ListFindCycleForest
import Proofs.Cpp.ListTopologicalProof
import Proofs.Cpp.GraphListEdge
import Proofs.Cpp.Lib.Basic
import Proofs.Math.ParentChain
import Proofs.Math.ListDijkstraMath
import Proofs.Math.ListBellmanFordMath
import Proofs.Math.ListPrimMath
import Proofs.Cpp.ListLowlinkCorrect

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

/-! ## `prim` (`Cost = long long`) -/

section Prim
open Proofs.ListPrimMath
open Proofs.DijkstraOldExec (doneOf)

local instance : Cpp.NumericTraits "Cost" Int := Cpp.intNumericTraits "Cost" 64 true

/-- The pair `(to, cost)` of an edge value. -/
def pairOf {E : Type} [Field "to" E Int] [Field "cost" E Int] (e : E) : Int × Int :=
  (Field.get (member := "to") e, Field.get (member := "cost") e)

def outP {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (adj : Array (Array E)) (v : Nat) :
    List (Int × Int) := (adj[v]!).toList.map pairOf

abbrev RP {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E) : Nat :=
  restU (outP g.adj) (Array.replicate g.n_.toNat false) g.n_.toNat

abbrev KP {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E) : Nat :=
  Nat.log2 (2 * RP g + 2) + 3

/-- The invariant of the loop of `prim_span` started at `i` from the picks `D`. -/
def SCont {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E)
    (U : Int) (i : Nat) (D : List Nat) (B : Nat) (st : Int × Array Int × Array Bool × List (Int × Int)) (c : Nat) :
    Prop :=
  ∃ D' cs', (SpanA g.n_.toNat U (outP g.adj) D' cs' st.2.1 st.2.2.1 st.2.2.2 ∨
      SpanB g.n_.toNat U (outP g.adj) D' cs' st.2.1 st.2.2.1 st.2.2.2 i) ∧ st.1 = cs'.sum ∧
    (i ∈ D' ∨ SpanB g.n_.toNat U (outP g.adj) D' cs' st.2.1 st.2.2.1 st.2.2.2 i) ∧ (∀ y ∈ D, y ∈ D') ∧
    st.2.2.1.size = g.n_.toNat ∧
    2 * restU (outP g.adj) st.2.2.1 g.n_.toNat + st.2.2.2.length ≤ 2 * RP g + 1 ∧
    c + KP g * (2 * restU (outP g.adj) st.2.2.1 g.n_.toNat + st.2.2.2.length) ≤ B

theorem span_spec {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int]
    (g : cp.ListGraph Int E) (U : Int) (hU : 0 ≤ U) (hV : ValidP g.n_.toNat U (outP g.adj))
    (hsmall : 2 * RP g + 1 < 2 ^ 64) (i : Int) (hi0 : 0 ≤ i) (hin : i.toNat < g.n_.toNat)
    (D : List Nat) (cs : List Int) (mst : Int) (dist : Array Int) (used : Array Bool)
    (hA : SpanA g.n_.toNat U (outP g.adj) D cs dist used []) (hiD : i.toNat ∉ D) (hmst : mst = cs.sum)
    (hR : restU (outP g.adj) used g.n_.toNat ≤ RP g) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.prim_span g i mst dist used
    ⦃⇓ r c => ⌜(∃ D' cs', SpanA g.n_.toNat U (outP g.adj) D' cs' r.2.1 r.2.2 [] ∧ r.1 = cs'.sum ∧
        i.toNat ∈ D' ∧ (∀ y ∈ D, y ∈ D')) ∧
      (∀ y < g.n_.toNat, used[y]! = true → r.2.2[y]! = true) ∧
      c + KP g * (2 * restU (outP g.adj) r.2.2 g.n_.toNat) ≤
        t0 + 3 + KP g * (2 * restU (outP g.adj) used g.n_.toNat + 1)⌝⦄ := by
  mvcgen [cp.ListGraph.prim_span, Cpp.pqPush, Cpp.pqTop, Cpp.pqPop]
  case vc1.inv =>
    exact ⟨fun st c => ⌜SCont g U i.toNat D (t0 + 2 + KP g * (2 * restU (outP g.adj) used g.n_.toNat + 1)) st c⌝,
      fun st c => ⌜st.2.2.2 = [] ∧
        SCont g U i.toNat D (t0 + 3 + KP g * (2 * restU (outP g.adj) used g.n_.toNat + 1)) st c⌝,
      fun st => 2 * restU (outP g.adj) st.2.2.1 g.n_.toNat + st.2.2.2.length⟩
  case inv1 =>
    rename_i b _ _ _ _ _ _ c0 _ _ x _ _ _ _ _ _
    exact ⇓⟨xs, st⟩ c => ⌜st = (xs.prefix.map pairOf).foldl (astep (Cpp.set b.2.2.1 x.2 true))
      (b.2.1, b.2.2.2.eraseIdx (pqBestIdx G b.2.2.2)) ∧
      (b.2.2.2.eraseIdx (pqBestIdx G b.2.2.2)).length + (Cpp.get g.adj x.2).size + 1 ≤ 2 * RP g + 2 ∧
      c0 ≤ c ∧ c ≤ c0 + KP g * (xs.prefix.length + 1)⌝
  case vc3.step.isFalse.h_1.isTrue => simp_all
  case vc9.step.isFalse.h_1.isFalse.isFalse.post.except => simp
  case vc10.step.isFalse.h_2 =>
    rename_i b _ _ _ _ _ _ _ _ hne hnone
    have hne' : b.2.2.2 ≠ [] := by intro e; simp +zetaDelta [e] at hne
    obtain ⟨y, _, h2, _⟩ := pqBest_spec G G_irr G_trans b.2.2.2 hne'
    have : pqBest G b.2.2.2 = none := hnone
    rw [this] at h2; cases h2
  case vc5.step.isTrue =>
    rename_i pref cur suff hsplit st _ _ c hinv hcond _
    simp at hinv
    obtain ⟨heq, hlenQ, hc0, hc⟩ := hinv
    refine ⟨?_, by omega, by simp +zetaDelta; omega, ?_⟩
    · rw [List.map_append, List.foldl_append, ← heq]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      unfold astep pairOf
      rw [if_pos (by simpa +zetaDelta using hcond)]
    · have hpl := congrArg List.length hsplit
      simp +zetaDelta at hpl
      have hq : ∀ (u : Array Bool) (st0 : Array Int × List (Int × Int)), st = (pref.map pairOf).foldl (astep u) st0 →
          st.2.length ≤ st0.2.length + (pref.map pairOf).length := by
        intro u st0 h; rw [h]; exact fold_astep_len u _ st0
      have hq := hq _ _ heq
      simp only [List.length_map] at hq
      have := log_bound (a := st.2.length + 1) (b := 2 * RP g + 2) (by simp +zetaDelta at hq hlenQ hpl ⊢; omega)
      simp +zetaDelta; unfold KP at hc ⊢; rw [Nat.mul_succ]; omega
  case vc6.step.isFalse =>
    rename_i pref cur suff hsplit st _ _ c hinv hcond
    simp at hinv
    obtain ⟨heq, hlenQ, hc0, hc⟩ := hinv
    refine ⟨?_, by omega, by (try simp +zetaDelta); omega, ?_⟩
    · rw [List.map_append, List.foldl_append, ← heq]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      unfold astep pairOf
      rw [if_neg (by simpa +zetaDelta using hcond)]
    · simp +zetaDelta; unfold KP at hc ⊢; rw [Nat.mul_succ]; omega
  case vc11.pre =>
    obtain ⟨hS, hI, hQI⟩ := hA
    have hiN : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg hi0
    have hl1 : Nat.log2 1 = 0 := by decide
    have hset : (Cpp.set dist i 0).toList = dist.toList.set i.toNat 0 := by
      rw [← hiN]; simp only [Int.toNat_natCast]; exact toList_set dist _ 0 (by rw [hS.1]; exact hin)
    have hB : SpanB g.n_.toNat U (outP g.adj) D cs (Cpp.set dist i 0) used [(0, i)] i.toNat := by
      refine ⟨⟨by simp [hS.1], hS.2.1, hS.2.2⟩, dist.toList, hI, hset, hiD, hin, fun x hx hxD => ?_, by rw [hiN]⟩
      rw [getD_toList]
      by_contra h
      have := hQI.2 x hx hxD (by omega)
      simp at this
    refine ⟨⟨D, cs, Or.inr hB, by simp +zetaDelta [hmst], Or.inr hB, fun y hy => hy, hS.2.1, ?_, ?_⟩, ?_⟩
    · simp +zetaDelta; omega
    · simp +zetaDelta [hl1]; omega
    · simp +zetaDelta [fuel]; omega
  case vc12.post.success =>
    rename_i r _ _ _ _ _ _ c h
    obtain ⟨hemp, D', cs', hAB, hmst', hiD', hsub, _, _, hc⟩ := h
    rcases hAB with hA' | hB'
    · rcases hiD' with hiD' | hB''
      · refine ⟨⟨D', cs', by rw [← hemp]; exact hA', hmst', hiD', hsub⟩, ?_, ?_⟩
        · intro y hy hu
          have h1 := hA.1.2.2 y hy; rw [h1] at hu
          have h2 := hA'.1.2.2 y hy
          simp +zetaDelta at h2 ⊢; rw [h2]; simpa using hsub y (by simpa using hu)
        · simp +zetaDelta at hc ⊢; rw [hemp] at hc; simpa using hc
      · obtain ⟨_, _, _, _, _, _, _, hQ⟩ := hB''; rw [hemp] at hQ; simp at hQ
    · obtain ⟨_, _, _, _, _, _, _, hQ⟩ := hB'; rw [hemp] at hQ; simp at hQ
  case vc2.step.isTrue =>
    rename_i b _ _ _ _ _ _ c hC hemp
    obtain ⟨D', cs', h1, h2, h3, h4, h5, h6, h7⟩ := hC
    exact ⟨by simpa +zetaDelta using hemp, D', cs', h1, h2, h3, h4, h5, h6, by simp +zetaDelta; omega⟩
  case vc4.step.isFalse.h_1.isFalse.isTrue =>
    rename_i b _ _ _ _ _ _ c hC _ x hx0 _ _ hst
    have hx : pqBest G b.2.2.2 = some x := hx0
    obtain ⟨hperm, hmin⟩ := top_pop _ _ hx
    obtain ⟨D', cs', hAB, hmst', hiD', hsub, hsz, hbound, hcost⟩ := hC
    -- in state B the pop is the root, which is not stale
    have hnotB : ¬ SpanB g.n_.toNat U (outP g.adj) D' cs' b.2.1 b.2.2.1 b.2.2.2 i.toNat := by
      intro hB
      obtain ⟨hQ, hd0, hu0, _⟩ := freshB hV hU hB
      rw [hQ] at hx
      have : x = (0, ((i.toNat : Nat) : Int)) := by
        simp [pqBest, pqBestIdx] at hx; rw [← hx]; congr 1; omega
      subst this
      simp only [Int.natCast_toNat_eq_self.mpr hi0] at hd0 hu0
      simp +zetaDelta [Int.natCast_toNat_eq_self.mpr hi0, hd0, hu0] at hst
    have hA : SpanA g.n_.toNat U (outP g.adj) D' cs' b.2.1 b.2.2.1 b.2.2.2 := by
      rcases hAB with h | h
      · exact h
      · exact absurd h hnotB
    obtain ⟨hS, hI, hQI⟩ := hA
    have hQI' := qi_stale hS hQI hperm (by simpa +zetaDelta using hst)
    have hlq := hperm.length_eq; simp at hlq
    have := log_bound (a := b.2.2.2.length) (b := 2 * RP g + 2) (by omega)
    have hK : KP g = Nat.log2 (2 * RP g + 2) + 3 := rfl
    have hKm : KP g * (2 * restU (outP g.adj) b.2.2.1 g.n_.toNat + (b.2.2.2.eraseIdx (pqBestIdx G b.2.2.2)).length)
        + KP g = KP g * (2 * restU (outP g.adj) b.2.2.1 g.n_.toNat + b.2.2.2.length) := by
      rw [← Nat.mul_succ]; congr 1; omega
    refine ⟨⟨D', cs', Or.inl ⟨hS, hI, hQI'⟩, by simpa +zetaDelta using hmst', ?_, hsub, hsz, ?_, ?_⟩, ?_⟩
    · rcases hiD' with h | h
      · exact Or.inl h
      · exact absurd h hnotB
    · simp +zetaDelta; unfold G at *; omega
    · simp +zetaDelta; unfold G at hKm; omega
    · simp +zetaDelta; unfold G at *; omega
  case vc7.step.isFalse.h_1.isFalse.isFalse.pre =>
    rename_i b _ _ _ _ _ _ c hC _ x hx0 _ _ hst _ _
    have hx : pqBest G b.2.2.2 = some x := hx0
    obtain ⟨hperm, _⟩ := top_pop _ _ hx
    obtain ⟨D', cs', hAB, _, _, _, hsz, hbound, _⟩ := hC
    have hlq := hperm.length_eq; simp at hlq
    simp +zetaDelta [get_eq] at hst
    have hx0' : 0 ≤ x.2 := by
      rcases hAB with ⟨_, _, hQI⟩ | ⟨_, Dd0, _, _, _, _, _, hQ⟩
      · exact (hQI.1 x (hperm.mem_iff.mpr List.mem_cons_self)).1
      · rw [hQ] at hx; simp [pqBest, pqBestIdx] at hx; rw [← hx]; simp
    have hxn : x.2.toNat < g.n_.toNat := by
      rcases hAB with ⟨_, _, hQI⟩ | ⟨_, Dd0, _, _, _, hin', _, hQ⟩
      · have := (hQI.1 x (hperm.mem_iff.mpr List.mem_cons_self)).2.1; omega
      · rw [hQ] at hx; simp [pqBest, pqBestIdx] at hx; rw [← hx]; simpa using hin'
    have hr := restU_ge (outP g.adj) b.2.2.1 x.2.toNat g.n_.toNat hxn hst.1
    have hdeg : (outP g.adj x.2.toNat).length = (Cpp.get g.adj x.2).size := by simp [outP, get_eq]
    have := log_bound (a := b.2.2.2.length) (b := 2 * RP g + 2) (by omega)
    refine ⟨by simp +zetaDelta, by simp +zetaDelta; unfold G at *; omega, by simp +zetaDelta; omega, ?_⟩
    simp +zetaDelta; unfold KP; omega
  case vc8.step.isFalse.h_1.isFalse.isFalse.post.success =>
    rename_i b _ _ _ _ _ _ c hC _ x hx0 _ _ hst _ _ r _ _ c' hinv
    have hx : pqBest G b.2.2.2 = some x := hx0
    obtain ⟨hperm, hmin⟩ := top_pop _ _ hx
    obtain ⟨D', cs', hAB, hmst', hiD', hsub, hsz, hbound, hcost⟩ := hC
    simp at hinv
    obtain ⟨heq, _, _, hc'⟩ := hinv
    have hlq := hperm.length_eq; simp at hlq
    have hKm : ∀ a b : Nat, a ≤ b → KP g * a ≤ KP g * b := fun a b h => Nat.mul_le_mul_left _ h
    have hout : ∀ v : Nat, x.2 = (v : Int) → (Cpp.get g.adj x.2).toList.map pairOf = outP g.adj v := by
      intro v hv; rw [hv]; simp [outP, get_eq]
    obtain ⟨v, k, D'', cs'', hv, hk, hvn, hvu, hA'', hcs, hi'', hsub'', hlen⟩ :
        ∃ (v : Nat) (k : Int) (D'' : List Nat) (cs'' : List Int), x.2 = (v : Int) ∧ Cpp.get b.2.1 x.2 = k ∧
          v < g.n_.toNat ∧ b.2.2.1[v]! = false ∧
          SpanA g.n_.toNat U (outP g.adj) D'' cs'' r.1 (Cpp.set b.2.2.1 x.2 true) r.2 ∧
          cs'' = cs' ++ [k] ∧ i.toNat ∈ D'' ∧ (∀ y ∈ D', y ∈ D'') ∧
          r.2.length ≤ (b.2.2.2.eraseIdx (pqBestIdx G b.2.2.2)).length + (outP g.adj v).length := by
      by_cases hB : SpanB g.n_.toNat U (outP g.adj) D' cs' b.2.1 b.2.2.1 b.2.2.2 i.toNat
      · obtain ⟨hQ, hd0, hu0, hA2, hlen2, hin2, hiD2⟩ := freshB hV hU hB
        have hxe : x = (0, ((i.toNat : Nat) : Int)) := by
          rw [hQ] at hx; simp [pqBest, pqBestIdx] at hx; rw [← hx]; congr 1; omega
        have hQ' : b.2.2.2.eraseIdx (pqBestIdx G b.2.2.2) = [] := by rw [hQ]; simp [pqBestIdx]
        have hr : r = (outP g.adj i.toNat).foldl (astep (Cpp.set b.2.2.1 ((i.toNat : Nat) : Int) true)) (b.2.1, []) := by
          rw [heq, hQ', hout i.toNat (by rw [hxe])]; simp +zetaDelta [hxe]
        refine ⟨i.toNat, 0, D' ++ [i.toNat], cs' ++ [0], by rw [hxe], by rw [hxe]; exact hd0, hin2, ?_, ?_, rfl,
          by simp, fun y hy => by simp [hy], ?_⟩
        · have := hB.1.2.2 i.toNat hin2; rw [this]; simp [hiD2]
        · rw [hr, hxe]; exact hA2
        · rw [hr, hQ']; simpa using hlen2
      · have hA : SpanA g.n_.toNat U (outP g.adj) D' cs' b.2.1 b.2.2.1 b.2.2.2 := by
          rcases hAB with h | h
          · exact h
          · exact absurd h hB
        obtain ⟨hk, hA2, hlen2, hvn2, hvD2⟩ := freshA hV hU hA hperm hmin (by simpa +zetaDelta using hst)
        have hx0' : 0 ≤ x.2 := (hA.2.2.1 x (hperm.mem_iff.mpr List.mem_cons_self)).1
        have hvi : x.2 = ((x.2.toNat : Nat) : Int) := (Int.toNat_of_nonneg hx0').symm
        have hr : r = (outP g.adj x.2.toNat).foldl (astep (Cpp.set b.2.2.1 ((x.2.toNat : Nat) : Int) true))
            (b.2.1, b.2.2.2.eraseIdx (pqBestIdx G b.2.2.2)) := by
          rw [heq, hout x.2.toNat hvi, ← hvi]
        refine ⟨x.2.toNat, x.1, D' ++ [x.2.toNat], cs' ++ [x.1], hvi, hk, hvn2, ?_, ?_, rfl, ?_, ?_, ?_⟩
        · have := hA.1.2.2 x.2.toNat hvn2; rw [this]; simp [hvD2]
        · rw [hr, ← hvi]; rw [← hvi] at hA2; exact hA2
        · rcases hiD' with h | h
          · simp [h]
          · exact absurd h hB
        · intro y hy; simp [hy]
        · rw [hr]; exact hlen2
    have hdeg : (Cpp.get g.adj x.2).size = (outP g.adj v).length := by
      rw [← hout v hv]; simp
    have hrs := restU_set (outP g.adj) b.2.2.1 v (by omega) hvu g.n_.toNat
    rw [if_pos hvn, ← hv] at hrs
    have hsz' : (Cpp.set b.2.2.1 x.2 true).size = g.n_.toNat := by simp [hsz]
    have hA2 : 2 * restU (outP g.adj) (Cpp.set b.2.2.1 x.2 true) g.n_.toNat + r.2.length +
        ((outP g.adj v).length + 1) ≤ 2 * restU (outP g.adj) b.2.2.1 g.n_.toNat + b.2.2.2.length := by omega
    have := hKm _ _ hA2
    rw [Nat.mul_add] at this
    rw [hdeg] at hc'
    refine ⟨⟨D'', cs'', Or.inl hA'', ?_, Or.inl hi'', fun y hy => hsub'' y (hsub y hy), hsz',
      by simp +zetaDelta; omega, ?_⟩, by simp +zetaDelta; omega⟩
    · simp +zetaDelta; rw [hcs, List.sum_append, ← hmst', ← hk, hv]; simp
    · simp +zetaDelta; omega


/-- `prim_span` as a step for `mvcgen`. -/
@[spec] theorem span_wp {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int]
    (g : cp.ListGraph Int E) (hV : ValidP g.n_.toNat Proofs.Cpp.GraphList.U (outP g.adj))
    (hsmall : 2 * RP g + 1 < 2 ^ 64) (i : Int) (hi0 : 0 ≤ i) (hin : i.toNat < g.n_.toNat)
    (mst : Int) (dist : Array Int) (used : Array Bool)
    (hPre : ∃ D cs, SpanA g.n_.toNat Proofs.Cpp.GraphList.U (outP g.adj) D cs dist used [] ∧ i.toNat ∉ D ∧ mst = cs.sum)
    (hR : restU (outP g.adj) used g.n_.toNat ≤ RP g) {Q : PostCond (Int × Array Int × Array Bool) PS} :
    ⦃fun t => ⌜∀ r c, ((∃ D' cs', SpanA g.n_.toNat Proofs.Cpp.GraphList.U (outP g.adj) D' cs' r.2.1 r.2.2 [] ∧ r.1 = cs'.sum ∧
        i.toNat ∈ D') ∧ (∀ y < g.n_.toNat, used[y]! = true → r.2.2[y]! = true) ∧
      c + KP g * (2 * restU (outP g.adj) r.2.2 g.n_.toNat) ≤
        t + 3 + KP g * (2 * restU (outP g.adj) used g.n_.toNat + 1)) → (Q.1 r c).down⌝⦄
      cp.ListGraph.prim_span g i mst dist used ⦃Q⦄ := by
  obtain ⟨D, cs, hA, hiD, hmst⟩ := hPre
  apply Triple.iff.mpr
  intro t ht
  obtain ⟨r, c, hx, ⟨⟨D', cs', h1, h2, h3, _⟩, h4, h5⟩⟩ :=
    run_of_triple (span_spec g Proofs.Cpp.GraphList.U (by decide) hV hsmall i hi0 hin D cs mst dist used hA hiD hmst hR t)
  simp [wp, hx]
  exact ht r c ⟨⟨D', cs', h1, h2, h3⟩, h4, h5⟩




open Proofs.PrimBridge (IsMSF toArc prim_msf)

/-- The outer loop of `prim` after the first `j` vertices: every one of them is picked. -/
def OInv {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int] (g : cp.ListGraph Int E) (t0 j : Nat)
    (st : Int × Array Int × Array Bool) (c : Nat) : Prop :=
  (∃ D cs, SpanA g.n_.toNat Proofs.Cpp.GraphList.U (outP g.adj) D cs st.2.1 st.2.2 [] ∧ st.1 = cs.sum) ∧
    (∀ y < j, st.2.2[y]! = true) ∧
    c + KP g * (2 * restU (outP g.adj) st.2.2 g.n_.toNat) ≤ t0 + 2 + 2 * g.n_.toNat + KP g * (2 * RP g) + j * (KP g + 4)

theorem len_of_all {n : Nat} {D : List Nat} (hnd : D.Nodup) (hlt : ∀ v ∈ D, v < n) (hall : ∀ j < n, j ∈ D) :
    D.length = n := by
  have h1 : D.length ≤ n := by
    have := (List.Nodup.subperm hnd (l₂ := List.range n) (fun x hx => List.mem_range.mpr (hlt x hx))).length_le
    simpa using this
  have h2 : n ≤ D.length := by
    have := (List.Nodup.subperm (List.nodup_range) (l₂ := D) (fun x hx => hall x (List.mem_range.mp hx))).length_le
    simpa using this
  omega

theorem prim_spec {E : Type} [Inhabited E] [Field "to" E Int] [Field "cost" E Int]
    (g : cp.ListGraph Int E) (hV : ValidP g.n_.toNat Proofs.Cpp.GraphList.U (outP g.adj)) (hsmall : 2 * RP g + 1 < 2 ^ 64)
    (hsym : ∀ e ∈ EdOf g.n_.toNat (outP g.adj), (e.2.1, e.1, e.2.2) ∈ EdOf g.n_.toNat (outP g.adj)) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.prim g
    ⦃⇓ r c => ⌜r.2 = g ∧ 0 ≤ r.1 ∧
      IsMSF g.n_.toNat Proofs.Cpp.GraphList.U.toNat ((EdOf g.n_.toNat (outP g.adj)).map toArc) r.1.toNat ∧
      c ≤ t0 + 2 + 2 * g.n_.toNat + KP g * (2 * RP g) + g.n_.toNat * (KP g + 4)⌝⦄ := by
  have hg : ∀ (h : cp.ListGraph Int E),
      (⟨h.n_, h.m_, h.adj, h.shortest_path_dist, h.shortest_path_parent⟩ : cp.ListGraph Int E) = h :=
    fun h => rfl
  mvcgen [cp.ListGraph.prim, unr_spec]
  case inv1 => exact ⇓⟨xs, st⟩ c => ⌜OInv g t0 xs.prefix.length st c⌝
  case vc3.hi0 =>
    rename_i pref cur suff hsplit _ _ _ _ _ _ _ _
    have := range_cursor hsplit; omega
  case vc4.hin =>
    rename_i pref cur suff hsplit _ _ _ _ _ _ _ _
    have h1 := range_cursor hsplit; have h2 := range_prefix_length hsplit; simp +zetaDelta; omega
  case vc5.hPre =>
    rename_i pref cur suff hsplit b _ _ _ _ c hinv hcond
    obtain ⟨⟨D, cs, hA, hmst⟩, _, _⟩ := hinv
    have h1 := range_cursor hsplit; have h2 := range_prefix_length hsplit
    refine ⟨D, cs, by simpa +zetaDelta using hA, fun h => ?_, by simpa +zetaDelta using hmst⟩
    have := hA.1.2.2 cur.toNat (by simp +zetaDelta at h2 ⊢; omega)
    simp +zetaDelta [get_eq] at hcond
    rw [this] at hcond; simp [h] at hcond
  case vc6.hR =>
    rename_i pref cur suff hsplit b _ _ _ _ c hinv _
    obtain ⟨⟨D, cs, hA, _⟩, _, _⟩ := hinv
    have := restU_le (outP g.adj) b.2.2 g.n_.toNat
    rw [hA.1.2.1] at this
    simpa +zetaDelta using this
  case vc7.step.isTrue =>
    rename_i pref cur suff hsplit b _ _ _ _ c hinv hcond
    intro r c' ⟨D', cs', hA', hmst', hi'⟩ hmono hcost
    obtain ⟨_, hpre, hc⟩ := hinv
    have h1 := range_cursor hsplit; have h2 := range_prefix_length hsplit
    simp +zetaDelta only at hcost
    rw [hg] at hcost
    try simp
    refine ⟨⟨D', cs', hA', hmst'⟩, fun y hy => ?_, ?_⟩
    · try simp at hy
      by_cases e : y < pref.length
      · exact hmono y (by simp +zetaDelta at h2; omega) (by simpa +zetaDelta using hpre y e)
      · have hy' : y = cur.toNat := by omega
        rw [hy', hA'.1.2.2 cur.toNat (by simp +zetaDelta at h2; omega)]; simp [hi']
    · have e : (pref ++ [cur]).length * (KP g + 4) = pref.length * (KP g + 4) + (KP g + 4) := by
        rw [List.length_append, List.length_singleton, Nat.succ_mul]
      have e1 : KP g * (2 * restU (outP g.adj) b.2.2 g.n_.toNat + 1) =
          KP g * (2 * restU (outP g.adj) b.2.2 g.n_.toNat) + KP g := by rw [Nat.mul_add, Nat.mul_one]
      have e2 : (pref ++ [cur]).length * (KP g + 4) = pref.length * (KP g + 4) + (KP g + 4) := by
        rw [List.length_append, List.length_singleton, Nat.succ_mul]
      have e3 : (pref.length + 1) * (KP g + 4) = pref.length * (KP g + 4) + (KP g + 4) := Nat.succ_mul _ _
      dsimp only at hc hcost ⊢
      try simp +zetaDelta only at hcost ⊢
      omega
  case vc8.step.isFalse =>
    rename_i pref cur suff hsplit b _ _ _ _ c hinv hcond
    obtain ⟨hA, hpre, hc⟩ := hinv
    have h1 := range_cursor hsplit; have h2 := range_prefix_length hsplit
    refine ⟨hA, fun y hy => ?_, ?_⟩
    · try simp at hy
      by_cases e : y < pref.length
      · exact hpre y e
      · have hy' : y = cur.toNat := by omega
        rw [hy']; simp +zetaDelta [get_eq] at hcond; exact hcond
    · have e : (pref ++ [cur]).length * (KP g + 4) = pref.length * (KP g + 4) + (KP g + 4) := by
        rw [List.length_append, List.length_singleton, Nat.succ_mul]
      dsimp only at hc ⊢; rw [e]; simp +zetaDelta only at hc ⊢; omega
  case vc9.pre =>
    rename_i hs0
    have hU0 : (0 : Int) ≤ Proofs.Cpp.GraphList.U := by decide
    refine ⟨⟨[], [], ⟨⟨by simp +zetaDelta [Cpp.replicate], by simp +zetaDelta [Cpp.replicate], fun x hx => by simp +zetaDelta [Cpp.replicate, hx]⟩,
      ?_, fun q hq => by simp at hq, fun x hx _ h => by simp +zetaDelta [Cpp.replicate, hx] at h⟩, rfl⟩,
      fun y hy => by simp at hy, ?_⟩
    · have := Proofs.PrimStep.PInv_init g.n_.toNat Proofs.Cpp.GraphList.U (EdOf g.n_.toNat (outP g.adj))
        (Array.replicate g.n_.toNat Proofs.Cpp.GraphList.U).toList (by simp) (fun j hj => by simp [List.getD_eq_getElem?_getD, hj]) hU0
      simpa +zetaDelta [Cpp.replicate, Proofs.Cpp.GraphList.U] using this
    · simp +zetaDelta [Cpp.replicate]; omega
  case vc10.post.success =>
    rename_i r _ c hinv
    obtain ⟨⟨D, cs, hA, hmst⟩, hall, hc⟩ := hinv
    obtain ⟨hS, hI, _⟩ := hA
    rw [range_length] at hall hc
    have hn : (g.n_ - 0).toNat = g.n_.toNat := by omega
    rw [hn] at hall hc
    have hD : ∀ j < g.n_.toNat, j ∈ D := by
      intro j hj; have := hall j hj; rw [hS.2.2 j hj] at this; simpa using this
    have hlen := len_of_all hI.nodup hI.lt hD
    have hpk : ∀ x ∈ cs, 0 ≤ x := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hjD : j < D.length := by rw [← hI.len]; exact hj
      have h1 := hI.cl3 j hjD
      have h2 := (hI.bnd D[j] (hI.lt D[j] (List.getElem_mem hjD))).1
      rw [h1] at h2; simpa [List.getD_eq_getElem?_getD, hj] using h2
    obtain ⟨hmsf, hsum⟩ := prim_msf (Cm := Proofs.Cpp.GraphList.U) hI hlen (by decide) (fun e he => by
      obtain ⟨h1, p, hp, he'⟩ := mem_EdOf.mp he
      obtain ⟨a1, a2, a3, a4⟩ := hV _ h1 p hp
      rw [he']; exact ⟨h1, by simp; omega, a3, le_of_lt a4⟩) hsym hpk
    have hsum0 : ∀ l : List Int, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => intro h; simp; have := h a (by simp); have := ih (fun x hx => h x (by simp [hx])); omega
    have hr1 : 0 ≤ r.1 := by rw [hmst]; exact hsum0 cs hpk
    refine ⟨by simp +zetaDelta, hr1, ?_, ?_⟩
    · have : r.1.toNat = (cs.map Int.toNat).sum := by rw [hmst, ← hsum]; simp
      rw [this]; exact hmsf
    · omega
  case vc11.post.except => simp

end Prim

end Proofs.Cpp.GraphList

namespace Proofs.Cpp.GraphList

open Proofs.Cpp.ListLowlink Proofs.LowlinkInv Proofs.LowlinkMultigraph

/-- The live C++ data are three vertex arrays, the two output buffers, and one constant-size frame
per active vertex. This counts model slots and frames, with no accounting for object lifetime. -/
theorem lowlink_workspace_slots {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n : Nat} {st : St} {state : DfsState}
    (I : MInv n (rowHeads adj n) (rowEnds adj n) st)
    (A : VisitArrays n st state) (hp : state.points.size ≤ n) (hb : state.bridges.size ≤ n) :
    state.seen.size + state.order.size + state.low.size + state.points.size + state.bridges.size + st.sp ≤
      6 * n := by
  have hs := Nat.le_trans I.sp_le I.vis_len_le
  rw [A.seenSize, A.orderSize, A.lowSize]
  omega

/-- Complete result and work contract for the translated original API. -/
theorem lowlink_spec {Cost E : Type} [Inhabited E] [Field "to" E Int] (g : cp.ListGraph Cost E)
    (edges : List Edge) (H : RowsRepresent edges g.n_.toNat (listTargets g.adj))
    (valid : Valid g.adj g.n_.toNat) (hsmall : g.n_.toNat ≤ Cpp.fuel) (t0 : Nat) :
    let n := g.n_.toNat
    let m := arcCount g.adj n
    let k := min n m
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.lowlink g
    ⦃⇓ r c => ⌜r.2 = g ∧ ExactResults edges n r.1.1 r.1.2 ∧
      r.1.1.size ≤ k ∧ r.1.2.size ≤ k ∧ c ≤ t0 + 1 + 6 * n + 2 * m + 2 * sortCost k⌝⦄ := by
  obtain ⟨r, c, run, same, result⟩ := run_of_triple (lowlink_correct g edges H valid hsmall t0)
  obtain ⟨r', c', run', _, points, bridges, work⟩ := run_of_triple (lowlink_work g hsmall valid t0)
  have he := Option.some.inj (run.symm.trans run')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact triple_of_run r c run ⟨same, result, points, bridges, work⟩

end Proofs.Cpp.GraphList

namespace Proofs.Cpp.GraphList

open Proofs.Cpp.ListFindCycle

theorem find_cycle_directed_spec {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]
    [ConstructState E] [Construct E (Int × Int × Unit)]
    (g : cp.ListGraph Cost E) (valid : ValidGraph g) (hsmall : g.adj.size < Cpp.fuel)
    (st st' : ConstructState.State E) (sentinel : E) (t0 tc : Nat)
    (constructorRun : (Construct.make (E := E) ((-1 : Int), (-1 : Int), ()) st).run
      (t0 + 1 + g.n_.toNat) = some ((sentinel, st'), tc)) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.find_cycle_directed g st
    ⦃⇓ r c => ⌜r.2.1 = st' ∧ r.2.2 = g ∧
      (r.1.size = 0 ∧ Acyclic g ∨ CycleWitness g r.1.toList) ∧
      r.1.size ≤ g.adj.size ∧ c ≤ tc + 9 * g.adj.size + 2 * arcCount g + 5⌝⦄ := by
  obtain ⟨cycle, t', run, result, length, work⟩ :=
    directed_cycle_spec g valid hsmall st st' sentinel t0 tc constructorRun
  exact triple_of_run (cycle, st', g) t' run ⟨rfl, rfl, result, length, work⟩

theorem find_cycle_directed_default_spec {T : Type} [One T] [Inhabited T]
    (g : cp.ListGraph T (cp.Edge T)) (valid : ValidGraph g) (hsmall : g.adj.size < Cpp.fuel)
    (st : cp.GlobalState_0b9f55bc762329ec T "Edge") (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.find_cycle_directed g st
    ⦃⇓ r c => ⌜r.2.1.Edge_next_id = st.Edge_next_id + 1 ∧ r.2.2 = g ∧
      (r.1.size = 0 ∧ Acyclic g ∨ CycleWitness g r.1.toList) ∧
      r.1.size ≤ g.adj.size ∧ c ≤ t0 + 10 * g.adj.size + 2 * arcCount g + 7⌝⦄ := by
  have hctor : (Construct.make (E := cp.Edge T) ((-1 : Int), (-1 : Int), ()) st).run
      (t0 + 1 + g.n_.toNat) =
    some ((⟨-1, -1, st.Edge_next_id, 1⟩, { Edge_next_id := st.Edge_next_id + 1 }),
      t0 + 1 + g.n_.toNat + 1) := rfl
  obtain ⟨cycle, t', run, result, length, work⟩ := directed_cycle_spec g valid hsmall _ _ _ t0 _ hctor
  have hsize : g.n_.toNat = g.adj.size := by simp [valid.size_eq]
  refine triple_of_run _ t' run ⟨rfl, rfl, result, length, ?_⟩
  omega

/-- Count the colour and parent buffers, the at-most-one cycle buffer, and the live recursive frames. -/
theorem find_cycle_workspace_slots {Cost E : Type} [Inhabited E] [Field "to" E Int]
    (g : cp.ListGraph Cost E) (st : Proofs.FindCycleInv.FS) (visited : Array Int) (parents cycle : Array E)
    (inv : Invariant g st) (active : Active g visited parents st) (cycleLength : cycle.size ≤ g.adj.size) :
    visited.size + parents.size + cycle.size + st.sp ≤ 4 * g.adj.size := by
  have hs := inv.sp_le
  rw [active.visited_size, active.parents_size]
  omega

end Proofs.Cpp.GraphList

namespace Proofs.Cpp.GraphList

open Proofs.Cpp.ListTopological

theorem topological_sort_spec {Cost E : Type} [Inhabited E] [Field "to" E Int]
    (g : cp.ListGraph Cost E) (valid : ValidGraph g) (hsmall : g.adj.size < Cpp.fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.topological_sort g
    ⦃⇓ r c => ⌜r.2 = g ∧ TopologicalResult .stack g r.1 ∧ c ≤ t0 + workBound .stack g⌝⦄ := by
  obtain ⟨order, t', run, correct, work⟩ := program_spec .stack g valid hsmall t0
  rw [← topological_stack_program g] at run
  exact triple_of_run (order, g) t' run ⟨rfl, correct, work⟩

theorem topological_sort_minimum_spec {Cost E : Type} [Inhabited E] [Field "to" E Int]
    (g : cp.ListGraph Cost E) (valid : ValidGraph g) (hsmall : g.adj.size < Cpp.fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.topological_sort_minimum g
    ⦃⇓ r c => ⌜r.2 = g ∧ TopologicalResult .minimum g r.1 ∧ c ≤ t0 + workBound .minimum g⌝⦄ := by
  obtain ⟨order, t', run, correct, work⟩ := program_spec .minimum g valid hsmall t0
  rw [← topological_minimum_program g] at run
  exact triple_of_run (order, g) t' run ⟨rfl, correct, work⟩

/-- Allow the full reserved order buffer, the peak frontier, and a possible return copy. -/
theorem topological_sort_workspace_slots {Cost E : Type} [Field "to" E Int]
    {g : cp.ListGraph Cost E} {mode : Discipline} {s : TopologicalState}
    (inv : Represents mode g s) (frontierPeak : Nat) (peakBound : frontierPeak ≤ g.adj.size) :
    g.adj.size + s.2.1.size + frontierPeak + s.1.size ≤ 4 * g.adj.size := by
  have h := workspace inv
  have hz := inv.inv.dsz
  omega

end Proofs.Cpp.GraphList
