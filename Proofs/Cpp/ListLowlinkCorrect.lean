import Proofs.Cpp.ListLowlinkCorrectState

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ListLowlink

open Proofs.LowlinkInv Proofs.LowlinkRoot Proofs.LowlinkPush Proofs.LowlinkPop

def SemPost {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E))
    (n v : Nat) (start : St) (args res : DfsState) : Prop :=
  ∃ done, FrameEnd adj n v start done args res

theorem get_child_low {E : Type} [Inhabited E] [Field "to" E Int]
    {adj : Array (Array E)} {n v : Nat} {p : Int} {start st : St} {args : DfsState}
    {r : LoopState} {pref suff : List E} {e : E} (A : FrameStart adj n v p start args)
    (H : CursorState adj n v start st args pref r) (_hrow : (Row adj v).toList = pref ++ e :: suff)
    (hw : r.core.seen[(Field.get (member := "to") e : Int).toNat]! = false)
    (lo : Array Int) (hlo : lo.size = n) :
    get (set lo v (min (get lo v) (get lo (Field.get (member := "to") e))))
      (Field.get (member := "to") e) = get lo (Field.get (member := "to") e) := by
  let w := (Field.get (member := "to") e : Int).toNat
  have hh : v ∈ st.Vis := H.mem A.mem
  have hne : w ≠ v := by
    intro he
    change r.core.seen[w]! = false at hw
    rw [he, (H.arrays.visits.marked v).mpr hh] at hw
    contradiction
  have hsize : v < lo.size := by rw [hlo]; exact H.valid.vis_lt _ hh
  simp only [get_eq, Int.toNat_natCast]
  change (set lo v (min lo[v]! lo[w]!))[w]! = lo[w]!
  rw [getElemBang_set _ _ _ _ (by simpa using hsize)]
  simp [hne]

private theorem cursor_exists {E : Type} [Inhabited E] [Field "to" E Int]
    {adj : Array (Array E)} {n v : Nat} {start st : St} {args : DfsState}
    {pref : List E} {r : LoopState} (H : CursorState adj n v start st args pref r) :
    ∃ st', CursorState adj n v start st' args pref r := ⟨st, H⟩

set_option linter.unusedTactic false in
theorem dfs_correct {Cost E : Type} [Inhabited E] [Field "to" E Int] (fuel : Nat) :
    ∀ (g : cp.ListGraph Cost E) (v : Nat) (parent : Int) (start : St) (args : DfsState),
    GH g.n_.toNat (rowHeads g.adj g.n_.toNat) (rowEnds g.adj g.n_.toNat) →
    Valid g.adj g.n_.toNat →
    FrameStart g.adj g.n_.toNat v parent start args →
    g.n_.toNat + 1 ≤ fuel + start.Vis.length →
    ∀ t0 : Nat,
    ⦃fun c => ⌜c = t0⌝⦄
      cp.ListGraph.lowlink_dfs_rec fuel g v parent args.seen args.order args.low args.points args.bridges args.counter
    ⦃⇓ r _ => ⌜SemPost g.adj g.n_.toNat v start args r⌝⦄ := by
  induction fuel with
  | zero =>
    intro g v p start args G valid A hf
    have h := A.valid.vis_len_le
    omega
  | succ fuel ih =>
    intro g v parent start args G valid A hf t0
    have hg : (⟨g.n_, g.m_, g.adj, g.shortest_path_dist, g.shortest_path_parent⟩ : cp.ListGraph Cost E) = g := rfl
    have hCall (w : Int) (p : Int) (u : Array Bool) (o l a : Array Int) (b : Array (Int × Int)) (cnt : Int)
        (Q : PostCond DfsState PS) :
        ⦃fun c => ⌜0 ≤ w ∧ ∃ prepared,
          FrameStart g.adj g.n_.toNat w.toNat p prepared (u, o, l, a, b, cnt) ∧
          g.n_.toNat + 1 ≤ fuel + prepared.Vis.length ∧
          ∀ r t, SemPost g.adj g.n_.toNat w.toNat prepared (u, o, l, a, b, cnt) r → (Q.1 r t).down⌝⦄
        cp.ListGraph.lowlink_dfs_rec fuel
          ⟨g.n_, g.m_, g.adj, g.shortest_path_dist, g.shortest_path_parent⟩ w p u o l a b cnt
        ⦃Q⦄ := by
      rw [hg]
      apply Triple.iff.mpr
      intro c hs
      obtain ⟨hw, st, H, hf', hq⟩ := hs
      have he : (w.toNat : Int) = w := by omega
      have hT := wp_of_triple (Q := Q) (ih g w.toNat p st (u, o, l, a, b, cnt) G valid H hf')
      rw [he] at hT
      exact (Triple.iff.mp hT) c hq
    mvcgen [cp.ListGraph.lowlink_dfs_rec, hCall]
    case inv1 =>
      exact ⟨fun ⟨xs, r⟩ _ => ⌜∃ st, CursorState g.adj g.n_.toNat v start st args xs.prefix r⌝,
        ExceptConds.false⟩
    all_goals simp +zetaDelta only [SPred.down_pure] at *
    case vc4.succ.pre =>
      exact ⟨start, enter_cursor A⟩
    case vc9.succ.post.except => simp
    case vc1.step.isTrue =>
      obtain ⟨st, H⟩ := ‹∃ st, CursorState _ _ _ _ st _ _ _›
      have hrow := ‹(get g.adj (v : Int)).toList = _ ++ _ :: _›
      have hv := H.valid.vis_lt _ (H.mem A.mem)
      have hn := (valid v hv _ (edge_mem_of_split hrow)).1
      have hfalse := ‹(!get _ _) = true›
      have Hchild := prepare_child G valid A H hrow (by simpa [get_eq] using hfalse)
      have hlen := H.frame.grows.length_le
      refine ⟨hn, _, Hchild, ?_, ?_⟩
      · simp only [pushS, List.length_append, List.length_singleton]
        omega
      · intro res t result
        obtain ⟨done, D⟩ := result
        have cc := cursor_exists (join_cursor_step G valid A H hrow (by simpa [get_eq] using hfalse) D)
        have hs := get_child_low A H hrow (by simpa [get_eq] using hfalse) res.low D.arrays.lowSize
        simp only [hs, wp_ite]
        split <;> split <;> refine (wp_run_some _ _ _ _ _ rfl).mpr ?_
        all_goals
          simp only [SPred.down_pure]
          simp only [joinChild, LoopState.ofCore, DfsState.withLow, DfsState.withBridges,
            DfsState.seen, DfsState.order, DfsState.low, DfsState.points, DfsState.bridges, DfsState.counter,
            LoopState.art, LoopState.skipped, LoopState.children, Int.toNat_of_nonneg hn, bridgeKey,
            Bool.and_eq_true, decide_eq_true_eq] at cc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at *
          simp only [get_eq, Int.toNat_natCast] at *
          simpa [*] using cc
    case vc2.step.isFalse.isTrue =>
      obtain ⟨st, H⟩ := ‹∃ st, CursorState _ _ _ _ st _ _ _›
      have hrow := ‹(get g.adj (v : Int)).toList = _ ++ _ :: _›
      have hn := (valid v (H.valid.vis_lt _ (H.mem A.mem)) _ (edge_mem_of_split hrow)).1
      have h := cursor_exists (visit_cursor_step A H hrow hn (by simpa [get_eq] using ‹¬(!get _ _) = true›))
      have hs := ‹(decide (_ = parent) && !_) = true›
      simpa only [visitedRow, Int.toNat_of_nonneg hn, ite_eq_left hs, LoopState.ofCore] using h
    case vc3.step.isFalse.isFalse =>
      obtain ⟨st, H⟩ := ‹∃ st, CursorState _ _ _ _ st _ _ _›
      have hrow := ‹(get g.adj (v : Int)).toList = _ ++ _ :: _›
      have hn := (valid v (H.valid.vis_lt _ (H.mem A.mem)) _ (edge_mem_of_split hrow)).1
      have h := cursor_exists (visit_cursor_step A H hrow hn (by simpa [get_eq] using ‹¬(!get _ _) = true›))
      have hs := ‹¬(decide (_ = parent) && !_) = true›
      simpa only [visitedRow, Int.toNat_of_nonneg hn, ite_eq_right hs, LoopState.ofCore, DfsState.withLow,
        get_eq, Int.toNat_natCast] using h
    all_goals
      obtain ⟨st, H⟩ := ‹∃ st, CursorState _ _ _ _ st _ _ _›
      refine ⟨st, ?_⟩
      have h := finish_cursor A H
      simpa [finishFrame, DfsState.withPoints, *] using h


open Proofs.LowlinkMultigraph Proofs.LowlinkGraph Proofs.LowlinkFinal Proofs.Cpp.LowlinkResults
open Proofs.PrimMath (Rtc)

structure ForestState {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n : Nat)
    (st : St) (args : DfsState) : Prop where
  valid : MInv n (rowHeads adj n) (rowEnds adj n) st
  emptyStack : st.sp = 0
  arrays : VisitArrays n st args
  points : PointsMatch st none args.points
  bridges : BridgesMatch (listTargets adj) st args.bridges

def initialState (n : Int) : DfsState :=
  (replicate n false, replicate n 0, replicate n 0, ([] : List Int).toArray, ([] : List (Int × Int)).toArray, 0)

theorem initial_forest {E : Type} [Inhabited E] [Field "to" E Int]
    (adj : Array (Array E)) (n : Int) :
    ForestState adj n.toNat (initS (fun _ => 0) (fun _ => 0) (fun _ => 0)) (initialState n) := by
  have hSize : (replicate n false).size = n.toNat := by simp [replicate]
  have hfalse : ∀ j : Nat, (replicate n false)[j]! = false := by
    intro j
    by_cases h : j < n.toNat
    · simp [replicate, getElem!_pos, h]
    · have hj : ¬ j < (replicate n false).size := by simpa [hSize] using h
      rw [getElem!_neg (replicate n false) j hj]
      rfl
  exact ⟨inv_init _ _ _ _ _ _, rfl,
    ⟨hSize, by simp [initialState, replicate, DfsState.order], by simp [initialState, replicate, DfsState.low],
      ⟨by simp [initialState, initS, hfalse], by simp [initS], rfl⟩⟩,
    ⟨by simp [initialState, DfsState.points], by simp [initialState, DfsState.points, PointMember, EmitsPoint, initS]⟩,
    ⟨by simp [initialState, DfsState.bridges], by simp [initialState, DfsState.bridges, BridgeMember, EmitsBridge, initS]⟩⟩

theorem prepare_root {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {st : St} {args : DfsState} (G : GH n (rowHeads adj n) (rowEnds adj n))
    (H : ForestState adj n st args) (hv : v < n) (hf : args.seen[v]! = false) :
    FrameStart adj n v (-1) (rootS (rowHeads adj n) st v) args := by
  have hnew : v ∉ st.Vis := by rw [← H.arrays.visits.marked v, hf]; decide
  obtain ⟨I', visit'⟩ := enter_root G H.valid H.arrays.visits H.emptyStack hv
    H.arrays.seenSize H.arrays.orderSize hf
  obtain ⟨hP, hB⟩ := output_unchanged H.valid (root_preserves_finished H.valid hnew)
    (after := rootS (rowHeads adj n) st v) rfl (fun x hx => upd_ne _ _ _ _ (fun he => hnew (he ▸ hx)))
    _ _ _ H.points H.bridges
  refine ⟨I', (by change 0 < 1; decide), (by change upd st.Sk 0 v 0 = v; exact upd_same _ _ _), H.valid.par_none _ hnew, upd_same _ _ _, ?_,
    H.valid.sep_unv _ hnew, hf,
    ⟨(size_set _ _ _).trans H.arrays.seenSize, (size_set _ _ _).trans H.arrays.orderSize,
      (size_set _ _ _).trans H.arrays.lowSize, visit'⟩, hP, hB⟩
  show upd st.L v (st.Vis.length : Int) v = args.counter
  rw [upd_same, H.arrays.visits.counter]

theorem complete_root {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n v : Nat} {st done : St} {args res : DfsState}
    (A : FrameStart adj n v (-1) (rootS (rowHeads adj n) st v) args)
    (D : FrameEnd adj n v (rootS (rowHeads adj n) st v) done args res) :
    ForestState adj n (popS done v) res := by
  have hd : 0 < done.sp := by rw [D.frame.depth]; exact A.depth
  have ht := D.frame.top A.depth A.top
  have hz : done.sp = 1 := D.frame.depth
  have hp := (D.frame.visited v A.mem).2.trans A.parentEq
  obtain ⟨I', V'⟩ := pop_projection D.valid D.arrays.visits hd ht D.cursor
  have P' := point_pop D.valid hd ht _ D.points
  have B' := bridge_pop D.valid hd ht _ _ D.bridges
  have hm : BridgesMatch (listTargets adj) (popS done v) res.bridges := by simpa [hp] using B'
  refine ⟨I', ?_, ⟨D.arrays.seenSize, D.arrays.orderSize, D.arrays.lowSize, V'⟩, P', hm⟩
  show done.sp - 1 = 0
  rw [hz]

def ForestLoop {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n k : Nat)
    (args : DfsState) : Prop :=
  (∀ j : Nat, j < k → args.seen[j]! = true) ∧ ∃ st, ForestState adj n st args

def CutVertex (edges : List Edge) (n : Nat) (x : Int) : Prop :=
  ∃ v : Nat, v < n ∧ (v : Int) = x ∧ ∃ a b, v ≠ a ∧ v ≠ b ∧ Adj edges v a ∧ Adj edges v b ∧
    ¬ Rtc (LlFinal.EV (Adj edges) v) a b

structure ExactResults (edges : List Edge) (n : Nat) (points : Array Int) (bridges : Array (Int × Int)) : Prop where
  pointsOrdered : points.toList.Pairwise (· ≤ ·)
  pointsUnique : points.toList.Nodup
  pointsExact : ∀ x, x ∈ points.toList ↔ CutVertex edges n x
  bridgesOrdered : bridges.toList.Pairwise EndpointOrder
  bridgesUnique : bridges.toList.Nodup
  bridgesExact : ∀ key, key ∈ bridges.toList ↔ OccurrenceBridge edges key

theorem exact_results {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n : Nat} {st : St} {args : DfsState} {edges : List Edge}
    (H : RowsRepresent edges n (listTargets adj)) (F : ForestState adj n st args)
    (hall : ∀ j : Nat, j < n → args.seen[j]! = true) :
    ExactResults edges n (sort args.points) (sortLex args.bridges) := by
  obtain ⟨hpts, hptsP, hbridge, hbridgeP⟩ := sorted_results args.points args.bridges
  have hm : ∀ j, j < n → j ∈ st.Vis := fun j hj => (F.arrays.visits.marked _).mp (hall j hj)
  refine ⟨hpts, hptsP.nodup_iff.mpr F.points.1, ?_, hbridge, hbridgeP.nodup_iff.mpr F.bridges.1, ?_⟩
  · intro x
    rw [hptsP.mem_iff, F.points.2]
    constructor
    · rintro ⟨v, he, h | ⟨e, _⟩⟩
      · have hmem : v ∈ st.Vis := by
          by_contra hn
          have := F.valid.fin_unv v hn
          have := h.1
          omega
        have hv := F.valid.vis_lt _ hmem
        exact ⟨v, hv, he, (point_test_final H F.valid F.emptyStack hm hv).mp h⟩
      · cases e
    · rintro ⟨v, hv, he, h⟩
      exact ⟨v, he, Or.inl ((point_test_final H F.valid F.emptyStack hm hv).mpr h)⟩
  · intro key
    rw [hbridgeP.mem_iff, F.bridges.2]
    exact bridge_test_final H F.valid F.emptyStack hm key

theorem seen_next {n cur : Int} {pref suff : List Int} {u : Array Bool}
    (hs : range 0 n = pref ++ cur :: suff) (old : ∀ i : Nat, i < pref.length → u[i]! = true)
    (newSeen : u[cur.toNat]! = true) :
    ∀ i : Nat, i < (pref ++ [cur]).length → u[i]! = true := by
  have hi := range_cursor hs
  simp only [Int.zero_add] at hi
  intro i hb
  by_cases ho : i < pref.length
  · exact old i ho
  · simp only [List.length_append, List.length_singleton] at hb
    have h : i = cur.toNat := by omega
    rwa [h]

theorem prepare_root_at_cursor {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)}
    {n current : Int} {pref suff : List Int} {st : St} {args : DfsState}
    (G : GH n.toNat (rowHeads adj n.toNat) (rowEnds adj n.toNat))
    (F : ForestState adj n.toNat st args) (hs : range 0 n = pref ++ current :: suff)
    (hf : args.seen[current.toNat]! = false) :
    FrameStart adj n.toNat current.toNat (-1) (rootS (rowHeads adj n.toNat) st current.toNat) args := by
  have hi := range_cursor hs
  have hb := range_prefix_length hs
  simp only [Int.zero_add, Int.sub_zero] at hi hb
  exact prepare_root G F (by omega) hf

theorem lowlink_correct {Cost E : Type} [Inhabited E] [Field "to" E Int] (g : cp.ListGraph Cost E)
    (edges : List Edge) (H : RowsRepresent edges g.n_.toNat (listTargets g.adj))
    (valid : Valid g.adj g.n_.toNat) (hsmall : g.n_.toNat ≤ Cpp.fuel) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.lowlink g
    ⦃⇓ r _ => ⌜r.2 = g ∧ ExactResults edges g.n_.toNat r.1.1 r.1.2⌝⦄ := by
  have G := H.view.1
  have hg : (⟨g.n_, g.m_, g.adj, g.shortest_path_dist, g.shortest_path_parent⟩ : cp.ListGraph Cost E) = g := rfl
  have hCall (v parent : Int) (u : Array Bool) (o l a : Array Int) (b : Array (Int × Int)) (cnt : Int)
      (Q : PostCond DfsState PS) :
      ⦃fun c => ⌜0 ≤ v ∧ ∃ st,
        FrameStart g.adj g.n_.toNat v.toNat parent st (u, o, l, a, b, cnt) ∧
        g.n_.toNat + 1 ≤ Cpp.fuel + st.Vis.length ∧
        ∀ r t, SemPost g.adj g.n_.toNat v.toNat st (u, o, l, a, b, cnt) r → (Q.1 r t).down⌝⦄
      cp.ListGraph.lowlink_dfs ⟨g.n_, g.m_, g.adj, g.shortest_path_dist, g.shortest_path_parent⟩ v parent u o l a b cnt
      ⦃Q⦄ := by
    rw [hg]
    unfold cp.ListGraph.lowlink_dfs
    apply Triple.iff.mpr
    intro c hs
    obtain ⟨hv, st, A, hlen, hq⟩ := hs
    have he : (v.toNat : Int) = v := by omega
    have ht := wp_of_triple (Q := Q) (dfs_correct Cpp.fuel g v.toNat parent st (u, o, l, a, b, cnt) G valid A hlen)
    rw [he] at ht
    exact (Triple.iff.mp ht) c hq
  mvcgen [cp.ListGraph.lowlink, hCall]
  case inv1 =>
    exact ⟨fun ⟨xs, r⟩ _ => ⌜ForestLoop g.adj g.n_.toNat xs.prefix.length r⌝, ExceptConds.false⟩
  all_goals simp +zetaDelta only [SPred.down_pure] at *
  case vc1.step.isTrue =>
    have hs := ‹range 0 g.n_ = _ ++ _ :: _›
    have hcur := range_cursor hs
    have hb := range_prefix_length hs
    simp only [Int.zero_add, Int.sub_zero] at hcur hb
    obtain ⟨hseen, st, F⟩ := ‹ForestLoop _ _ _ _›
    have hr := prepare_root_at_cursor G F hs (by simpa [get_eq] using ‹(!get _ _) = true›)
    refine ⟨by omega, _, hr, ?_, ?_⟩
    · simp only [rootS, List.length_append, List.length_singleton]
      omega
    · intro res t post
      refine (wp_run_some _ _ _ _ _ rfl).mpr ?_
      obtain ⟨done, D⟩ := post
      have Fc := complete_root hr D
      have seen := seen_next hs (fun i hi => D.stable.1 i (hseen i hi)) (by
        apply (D.arrays.visits.marked _).mpr
        exact D.frame.grows.subset hr.mem)
      exact ⟨seen, _, Fc⟩
  case vc2.step.isFalse =>
    have hs := ‹range 0 g.n_ = _ ++ _ :: _›
    obtain ⟨hseen, hf⟩ := ‹ForestLoop _ _ _ _›
    exact ⟨seen_next hs hseen (by simpa [get_eq] using ‹¬(!get _ _) = true›), hf⟩
  case vc3.pre =>
    exact ⟨fun _ hk => False.elim (Nat.not_lt_zero _ hk), _, initial_forest _ _⟩
  case vc4.post.success =>
    obtain ⟨hseen, st, F⟩ := ‹ForestLoop _ _ _ _›
    simp only [range_length, Int.sub_zero] at hseen
    exact ⟨trivial, exact_results H F hseen⟩
  case vc5.post.except => simp


end Proofs.Cpp.ListLowlink
