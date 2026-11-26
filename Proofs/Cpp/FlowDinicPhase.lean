import Proofs.Cpp.FlowDinicBlock

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowResidual Proofs.Cpp.FlowBfs
open Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView Proofs.Cpp.FlowCostSearch

namespace Proofs.Cpp.FlowDinic

variable {E Arc : Type} [Inhabited E] [Field "cap" E Int] [Field "cost" E Int] [Field "to" E Int]
  [Field "rev" E Int] [WriteField "cap" E Int] [NumericTraits "Cost" Int] [ShiftInt Int] [DecidableEq Arc]

def phaseCharge (g : cp.FlowGraph Int E) (arcs : List Arc) : Nat :=
  7 + 5 * g.adj.size + 4 * FlowCostSearch.arcCount g + 8 * arcs.length * (3 + 2 * g.adj.size)

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem tickN_run (k t : Nat) : (tickN k).run t = some ((), t + k) := rfl
private theorem some_bind {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

private theorem suffix {A B C D : Type} (a : M A) (b : A → M B) (c : B → M C) (f : C → D) :
    (do let x ← a; let y ← b x; let z ← c y; pure (f z)) =
      (do let z ← (do let x ← a; let y ← b x; c y); pure (f z)) := by
  simp only [bind_assoc]

private def layout_level (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (h : CapacityLayout n g slot atSlot) (lv : Array Int) :
    CapacityLayout n {g with level := lv} slot atSlot := by
  let old := h.order
  exact ⟨⟨old.position, old.graph_size, old.tailBound, old.headBound, old.positionBound,
    old.lookup, old.lookup_sound, old.covers, old.dest, old.cap, old.cost⟩, h.slotEq, h.represents, h.reverseIndices⟩

private def startLayer (n : Network Arc Nat) (g : cp.FlowGraph Int E) (slot : Arc → Slot)
    (atSlot : Int → Int → Option Arc) (h : CapacityLayout n g slot atSlot) (t : Nat)
    (dist : ValidDistance n (capacity g.adj slot) (levelsView g.level)) (nonnegative : ∀ a, 0 ≤ capacity g.adj slot a) :
    LayerState n (initializeCursors g) slot atSlot t := by
  have shape : g.n_.toNat = g.adj.size := by simp [h.order.graph_size]
  refine ⟨layout_changeIter h _, ⟨by simp [initializeCursors, replicate, shape], ?_, ?_⟩, dist, nonnegative⟩
  · intro v hv
    have hv' : v < g.adj.size := hv
    have hzero : cursor (initializeCursors g) v = 0 := by simp [cursor, initializeCursors, replicate, shape, hv', getElem!_pos]
    simp [hzero, Cpp.size]
  · intro a ha
    have hv := h.order.tailBound a
    have hzero : cursor (initializeCursors g) (n.tail a) = 0 := by
      simp [cursor, initializeCursors, replicate, shape, hv, getElem!_pos]
    rw [hzero] at ha
    omega

private theorem init_charge (g : cp.FlowGraph Int E) : cursorCharge (initializeCursors g) = 0 := by
  simp [cursorCharge, initializeCursors, replicate]

inductive PhaseTransition (n : Network Arc Nat) (arcs : List Arc) (base : Capacity Arc)
    (g : cp.FlowGraph Int E) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc) (s t : Nat) (flow : Int) :
    ForInStep (MaxFrame Int E) → Prop where
  | halt (lv : Array Int) : (∀ amount f, SignedFeasible n arcs base s t amount f → amount ≤ flow) →
      PhaseTransition n arcs base g slot atSlot s t flow (.done (packMax (some (flow, {g with level := lv})) {g with level := lv} flow))
  | progress (out : cp.FlowGraph Int E) (amount : Int) (d : Nat) :
      CapacityLayout n out slot atSlot → (out.n_ = g.n_ ∧ out.m_ = g.m_) →
      (out.adj.size = g.adj.size ∧ ∀ v : Nat, out.adj[v]!.size = g.adj[v]!.size) →
      (∀ a, 0 ≤ capacity out.adj slot a) →
      SignedFeasible n arcs base s t amount (fun a => base a - capacity out.adj slot a) → flow ≤ amount →
      d < g.adj.size → (∃ path, Path n s t path ∧ path.length = d ∧ ∀ a ∈ path, 0 < capacity g.adj slot a) →
      (∀ path, Path n s t path → (∀ a ∈ path, 0 < capacity out.adj slot a) → d < path.length) →
      PhaseTransition n arcs base g slot atSlot s t flow (.yield (packMax none out amount))

/-- One successful phase strictly raises the shortest residual source-to-sink distance. -/
theorem max_step_spec (n : Network Arc Nat) (arcs : List Arc) (nd : arcs.Nodup) (all : ∀ a, a ∈ arcs)
    (base : Capacity Arc) (g : cp.FlowGraph Int E) (slot : Arc → Slot) (atSlot : Int → Int → Option Arc)
    (state : CapacityLayout n g slot atSlot) (laws : CapLaws (E := E)) (nonnegative : ∀ a, 0 ≤ capacity g.adj slot a)
    (s t : Nat) (hs : s < g.adj.size) (ht : t < g.adj.size) (different : s ≠ t) (fuelSize : g.adj.size + 2 ≤ fuel)
    (fuelArcs : 8 * arcs.length + 1 ≤ fuel) (limPos : 0 < flowLimit)
    (edgeBound : ∀ a, base a ≤ 7 * flowLimit) (flow : Int) (flowNonnegative : 0 ≤ flow)
    (feasible : SignedFeasible n arcs base s t flow (fun a => base a - capacity g.adj slot a)) (clock : Nat) :
    ∃ step finish, (maxStep (s : Int) (t : Int) () (packMax none g flow)).run clock = some (step, finish) ∧
      PhaseTransition n arcs base g slot atSlot s t flow step ∧ finish ≤ clock + phaseCharge g arcs := by
  obtain ⟨lv, tBfs, ran, lvSize, root, distance, cells, bfsCost⟩ := bfs_phase n g slot atSlot state s hs fuelSize (clock + 1)
  let reset : cp.FlowGraph Int E := initializeCursors {g with level := lv}
  rcases cells t ht with missing | ⟨d, htRank, ds, w, reaches, exactDepth, along⟩
  · let inside (v : Nat) : Bool := (levelsView lv v).isSome
    have ho : levelsView lv t = none := by
      have h : lv[t]! = -1 := missing
      simp [levelsView, h]
    have closed (a : Arc) (yes : inside (n.tail a) = true) (no : inside (n.head a) = false) : capacity g.adj slot a ≤ 0 := by
      by_contra pos
      have seen : ∃ i, levelsView lv (n.tail a) = some i := by
        cases eq : levelsView lv (n.tail a) with
        | none => simp [inside, eq] at yes
        | some k => exact ⟨k, rfl⟩
      obtain ⟨i, hi⟩ := seen
      obtain ⟨j, hj, _⟩ := distance a (by omega) i hi
      simp [inside, hj] at no
    have maximum (amount : Int) (f : Arc → Int) (valid : SignedFeasible n arcs base s t amount f) : amount ≤ flow := by
      exact signed_cut_maximal n arcs (List.range g.adj.size) List.nodup_range
        (fun a _ => ⟨List.mem_range.mpr (state.order.tailBound a), List.mem_range.mpr (state.order.headBound a)⟩)
        base (capacity g.adj slot) inside s t (List.mem_range.mpr hs) (List.mem_range.mpr ht)
        (by simp [inside, root]) (by simp [inside, ho]) closed flow amount f feasible valid
    refine ⟨_, tBfs, ?_, .halt lv maximum, ?_⟩
    · unfold maxStep
      simp only [StateT.run_bind, maxGraph, maxAmount, packMax, tick_run, some_bind]
      change ((cp.FlowGraph.bfs g (s : Int)).run (clock + 1) >>= _) = _
      rw [ran]
      simp only [some_bind, missing, decide_true, ite_true]
      rfl
    · unfold phaseCharge
      omega
  · let upper : Int := (arcs.length : Int) * (7 * flowLimit)
    have capacityBound (amount : Int) (f : Arc → Int) (ok : SignedFeasible n arcs base s t amount f) : amount ≤ upper :=
      signed_capacity_bound n arcs base s t different (7 * flowLimit) amount (by omega) edgeBound f ok
    have initialized : LayerState n reset slot atSlot t :=
      startLayer n {g with level := lv} slot atSlot (layout_level n g slot atSlot state lv) t distance nonnegative
    have henergy := energy_bound n (levelsView lv) (capacity g.adj slot) arcs flow flowLimit flowNonnegative limPos
    have hbudget : phaseEnergy n (levelsView reset.level) (capacity reset.adj slot) arcs upper flow flowLimit + 1 ≤ fuel := by
      change phaseEnergy n (levelsView lv) (capacity g.adj slot) arcs ((arcs.length : Int) * (7 * flowLimit)) flow flowLimit + 1 ≤ fuel
      omega
    obtain ⟨out, amount, done, runBlock, ⟨stateOut⟩, same, newNet, greater, blocked, cost⟩ :=
      blocking_spec n arcs nd all base slot atSlot laws s t different upper capacityBound limPos fuel reset initialized hs ht root
        (by change g.adj.size ≤ fuel; omega) flow flowNonnegative feasible hbudget (tBfs + g.n_.toNat)
    have sameN : out.adj.size = g.adj.size := same.vertices
    have dims : out.adj.size = g.adj.size ∧ ∀ v : Nat, out.adj[v]!.size = g.adj[v]!.size := ⟨sameN, same.rows⟩
    have mEq := arcCount_withRows g out.adj dims
    have arcEq : FlowCostSearch.arcCount out = FlowCostSearch.arcCount g := mEq
    have timeEnergy := Nat.mul_le_mul_right (3 + 2 * g.adj.size) henergy
    have pay := cursor_charge_bound n out slot t stateOut.cursors
    rw [arcEq] at pay
    rw [init_charge] at cost
    have hsz : g.n_.toNat = g.adj.size := by simp [state.order.graph_size]
    rw [hsz] at cost
    have hleaf : (get lv (t : Int)) ≠ -1 := by
      have hGet : get lv (t : Int) = (d : Int) := (view_some lv (by rwa [lvSize])).mp htRank
      rw [hGet]
      omega
    have allOldLabels : out.level = lv := same.level
    refine ⟨.yield (packMax none out amount), done, ?_, ?_, ?_⟩
    · unfold maxStep
      simp only [StateT.run_bind, maxGraph, maxAmount, packMax, tick_run, some_bind]
      change ((cp.FlowGraph.bfs g (s : Int)).run (clock + 1) >>= _) = _
      rw [ran]
      simp only [some_bind, hleaf, decide_false, Bool.false_eq_true, ite_false]
      rw [StateT.run_bind, tickN_run, some_bind]
      let emit (r : BlockFrame Int E) : ForInStep (MaxFrame Int E) :=
        .yield (packMax none (blockGraph r) (blockFlow r))
      change (do
        let bound ← cp.FlowGraph.F_MAX (Cost := Int) (E := E)
        let c ← cp.FlowGraph.dfs reset (s : Int) (t : Int) bound
        let r ← forIn forever (packBlock c.2 flow c.1) (blockStep (s : Int) (t : Int))
        pure (emit r) : M (ForInStep (MaxFrame Int E))).run (tBfs + g.n_.toNat) = _
      have join := suffix (cp.FlowGraph.F_MAX (Cost := Int) (E := E))
        (fun bound => cp.FlowGraph.dfs reset (s : Int) (t : Int) bound)
        (fun c => forIn forever (packBlock c.2 flow c.1) (blockStep (s : Int) (t : Int)))
        emit
      rw [join, StateT.run_bind]
      change ((blockingStart fuel reset (s : Int) (t : Int) flow).run (tBfs + g.n_.toNat) >>= _) = _
      rw [runBlock]
      rfl
    · refine .progress out amount d stateOut.layout ⟨same.vertexCount, same.arcCounter⟩ dims stateOut.nonnegative newNet greater ds
        ⟨w, reaches, exactDepth, fun a ha => (along a ha).1⟩ ?_
      intro path route available
      have postDist : ValidDistance n (capacity out.adj slot) (levelsView lv) := by
        simpa only [allOldLabels] using stateOut.distance
      exact blocking_increases n (capacity out.adj slot) (levelsView lv) postDist s t d root htRank
        (fun q walk positive tight => blocked ⟨q, walk, fun a ha => ⟨positive a ha, tight a ha⟩⟩) path route available
    · change done + 2 * 0 ≤ tBfs + g.adj.size + 3 + 2 * cursorCharge out +
        phaseEnergy n (levelsView lv) (capacity g.adj slot) arcs ((arcs.length : Int) * (7 * flowLimit)) flow flowLimit * (3 + 2 * g.adj.size) at cost
      unfold phaseCharge
      omega

end Proofs.Cpp.FlowDinic
