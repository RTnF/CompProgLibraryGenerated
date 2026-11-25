import Proofs.Cpp.Gen.GraphList
import Proofs.Cpp.Lib.Basic

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ListLowlink

def unseen (w : Nat → Nat) (used : Array Bool) : Nat → Nat
  | 0 => 0
  | k+1 => unseen w used k + if used[k]! then 0 else w k

theorem unseen_set (w : Nat → Nat) (used : Array Bool) (v n : Nat)
    (hv : v < used.size) (hf : used[v]! = false) :
    unseen w (set used v true) n + (if v < n then w v else 0) = unseen w used n := by
  induction n with
  | zero => simp [unseen]
  | succ k ih =>
    have hg := getElemBang_set used (v : Int) true k (by simpa using hv)
    simp only [Int.toNat_natCast] at hg
    simp only [unseen, hg]
    by_cases he : k = v
    · subst k
      simp [hf] at ih ⊢
      omega
    · by_cases hl : v < k
      · have hl' : v < k + 1 := by omega
        simp [he, hl, hl'] at ih ⊢
        omega
      · have hl' : ¬ v < k + 1 := by omega
        simp [he, hl, hl'] at ih ⊢
        omega

theorem get_marked (used : Array Bool) (v : Nat) (hv : v < used.size) :
    (set used v true)[v]! = true ∧
      (∀ j : Nat, used[j]! = true → (set used v true)[j]! = true) := by
  have hf (j : Nat) : (set used v true)[j]! = if j = v then true else used[j]! := by
    simpa using getElemBang_set used (v : Int) true j (by simpa using hv)
  refine ⟨by simp [hf], fun j hj => ?_⟩
  rw [hf]
  split <;> simp [hj]

abbrev DfsState := Array Bool × Array Int × Array Int × Array Int × Array (Int × Int) × Int

abbrev Row {E : Type} [Inhabited E] (adj : Array (Array E)) (i : Nat) := adj[i]!

def Valid {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n : Nat) : Prop :=
  ∀ v < n, ∀ e ∈ (Row adj v).toList,
    0 ≤ (Field.get (member := "to") e : Int) ∧ (Field.get (member := "to") e : Int).toNat < n

abbrev Remaining (used : Array Bool) (n : Nat) := unseen (fun _ => 1) used n
abbrev Weight {E : Type} [Inhabited E] (adj : Array (Array E)) (v : Nat) := 2 + 2 * (Row adj v).size
abbrev Budget {E : Type} [Inhabited E] (adj : Array (Array E)) (used : Array Bool) (n : Nat) :=
  unseen (Weight adj) used n

abbrev ArcsLeft {E : Type} [Inhabited E] (adj : Array (Array E)) (used : Array Bool) (n : Nat) :=
  unseen (fun v => (Row adj v).size) used n

/-- A call can change the order and low values only of newly discovered vertices.
The caller updates its own low value after the call returns. -/
structure Cells (n : Nat) (used : Array Bool) (ord low ord' low' : Array Int) : Prop where
  orderSize : ord'.size = n
  lowSize : low'.size = n
  preserves : ∀ j : Nat, used[j]! = true → ord'[j]! = ord[j]! ∧ low'[j]! = low[j]!

theorem Cells.enter (n v : Nat) (used : Array Bool) (ord low : Array Int) (o l : Int)
    (hv : v < n) (hf : used[v]! = false) (ho : ord.size = n) (hl : low.size = n) :
    Cells n used ord low (set ord v o) (set low v l) := by
  refine ⟨by simpa using ho, by simpa using hl, ?_⟩
  intro j hj
  have hne : j ≠ v := by
    intro he
    subst j
    simp [hf] at hj
  rw [getElemBang_set _ _ _ _ (by simpa [ho] using hv),
      getElemBang_set _ _ _ _ (by simpa [hl] using hv)]
  simp [hne]

private theorem Cells.updateLow {n v : Nat} {used : Array Bool} {ord low ord' low' : Array Int}
    (h : Cells n used ord low ord' low') (hv : v < n) (hf : used[v]! = false) (value : Int) :
    Cells n used ord low ord' (set low' v value) := by
  refine ⟨h.orderSize, by simpa using h.lowSize, ?_⟩
  intro j hj
  have hne : j ≠ v := by
    intro he
    subst j
    simp [hf] at hj
  rw [getElemBang_set _ _ _ _ (by simpa [h.lowSize] using hv)]
  simpa [hne] using h.preserves j hj

private theorem Cells.trans {n : Nat} {used used' : Array Bool} {ord low ord' low' ord'' low'' : Array Int}
    (h₁ : Cells n used ord low ord' low') (h₂ : Cells n used' ord' low' ord'' low'')
    (mono : ∀ j : Nat, used[j]! = true → used'[j]! = true) :
    Cells n used ord low ord'' low'' := by
  refine ⟨h₂.orderSize, h₂.lowSize, fun j hj => ?_⟩
  obtain ⟨ho₁, hl₁⟩ := h₁.preserves j hj
  obtain ⟨ho₂, hl₂⟩ := h₂.preserves j (mono j hj)
  exact ⟨ho₂.trans ho₁, hl₂.trans hl₁⟩

/-- Newly discovered vertices, in the same order as the assigned C++ visit numbers. -/
structure Discovery (n : Nat) (oldUsed used : Array Bool) (oldCount count : Int) (order : Array Int)
    (discovered : List Nat) : Prop where
  counter : count = oldCount + discovered.length
  nodup : discovered.Nodup
  fresh : ∀ j ∈ discovered, j < n ∧ oldUsed[j]! = false
  marked : ∀ j : Nat, used[j]! = true ↔ oldUsed[j]! = true ∨ j ∈ discovered
  numbered : ∀ (k : Nat) (hk : k < discovered.length), order[discovered[k]]! = oldCount + k

theorem Discovery.single (n v : Nat) (used : Array Bool) (counter : Int) (ord : Array Int)
    (hv : v < n) (hu : used.size = n) (ho : ord.size = n) (hf : used[v]! = false) :
    Discovery n used (set used v true) counter (counter + 1) (set ord v counter) [v] := by
  refine ⟨by simp, by simp, ?_, ?_, ?_⟩
  · intro j hj
    have he : j = v := by simpa using hj
    subst j
    exact ⟨hv, hf⟩
  · intro j
    rw [getElemBang_set _ _ _ _ (by simpa [hu] using hv)]
    by_cases he : j = v <;> simp [he]
  · intro k hk
    have hk0 : k = 0 := by simp at hk; omega
    subst k
    rw [getElemBang_set _ _ _ _ (by simpa [ho] using hv)]
    simp

private theorem Discovery.append {n : Nat} {oldUsed used used' : Array Bool} {start count count' : Int}
    {ord low ord' low' : Array Int} {xs ys : List Nat}
    (h : Discovery n oldUsed used start count ord xs) (h' : Discovery n used used' count count' ord' ys)
    (stable : Cells n used ord low ord' low') :
    Discovery n oldUsed used' start count' ord' (xs ++ ys) := by
  refine ⟨by simp [h'.counter, h.counter, add_assoc], ?_, ?_, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨h.nodup, h'.nodup, ?_⟩
    rintro x hx y hy rfl
    have hx' := (h.marked x).mpr (Or.inr hx)
    have hy' := (h'.fresh x hy).2
    simp [hx'] at hy'
  · intro j hj
    rcases List.mem_append.mp hj with hx | hy
    · exact h.fresh _ hx
    · have hh := h'.fresh _ hy
      refine ⟨hh.1, ?_⟩
      cases he : oldUsed[j]! with
      | false => rfl
      | true =>
        have hh' := (h.marked j).mpr (Or.inl he)
        simp [hh'] at hh
  · intro j
    rw [h'.marked, h.marked, List.mem_append, or_assoc]
  · intro k hk
    by_cases hkx : k < xs.length
    · have hx := (stable.preserves xs[k] ((h.marked xs[k]).mpr (Or.inr (List.getElem_mem hkx)))).1
      rw [List.getElem_append_left hkx, hx, h.numbered]
    · have hk' : k - xs.length < ys.length := by simp only [List.length_append] at hk; omega
      rw [List.getElem_append_right (by omega), h'.numbered _ hk', h.counter]
      omega

def Scanned {E : Type} [Field "to" E Int] (used : Array Bool) (edges : List E) : Prop :=
  ∀ e ∈ edges, used[((Field.get (member := "to") e) : Int).toNat]! = true

private theorem Scanned.mono {E : Type} [Field "to" E Int] {used used' : Array Bool} {edges : List E}
    (h : Scanned used edges) (mono : ∀ j : Nat, used[j]! = true → used'[j]! = true) :
    Scanned used' edges := fun e he => mono _ (h e he)

private theorem Scanned.step {E : Type} [Field "to" E Int] {used : Array Bool} {edges : List E} {e : E}
    (h : Scanned used edges) (seen : used[((Field.get (member := "to") e) : Int).toNat]! = true) :
    Scanned used (edges ++ [e]) := by
  intro a ha
  rcases List.mem_append.mp ha with hp | hm
  · exact h a hp
  · have he : a = e := by simpa using hm
    subst a
    exact seen

-- Every DFS call reserves one unit for its incoming edge, so the root never emits a bridge of its own.
structure DfsPost {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n v : Nat)
    (used : Array Bool) (ord low points : Array Int) (bridges : Array (Int × Int)) (visitCount : Int) (t0 : Nat)
    (res : DfsState) (t : Nat) : Prop where
  size : res.1.size = n
  marked : res.1[v]! = true
  monotone : ∀ j : Nat, used[j]! = true → res.1[j]! = true
  decrease : Remaining res.1 n < Remaining used n
  work : t + Budget adj res.1 n ≤ t0 + Budget adj used n
  pointsCount : res.2.2.2.1.size + Remaining res.1 n ≤ points.size + Remaining used n
  bridgesCount : res.2.2.2.2.1.size + Remaining res.1 n + 1 ≤ bridges.size + Remaining used n
  pointArcs : res.2.2.2.1.size + ArcsLeft adj res.1 n ≤ points.size + ArcsLeft adj used n
  bridgeArcs : res.2.2.2.2.1.size + ArcsLeft adj res.1 n ≤ bridges.size + ArcsLeft adj used n
  cells : Cells n used ord low res.2.1 res.2.2.1
  log : ∃ xs, Discovery n used res.1 visitCount res.2.2.2.2.2 res.2.1 xs ∧
    ∀ y ∈ xs, Scanned res.1 (Row adj y).toList

abbrev LoopState := Array Bool × Array Int × Array Int × Array Int × Array (Int × Int) × Int × Bool × Bool × Int

def LoopInv {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n v : Nat)
    (used : Array Bool) (ord low points : Array Int) (bridges : Array (Int × Int)) (visitCount : Int) (t0 : Nat) (pref : List E)
    (r : LoopState) (t : Nat) : Prop :=
  r.1.size = n ∧
  r.1[v]! = true ∧
  (∀ j : Nat, used[j]! = true → r.1[j]! = true) ∧
  Remaining r.1 n + 1 ≤ Remaining used n ∧
  t + 1 + Budget adj r.1 n + 2 * (Row adj v).size ≤ t0 + Budget adj used n + 2 * pref.length ∧
  r.2.2.2.1.size + Remaining r.1 n + 1 ≤ points.size + Remaining used n ∧
  r.2.2.2.2.1.size + Remaining r.1 n + 1 ≤ bridges.size + Remaining used n ∧
  r.2.2.2.1.size + ArcsLeft adj r.1 n + (Row adj v).size ≤ points.size + ArcsLeft adj used n ∧
  r.2.2.2.2.1.size + ArcsLeft adj r.1 n + (Row adj v).size ≤ bridges.size + ArcsLeft adj used n + pref.length ∧
  (pref = [] → r.2.2.2.2.2.2.1 = false ∧ r.2.2.2.2.2.2.2.2 = 0) ∧
  Cells n used ord low r.2.1 r.2.2.1 ∧
  Scanned r.1 pref ∧
  ∃ xs, Discovery n used r.1 visitCount r.2.2.2.2.2.1 r.2.1 xs ∧
    ∀ y ∈ xs, y ≠ v → Scanned r.1 (Row adj y).toList

theorem wp_ite {α : Type} (p : Prop) [Decidable p] (a b : M α) (Q : PostCond α PS) (t : Nat) :
    ((wp (if p then a else b)).apply Q t).down =
      if p then ((wp a).apply Q t).down else ((wp b).apply Q t).down := by
  by_cases h : p <;> simp [h]

theorem wp_run_some {α : Type} (x : M α) (Q : PostCond α PS) (t : Nat)
    (a : α) (t' : Nat) (h : x.run t = some (a, t')) :
    ((wp x).apply Q t).down ↔ (Q.1 a t').down := by
  simp only [wp, PredTrans.apply_pushArg, h]
  rfl

private theorem mem_cursor {α : Type} {l p s : List α} {x : α}
    (h : l = p ++ x :: s) : x ∈ l := by simp [h]

set_option linter.unusedTactic false in
theorem dfs_work {Cost E : Type} [Inhabited E] [Field "to" E Int] (fuel : Nat) :
    ∀ (g : cp.ListGraph Cost E) (v : Nat) (parent : Int)
      (used : Array Bool) (ord low points : Array Int) (bridges : Array (Int × Int)) (visitCount : Int),
      Valid g.adj g.n_.toNat → v < g.n_.toNat → used.size = g.n_.toNat → ord.size = g.n_.toNat → low.size = g.n_.toNat → used[v]! = false →
      Remaining used g.n_.toNat ≤ fuel → ∀ t0,
      ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.lowlink_dfs_rec fuel g v parent used ord low points bridges visitCount
      ⦃⇓ r c => ⌜DfsPost g.adj g.n_.toNat v used ord low points bridges visitCount t0 r c⌝⦄ := by
  induction fuel with
  | zero =>
    intro g v parent used ord low points bridges visitCount valid hv hs hord hlow hf hfuel t0
    have hd := unseen_set (fun _ => 1) used v g.n_.toNat (by omega) hf
    simp only [hv, ite_true] at hd
    exact False.elim (by change Remaining (set used v true) g.n_.toNat + 1 = Remaining used g.n_.toNat at hd; omega)
  | succ f ih =>
    intro g v parent used ord low points bridges visitCount valid hv hs hord hlow hf hfuel t0
    have hg : (⟨g.n_, g.m_, g.adj, g.shortest_path_dist, g.shortest_path_parent⟩ : cp.ListGraph Cost E) = g := rfl
    have hCall (w : Int) (p : Int) (u : Array Bool) (o l a : Array Int) (b : Array (Int × Int)) (cnt : Int)
        (Q : PostCond DfsState PS) :
        ⦃fun c => spred(⌜0 ≤ w ∧ w.toNat < g.n_.toNat ∧ u.size = g.n_.toNat ∧ o.size = g.n_.toNat ∧ l.size = g.n_.toNat ∧ u[w.toNat]! = false ∧
            Remaining u g.n_.toNat ≤ f⌝ ∧ (∀ r t, ⌜DfsPost g.adj g.n_.toNat w.toNat u o l a b cnt c r t⌝ → Q.1 r t))⦄
        cp.ListGraph.lowlink_dfs_rec f ⟨g.n_, g.m_, g.adj, g.shortest_path_dist, g.shortest_path_parent⟩ w p u o l a b cnt ⦃Q⦄ := by
      rw [hg]
      apply Triple.iff.mpr
      intro c h
      obtain ⟨⟨hw0, hw, hu, ho, hl, hfalse, hremain⟩, hq⟩ := h
      have he : (w.toNat : Int) = w := by omega
      have ht (start : Nat) := ih g w.toNat p u o l a b cnt valid hw hu ho hl hfalse hremain start
      have hwP := wp_of_triple (Q := Q) ht
      rw [he] at hwP
      exact (Triple.iff.mp hwP) c hq
    mvcgen [cp.ListGraph.lowlink_dfs_rec, hCall]
    case inv1 =>
      exact ⟨fun ⟨xs, r⟩ c => ⌜LoopInv g.adj g.n_.toNat v used ord low points bridges visitCount t0 xs.prefix r c⌝, ExceptConds.false⟩
    all_goals simp +zetaDelta only [SPred.down_pure] at *
    case vc1.step.isTrue =>
      have hI := ‹LoopInv _ _ _ _ _ _ _ _ _ _ _ _ _›
      have hmem := mem_cursor ‹(get g.adj (v : Int)).toList = _ ++ _ :: _›
      obtain ⟨hw0, hw⟩ := valid v hv _ hmem
      obtain ⟨hs', hv', hmono, hr, hwork, ha, hb, hpa, hba, hblank, hcells, hscanned, hdisc⟩ := hI
      refine ⟨⟨hw0, hw, hs', hcells.orderSize, hcells.lowSize, ?_, by omega⟩, ?_⟩
      · simpa [get_eq] using ‹(!get _ _) = true›
      · intro res t hy
        simp only [wp_ite]
        split <;> split <;> refine (wp_run_some _ _ _ _ _ rfl).mpr ?_
        all_goals
          simp only [SPred.down_pure]
          have hwork' := hy.work
          have hpoints' := hy.pointsCount
          have hbridges' := hy.bridgesCount
          have hrem' := hy.decrease
          have hpa' := hy.pointArcs
          have hba' := hy.bridgeArcs
          obtain ⟨xs, hxs, hclosed⟩ := hdisc
          obtain ⟨ys, hys, hnewClosed⟩ := hy.log
          have hnew := hxs.append hys hy.cells
          refine ⟨hy.size, hy.monotone v hv', fun j h => hy.monotone j (hmono j h), ?_, ?_, ?_, ?_, ?_, ?_, by simp,
            (hcells.trans hy.cells hmono).updateLow hv hf _, (hscanned.mono hy.monotone).step hy.marked,
            xs ++ ys, hnew, ?_⟩
          case refine_7 =>
            intro y hy' hne
            rcases List.mem_append.mp hy' with hx | hyy
            · exact (hclosed y hx hne).mono hy.monotone
            · exact hnewClosed y hyy
          all_goals simp only [Array.size_push, List.length_append, List.length_singleton]
          all_goals (try dsimp only)
          all_goals omega
    case vc4.succ.pre =>
      have hn : v < used.size := by omega
      have hmark := get_marked used v hn
      have hrem := unseen_set (fun _ => 1) used v g.n_.toNat hn hf
      have hbud := unseen_set (Weight g.adj) used v g.n_.toNat hn hf
      have harc := unseen_set (fun i => (Row g.adj i).size) used v g.n_.toNat hn hf
      simp only [hv, ite_true] at hrem hbud harc
      change Remaining (set used v true) g.n_.toNat + 1 = Remaining used g.n_.toNat at hrem
      change Budget g.adj (set used v true) g.n_.toNat + Weight g.adj v = Budget g.adj used g.n_.toNat at hbud
      change ArcsLeft g.adj (set used v true) g.n_.toNat + (Row g.adj v).size =
        ArcsLeft g.adj used g.n_.toNat at harc
      refine ⟨by simpa using hs, hmark.1, hmark.2, by dsimp only; omega, ?_, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, (by simp), Cells.enter _ _ _ _ _ _ _ hv hf hord hlow, (by simp [Scanned]),
        [v], Discovery.single _ _ _ _ _ hv hs hord hf, ?_⟩
      rotate_left
      · intro j hj hne
        exact False.elim (hne (by simpa using hj))
      dsimp only [List.length_nil, Nat.mul_zero, Nat.add_zero, Weight] at hbud ⊢
      omega
    case vc9.succ.post.except =>
      simp
    case vc2.step.isFalse.isTrue =>
      obtain ⟨hs', hv', hmono, hr, hwork, ha, hb, hpa, hba, hblank, hcells, hscanned, hdisc⟩ := ‹LoopInv _ _ _ _ _ _ _ _ _ _ _ _ _›
      refine ⟨hs', hv', hmono, hr, ?_, ha, hb, hpa, ?_, by simp, hcells, hscanned.step (by simpa [get_eq] using ‹¬(!get _ _) = true›), hdisc⟩
      all_goals simp only [List.length_append, List.length_singleton]
      all_goals omega
    case vc3.step.isFalse.isFalse =>
      obtain ⟨hs', hv', hmono, hr, hwork, ha, hb, hpa, hba, hblank, hcells, hscanned, hdisc⟩ := ‹LoopInv _ _ _ _ _ _ _ _ _ _ _ _ _›
      refine ⟨hs', hv', hmono, hr, ?_, ha, hb, hpa, ?_, by simp, hcells.updateLow hv hf _, hscanned.step (by simpa [get_eq] using ‹¬(!get _ _) = true›), hdisc⟩
      all_goals simp only [List.length_append, List.length_singleton]
      all_goals omega
    all_goals
      obtain ⟨hs', hv', hmono, hr, hwork, ha, hb, hpa, hba, hblank, hcells, hscanned, hdisc⟩ := ‹LoopInv _ _ _ _ _ _ _ _ _ _ _ _ _›
      refine DfsPost.mk hs' hv' hmono (by (try dsimp only); omega) ?_ ?_ hb ?_ ?_ hcells ?_
      · simp only [get_eq, Int.toNat_natCast, Array.length_toList] at hwork
        change _ + 1 + _ + 2 * g.adj[v]!.size ≤ _ + _ + 2 * g.adj[v]!.size at hwork
        try dsimp only
        omega
      · simp only [Array.size_push]
        omega
      · simp only [Array.size_push]
        first
        | omega
        | have hnonempty : 0 < (Row g.adj v).size := by
            by_contra hn
            have hr0 : (get g.adj (v : Int)).toList = [] := by
              apply List.eq_nil_of_length_eq_zero
              simp only [Array.length_toList, get_eq, Int.toNat_natCast]
              change (Row g.adj v).size = 0
              omega
            obtain ⟨hnFlag, hnCount⟩ := hblank hr0
            first
            | have hc := ‹(decide (parent = -1) && decide _) = true›
              simp [hnCount] at hc
            | simp_all only [Bool.false_eq_true]
          omega
      · simp only [Array.length_toList, get_eq, Int.toNat_natCast] at hba
        change _ + _ + (Row g.adj v).size ≤ _ + _ + (Row g.adj v).size at hba
        try dsimp only
        omega
      · obtain ⟨xs, hdisc, hclosed⟩ := hdisc
        refine ⟨xs, hdisc, fun y hy => ?_⟩
        by_cases he : y = v
        · subst y
          exact hscanned
        · exact hclosed y hy he


def arcCount {E : Type} [Inhabited E] (adj : Array (Array E)) : Nat → Nat
  | 0 => 0
  | k+1 => arcCount adj k + (Row adj k).size

theorem remaining_le (used : Array Bool) (n : Nat) : Remaining used n ≤ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change Remaining used k + (if used[k]! then 0 else 1) ≤ k + 1
    split <;> omega

theorem budget_le {E : Type} [Inhabited E] (adj : Array (Array E)) (used : Array Bool) (n : Nat) :
    Budget adj used n ≤ 2 * n + 2 * arcCount adj n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change Budget adj used k + (if used[k]! then 0 else Weight adj k) ≤
      2 * (k + 1) + 2 * (arcCount adj k + (Row adj k).size)
    split <;> (try dsimp only [Weight]) <;> omega

theorem arcsLeft_le {E : Type} [Inhabited E] (adj : Array (Array E)) (used : Array Bool) (n : Nat) :
    ArcsLeft adj used n ≤ arcCount adj n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change ArcsLeft adj used k + (if used[k]! then 0 else (Row adj k).size) ≤
      arcCount adj k + (Row adj k).size
    split <;> omega

theorem sortCost_mono {k n : Nat} (h : k ≤ n) : sortCost k ≤ sortCost n := by
  by_cases hk : k = 0
  · simp [hk, sortCost]
  have hn : n ≠ 0 := by omega
  have hlog : k.log2 ≤ n.log2 := (Nat.le_log2 hn).mpr (Nat.le_trans (Nat.log2_self_le hk) h)
  exact Nat.mul_le_mul h (by omega)

def RootsInv {E : Type} [Inhabited E] (adj : Array (Array E)) (n t0 k : Nat) (r : DfsState) (t : Nat) : Prop :=
  r.1.size = n ∧ r.2.1.size = n ∧ r.2.2.1.size = n ∧
  (∀ i : Nat, i < k → r.1[i]! = true) ∧
  t + Budget adj r.1 n ≤ t0 + 1 + 5 * n + k + 2 * arcCount adj n ∧
  r.2.2.2.1.size + Remaining r.1 n ≤ n ∧
  r.2.2.2.2.1.size + Remaining r.1 n ≤ n ∧
  r.2.2.2.1.size + ArcsLeft adj r.1 n ≤ arcCount adj n ∧
  r.2.2.2.2.1.size + ArcsLeft adj r.1 n ≤ arcCount adj n

private theorem seen_succ {n i : Int} {pref suff : List Int} {u : Array Bool}
    (h : range 0 n = pref ++ i :: suff) (hp : ∀ j : Nat, j < pref.length → u[j]! = true)
    (hi : u[i.toNat]! = true) : ∀ j : Nat, j < (pref ++ [i]).length → u[j]! = true := by
  have hc := range_cursor h
  intro j hj
  by_cases before : j < pref.length
  · exact hp j before
  · simp only [List.length_append, List.length_singleton] at hj
    have he : j = i.toNat := by simp only [Int.zero_add] at hc; omega
    rwa [he]

private theorem sort_sizes (a : Array Int) (b : Array (Int × Int)) :
    (sort a).size = a.size ∧ (sortLex b).size = b.size := by
  constructor
  · simp [sort, (List.mergeSort_perm a.toList (fun x y => !decide (y < x))).length_eq]
  · simp [sortLex, (List.mergeSort_perm b.toList (fun x y => !decide (Prod.lexLt y x))).length_eq]

/-- All rows are searched in linear work. Either output is bounded by the number of
vertices and by the number of arcs, so the separate sorts also respect sparse inputs. -/
theorem lowlink_work {Cost E : Type} [Inhabited E] [Field "to" E Int]
    (g : cp.ListGraph Cost E) (hsmall : g.n_.toNat ≤ Cpp.fuel)
    (valid : Valid g.adj g.n_.toNat) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.ListGraph.lowlink g
    ⦃⇓ r c => ⌜r.2 = g ∧ r.1.1.size ≤ min g.n_.toNat (arcCount g.adj g.n_.toNat) ∧
      r.1.2.size ≤ min g.n_.toNat (arcCount g.adj g.n_.toNat) ∧
      c ≤ t0 + 1 + 6 * g.n_.toNat + 2 * arcCount g.adj g.n_.toNat + 2 * sortCost (min g.n_.toNat (arcCount g.adj g.n_.toNat))⌝⦄ := by
  have hg : (⟨g.n_, g.m_, g.adj, g.shortest_path_dist, g.shortest_path_parent⟩ : cp.ListGraph Cost E) = g := rfl
  have hCall (w : Int) (p : Int) (u : Array Bool) (o l a : Array Int) (b : Array (Int × Int)) (cnt : Int)
      (Q : PostCond DfsState PS) :
      ⦃fun c => spred(⌜0 ≤ w ∧ w.toNat < g.n_.toNat ∧ u.size = g.n_.toNat ∧ o.size = g.n_.toNat ∧ l.size = g.n_.toNat ∧ u[w.toNat]! = false⌝ ∧
          (∀ r t, ⌜DfsPost g.adj g.n_.toNat w.toNat u o l a b cnt c r t⌝ → Q.1 r t))⦄
      cp.ListGraph.lowlink_dfs ⟨g.n_, g.m_, g.adj, g.shortest_path_dist, g.shortest_path_parent⟩ w p u o l a b cnt
      ⦃Q⦄ := by
    rw [hg]
    unfold cp.ListGraph.lowlink_dfs
    apply Triple.iff.mpr
    intro c h
    obtain ⟨⟨hw0, hw, hu, ho, hl, hfalse⟩, hq⟩ := h
    have he : (w.toNat : Int) = w := by omega
    have ht (start : Nat) := dfs_work Cpp.fuel g w.toNat p u o l a b cnt valid hw hu ho hl hfalse
      (Nat.le_trans (remaining_le u _) hsmall) start
    have hwP := wp_of_triple (Q := Q) ht
    rw [he] at hwP
    exact (Triple.iff.mp hwP) c hq
  mvcgen [cp.ListGraph.lowlink, hCall]
  case inv1 =>
    exact ⟨fun ⟨xs, r⟩ c => ⌜RootsInv g.adj g.n_.toNat t0 xs.prefix.length r c⌝, ExceptConds.false⟩
  all_goals simp +zetaDelta only [SPred.down_pure] at *
  case vc1.step.isTrue =>
    have hcursor := ‹range 0 g.n_ = _ ++ _ :: _›
    have hrange := range_cursor hcursor
    have hbnd := range_prefix_length hcursor
    simp only [Int.zero_add, Int.sub_zero] at hrange hbnd
    obtain ⟨hs, ho, hl, hp, hwork, ha, hb, hapa, hba⟩ := ‹RootsInv _ _ _ _ _ _›
    refine ⟨⟨by omega, by omega, hs, ho, hl, by simpa [get_eq] using ‹(!get _ _) = true›⟩, ?_⟩
    intro res t hy
    refine (wp_run_some _ _ _ _ _ rfl).mpr ?_
    change RootsInv _ _ _ _ _ _
    have hwork' := hy.work
    have ha' := hy.pointsCount
    have hb' := hy.bridgesCount
    have hpa' := hy.pointArcs
    have hba' := hy.bridgeArcs
    refine ⟨hy.size, hy.cells.orderSize, hy.cells.lowSize, seen_succ hcursor (fun j hj => hy.monotone j (hp j hj)) hy.marked, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try dsimp only)
    all_goals (try simp only [List.length_append, List.length_singleton])
    all_goals omega
  case vc2.step.isFalse =>
    have hcursor := ‹range 0 g.n_ = _ ++ _ :: _›
    obtain ⟨hs, ho, hl, hp, hwork, ha, hb, hapa, hba⟩ := ‹RootsInv _ _ _ _ _ _›
    refine ⟨hs, ho, hl, seen_succ hcursor hp (by simpa [get_eq] using ‹¬(!get _ _) = true›), ?_, ha, hb, hapa, hba⟩
    simp only [List.length_append, List.length_singleton]
    omega
  case vc3.pre =>
    have hb := budget_le g.adj (replicate g.n_ false) g.n_.toNat
    have hr := remaining_le (replicate g.n_ false) g.n_.toNat
    have hArcs := arcsLeft_le g.adj (replicate g.n_ false) g.n_.toNat
    refine ⟨by simp [replicate], by simp [replicate], by simp [replicate], fun _ h => False.elim (Nat.not_lt_zero _ h), ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try dsimp only)
    all_goals (try simp only [List.length_nil, Array.size_empty])
    all_goals omega
  case vc4.post.success =>
    obtain ⟨hs, ho, hl, hp, hwork, ha, hb, hapa, hba⟩ := ‹RootsInv _ _ _ _ _ _›
    simp only [range_length, Int.sub_zero] at hwork
    have ha' : _ ≤ g.n_.toNat := Nat.le_trans (Nat.le_add_right _ _) ha
    have hb' : _ ≤ g.n_.toNat := Nat.le_trans (Nat.le_add_right _ _) hb
    have ha'' : _ ≤ arcCount g.adj g.n_.toNat := Nat.le_trans (Nat.le_add_right _ _) hapa
    have hb'' : _ ≤ arcCount g.adj g.n_.toNat := Nat.le_trans (Nat.le_add_right _ _) hba
    have hsA := sortCost_mono (Nat.le_min.mpr ⟨ha', ha''⟩)
    have hsB := sortCost_mono (Nat.le_min.mpr ⟨hb', hb''⟩)
    refine ⟨trivial, ?_, ?_, by omega⟩
    · rw [(sort_sizes _ (Array.empty : Array (Int × Int))).1]
      exact Nat.le_min.mpr ⟨ha', ha''⟩
    · rw [(sort_sizes (Array.empty : Array Int) _).2]
      exact Nat.le_min.mpr ⟨hb', hb''⟩
  case vc5.post.except => simp

end Proofs.Cpp.ListLowlink
