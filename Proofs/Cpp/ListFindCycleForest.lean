import Proofs.Cpp.ListFindCycleSearch
import Proofs.Cpp.FindCycle

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FindCycleInv Proofs.FindCycleStep Proofs.FindCyclePhi
open Proofs.LowlinkInv (upd upd_same upd_ne AdjH)
open Proofs.LowlinkMultigraph (offsets endpoints)

namespace Proofs.Cpp.ListFindCycle

variable {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]

local notation "n[" g "]" => Array.size (cp.ListGraph.adj g)
local notation "hd[" g "]" => offsets (directedRows g)
local notation "tg[" g "]" => endpoints (directedRows g)

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem tickN_run (n t : Nat) : (tickN n).run t = some ((), t + n) := rfl
private theorem pure_run {α : Type} (x : α) (t : Nat) : (pure x : M α).run t = some (x, t) := rfl
private theorem some_bind {α β : Type} (x : α) (f : α → Option β) : (some x >>= f) = f x := rfl

def rootStep (g : cp.ListGraph Cost E) (v : Int) (s : SearchResult E) : M (ForInStep (SearchResult E)) := do
  tick
  if !(decide (get s.1 v ≠ 0)) then
    let r ← cp.ListGraph.find_cycle_dfs g v s.1 s.2.1 s.2.2
    return .yield (r.1, r.2.1, r.2.2)
  else
    return .yield (s.1, s.2.1, s.2.2)

private theorem root_skip (g : cp.ListGraph Cost E) (v : Nat) (s : SearchResult E) (t : Nat)
    (h : get s.1 (v : Int) ≠ 0) :
    (rootStep g (v : Int) s).run t = some (.yield s, t + 1) := by
  unfold rootStep
  have hskip : ¬ (!decide (get s.1 (v : Int) ≠ 0)) = true := by rw [decide_eq_true h]; decide
  rw [ite_eq_right hskip]
  rfl

private theorem root_take (g : cp.ListGraph Cost E) (v : Nat) (s : SearchResult E) (t : Nat)
    (h : get s.1 (v : Int) = 0) :
    (rootStep g (v : Int) s).run t =
      ((cp.ListGraph.find_cycle_dfs_rec fuel g (v : Int) s.1 s.2.1 s.2.2).run (t + 1)).map
        (fun p => (.yield p.1, p.2)) := by
  unfold rootStep cp.ListGraph.find_cycle_dfs
  rw [h]
  simp only [ne_self_iff_false, decide_false, Bool.not_false, ite_true, StateT.run_bind, tick_run, some_bind,
    pure_run]
  cases (cp.ListGraph.find_cycle_dfs_rec fuel g (v : Int) s.1 s.2.1 s.2.2).run (t + 1) <;> rfl

private theorem roots_cons (g : cp.ListGraph Cost E) (v : Nat) (roots : List Nat)
    (s s' : SearchResult E) (t t' : Nat)
    (h : (rootStep g (v : Int) s).run t = some (.yield s', t')) :
    (forIn ((v :: roots).map (Int.ofNat)) s (rootStep g)).run t =
      (forIn (roots.map (Int.ofNat)) s' (rootStep g)).run t' := by
  change (rootStep g (Int.ofNat v) s).run t = _ at h
  rw [List.map_cons, List.forIn_cons, StateT.run_bind, h]
  rfl

private theorem retain_cycle_at_fuel (g : cp.ListGraph Cost E) (v : Nat) (s : SearchResult E)
    (hcycle : s.2.2.size ≠ 0) (t : Nat) :
    (cp.ListGraph.find_cycle_dfs_rec fuel g (v : Int) s.1 s.2.1 s.2.2).run t =
      some ((set (set s.1 (v : Int) 1) (v : Int) 2, s.2.1, s.2.2),
        t + 1 + (if (get g.adj (v : Int)).toList.isEmpty then 0 else 1)) := by
  exact retain_cycle (fuel - 1) g (v : Int) s.1 s.2.1 s.2.2 hcycle t

private theorem roots_retain_cycle (g : cp.ListGraph Cost E) (roots : List Nat) :
    ∀ (s : SearchResult E) (t : Nat), s.2.2.size ≠ 0 →
      ∃ res t', (forIn (roots.map Int.ofNat) s (rootStep g)).run t = some (res, t') ∧
        res.2.2 = s.2.2 ∧ t' ≤ t + 3 * roots.length := by
  induction roots with
  | nil => intro s t _; exact ⟨s, t, rfl, rfl, by simp⟩
  | cons v roots ih =>
    intro s t hcycle
    by_cases hwhite : get s.1 (v : Int) = 0
    · let extra := if (get g.adj (v : Int)).toList.isEmpty then 0 else 1
      let next : SearchResult E := (set (set s.1 (v : Int) 1) (v : Int) 2, s.2.1, s.2.2)
      have hb : extra ≤ 1 := by
        change (if (get g.adj (v : Int)).toList.isEmpty then (0 : Nat) else 1) ≤ 1
        by_cases hempty : (get g.adj (v : Int)).toList.isEmpty = true
        · rw [ite_eq_left hempty]; omega
        · rw [ite_eq_right hempty]
      have hx := root_take g v s t hwhite
      rw [retain_cycle_at_fuel g v s hcycle (t + 1)] at hx
      have hs := roots_cons g v roots s next t (t + 1 + 1 + extra) hx
      obtain ⟨r, t', hrun, hsame, htime⟩ := ih next (t + 1 + 1 + extra) hcycle
      exact ⟨r, t', hs.trans hrun, hsame, by simp only [List.length_cons]; omega⟩
    · have hs := roots_cons g v roots s s t (t + 1) (root_skip g v s t hwhite)
      obtain ⟨r, t', hrun, hsame, htime⟩ := ih s (t + 1) hcycle
      exact ⟨r, t', hs.trans hrun, hsame, by simp only [List.length_cons]; omega⟩

structure ForestComplete (g : cp.ListGraph Cost E) (start result : FS) (roots : List Nat)
    (res : SearchResult E) (t t' : Nat) : Prop where
  empty : res.2.2 = Array.empty
  inv : Invariant g result
  active : Active g res.1 res.2.1 result
  depth : result.sp = 0
  preserved : VisitedPersists start result
  reached : ∀ v ∈ roots, result.C v ≠ 0
  work : t' + reserve g result ≤ t + 3 * roots.length + reserve g start

theorem scan_roots (g : cp.ListGraph Cost E) (valid : ValidGraph g) (hfuel : n[g] < fuel)
    (roots : List Nat) (hrange : ∀ v ∈ roots, v < n[g]) :
    ∀ visited parents st t, Invariant g st → Active g visited parents st → st.sp = 0 →
      ∃ (res : SearchResult E) (t' : Nat),
        (forIn (roots.map Int.ofNat) (visited, parents, Array.empty) (rootStep g)).run t = some (res, t') ∧
        ((∃ after, ForestComplete g st after roots res t t') ∨
          (CycleWitness g res.2.2.toList ∧ t' ≤ t + 3 * roots.length + reserve g st + 5 + 3 * n[g])) := by
  induction roots with
  | nil =>
    intro visited parents st t inv active hsp
    exact ⟨_, _, rfl, .inl ⟨st, rfl, inv, active, hsp, fun _ h => h, by simp, by simp⟩⟩
  | cons v roots ih =>
    intro visited parents st t inv active hsp
    have hv := hrange v (by simp)
    have htail : ∀ w ∈ roots, w < n[g] := fun w hw => hrange w (List.mem_cons_of_mem _ hw)
    let s : SearchResult E := (visited, parents, Array.empty)
    have hcolor := active.color v hv
    by_cases hwhite : st.C v = 0
    · let start := fRoot hd[g] st v
      have hi : Invariant g start := inv_root (directed_graph_view g valid) inv hsp hv hwhite
      have ha : Active g (set visited (v : Int) 1) parents start := active.enter_root hd[g] hv
      have hsz : start.sp = 1 := rfl
      have htop : start.Sk (start.sp - 1) = v := by
        change upd st.Sk 0 v 0 = v
        exact upd_same _ _ _
      have hIt : start.It v = (hd[g] v : Int) := upd_same _ _ _
      have hres : reserve g start ≤ reserve g st := Nat.mul_le_mul_left 2 (phiF_root n[g] hd[g] st v hv hwhite hsp)
      have hsC : start.C v = 1 := upd_same _ _ _
      obtain ⟨mid, tm, hsearch, hout⟩ := recursive_search g valid hfuel fuel v visited parents start (t + 1)
        ⟨hi, ha, by omega, htop, hIt, by omega⟩
      have hstep := root_take g v s t (hcolor.trans hwhite)
      change _ = ((cp.ListGraph.find_cycle_dfs_rec fuel g (v : Int) visited parents Array.empty).run (t + 1)).map _ at hstep
      rw [hsearch] at hstep
      have hscan := roots_cons g v roots s mid t tm hstep
      rcases hout with ⟨after, hpost⟩ | hfound
      · have hdepth : after.sp = 0 := by rw [hpost.height, hsz]
        have hseen : VisitedPersists st after := (persists_with_update (by decide : (1 : Int) ≠ 0)
          (show start.C = upd st.C v 1 from rfl)).trans hpost.seen
        have hvseen : after.C v ≠ 0 := hpost.seen v (by omega)
        obtain ⟨r, tr, hrun, hret⟩ := ih htail mid.1 mid.2.1 after tm hpost.result hpost.active hdepth
        refine ⟨r, tr, hscan.trans (by simpa only [← hpost.empty] using hrun), ?_⟩
        have hwork := hpost.work
        rcases hret with ⟨final, hf⟩ | ⟨witness, budget⟩
        · have hfw := hf.work
          refine .inl ⟨final, hf.empty, hf.inv, hf.active, hf.depth, hseen.trans hf.preserved, ?_, ?_⟩
          · intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · exact hf.preserved _ hvseen
            · exact hf.reached w hw
          · simp only [List.length_cons]; omega
        · exact .inr ⟨witness, by simp only [List.length_cons]; omega⟩
      · obtain ⟨witness, bound⟩ := hfound
        obtain ⟨r, tr, hrun, hsame, hwork⟩ := roots_retain_cycle g roots mid tm witness.positive
        exact ⟨r, tr, hscan.trans hrun, .inr ⟨by simpa only [hsame] using witness, by simp only [List.length_cons]; omega⟩⟩
    · have hskip := root_skip g v s t (by simpa [s, hcolor] using hwhite)
      have hscan := roots_cons g v roots s s t (t + 1) hskip
      obtain ⟨r, tr, hrun, hret⟩ := ih htail visited parents st (t + 1) inv active hsp
      refine ⟨r, tr, hscan.trans hrun, ?_⟩
      rcases hret with ⟨final, hf⟩ | ⟨witness, budget⟩
      · have hwork := hf.work
        refine .inl ⟨final, hf.empty, hf.inv, hf.active, hf.depth, hf.preserved, ?_, ?_⟩
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact hf.preserved _ hwhite
          · exact hf.reached w hw
        · simp only [List.length_cons]; omega
      · exact .inr ⟨witness, by simp only [List.length_cons]; omega⟩

end Proofs.Cpp.ListFindCycle

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FindCycleInv Proofs.FindCyclePhi
open Proofs.LowlinkInv (AdjH)
open Proofs.LowlinkMultigraph (offsets endpoints)
open Proofs.PrimMath (Rtc)

namespace Proofs.Cpp.ListFindCycle

variable {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]

local notation "n[" g "]" => Array.size (cp.ListGraph.adj g)
local notation "hd[" g "]" => offsets (directedRows g)
local notation "tg[" g "]" => endpoints (directedRows g)

/-- Number of actual adjacency entries, including entries inserted through the mutable row API. -/
abbrev arcCount (g : cp.ListGraph Cost E) : Nat := hd[g] n[g]

def Acyclic (g : cp.ListGraph Cost E) : Prop :=
  ∀ v w, AdjH hd[g] tg[g] v w → ¬ Rtc (AdjH hd[g] tg[g]) w v

omit [Inhabited E] in
theorem CycleWitness.length_le (g : cp.ListGraph Cost E) (valid : ValidGraph g) (cycle : Array E)
    (h : CycleWitness g cycle.toList) : cycle.size ≤ n[g] := by
  obtain ⟨first, rest, hfrom, _, hn, inGraph⟩ := h
  have hsub : first :: rest ⊆ (List.range n[g]).map Int.ofNat := by
    intro v hv
    rw [← hfrom] at hv
    obtain ⟨edge, he, heq⟩ := List.mem_map.mp hv
    obtain ⟨u, hu, hed⟩ := inGraph edge he
    exact List.mem_map.mpr ⟨u, List.mem_range.mpr hu, ((valid.row u hu edge hed).1.symm.trans heq)⟩
  have hlen := List.Nodup.length_le_of_subset hn hsub
  rw [← hfrom] at hlen
  simpa using hlen

section Constructor
variable [ConstructState E] [Construct E (Int × Int × Unit)]

theorem entry_run (g : cp.ListGraph Cost E) (st st' : ConstructState.State E) (sentinel : E) (t tc : Nat)
    (hmake : (Construct.make (E := E) ((-1 : Int), (-1 : Int), ()) st).run (t + 1 + g.n_.toNat) =
      some ((sentinel, st'), tc)) :
    (cp.ListGraph.find_cycle_directed g st).run t =
      ((forIn (range 0 g.n_) (replicate g.n_ 0, replicate g.n_ sentinel, Array.empty) (rootStep g)).run
        (tc + g.n_.toNat)).map (fun r => ((r.1.2.2, st', g), r.2)) := by
  simp only [cp.ListGraph.find_cycle_directed, StateT.run_bind, tick_run, tickN_run, pure_run,
    some_bind, hmake]
  conv_lhs =>
    enter [1, 1, 3, v, s]
    change rootStep g v s
  let loop := (forIn (range 0 g.n_) (replicate g.n_ 0, replicate g.n_ sentinel, Array.empty)
    (rootStep g)).run (tc + g.n_.toNat)
  change (loop >>= fun r => some ((r.1.2.2, st', g), r.2)) =
    loop.map (fun r => ((r.1.2.2, st', g), r.2))
  cases loop <;> rfl

/-- The generated entry point preserves the graph and the edge construction state and returns
an exact simple cycle, or an empty array with a proof of acyclicity. -/
theorem directed_cycle_spec (g : cp.ListGraph Cost E) (valid : ValidGraph g) (hfuel : n[g] < fuel)
    (st st' : ConstructState.State E) (sentinel : E) (t tc : Nat)
    (hmake : (Construct.make (E := E) ((-1 : Int), (-1 : Int), ()) st).run (t + 1 + g.n_.toNat) =
      some ((sentinel, st'), tc)) :
    ∃ (cycle : Array E) (t' : Nat),
      (cp.ListGraph.find_cycle_directed g st).run t = some ((cycle, st', g), t') ∧
      (cycle.size = 0 ∧ Acyclic g ∨ CycleWitness g cycle.toList) ∧
      cycle.size ≤ n[g] ∧ t' ≤ tc + 9 * n[g] + 2 * arcCount g + 5 := by
  let start := FindCycle.initF Array.empty
  let visited : Array Int := replicate g.n_ 0
  let parents : Array E := replicate g.n_ sentinel
  have hinit : Invariant g start := FindCycle.inv_initF n[g] hd[g] tg[g] Array.empty
  have hactive : Active g visited parents start := by
    refine ⟨by simp [visited, replicate, valid.size_eq], by simp [parents, replicate, valid.size_eq], ?_, ?_⟩
    · intro v hv
      simp [visited, replicate, valid.size_eq, get_eq, getElem!_pos, hv, start, FindCycle.initF]
    · intro j hj
      change j + 1 < 0 at hj
      omega
  have hstart : start.sp = 0 := rfl
  have hlen : g.n_.toNat = n[g] := by rw [valid.size_eq]; simp
  have hroots : range 0 g.n_ = (List.range n[g]).map Int.ofNat := by
    change range 0 g.n_ = (List.range n[g]).map (fun k : Nat => (k : Int))
    simpa only [size, ← valid.size_eq] using range_zero_size g.adj
  have hb : reserve g start = 2 * (arcCount g + n[g]) := by
    have htel := FindCycle.tele hd[g] n[g] (directed_graph_view g valid).mono
    have hzero : hd[g] 0 = 0 := rfl
    have hsum : ((List.range n[g]).map (fun a => hd[g] (a + 1) - hd[g] a)).sum = arcCount g := by
      simpa only [hzero, Nat.add_zero] using htel
    simp [reserve, phiF, whiteF, unscF, itNF, start, FindCycle.initF, hsum]
  obtain ⟨res, t', hrun, hret⟩ := scan_roots g valid hfuel (List.range n[g])
    (fun _ h => List.mem_range.mp h) visited parents start (tc + n[g]) hinit hactive hstart
  have actual := entry_run g st st' sentinel t tc hmake
  rw [hroots, hlen] at actual
  change (cp.ListGraph.find_cycle_directed g st).run t =
    ((forIn ((List.range n[g]).map Int.ofNat) (visited, parents, Array.empty) (rootStep g)).run (tc + n[g])).map _ at actual
  rw [hrun] at actual
  refine ⟨res.2.2, t', actual, ?_⟩
  rcases hret with ⟨after, hc⟩ | ⟨hw, ht⟩
  · have hac := Proofs.FindCycleSpec.acyclic_of_done (directed_graph_view g valid) hc.inv hc.depth
      (fun v hv => hc.reached v (List.mem_range.mpr hv))
    have hwork := hc.work
    rw [hb, List.length_range] at hwork
    rw [hc.empty]
    exact ⟨.inl ⟨rfl, hac⟩, Nat.zero_le _, by omega⟩
  · rw [List.length_range, hb] at ht
    exact ⟨.inr hw, hw.length_le g valid _, by omega⟩

end Constructor

end Proofs.Cpp.ListFindCycle
