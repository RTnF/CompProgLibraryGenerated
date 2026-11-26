import Proofs.Cpp.ListFindCycleScan
import Proofs.Math.FindCyclePhi

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FindCycleInv Proofs.FindCycleStep Proofs.FindCyclePhi
open Proofs.LowlinkInv (upd upd_same upd_ne)
open Proofs.LowlinkMultigraph (offsets endpoints)

namespace Proofs.Cpp.ListFindCycle

variable {Cost E : Type} [Inhabited E] [Field "from" E Int] [Field "to" E Int]

local notation "n[" g "]" => Array.size (cp.ListGraph.adj g)
local notation "hd[" g "]" => offsets (directedRows g)
local notation "tg[" g "]" => endpoints (directedRows g)

abbrev Invariant (g : cp.ListGraph Cost E) (st : FS) := FInv n[g] hd[g] tg[g] st
abbrev reserve (g : cp.ListGraph Cost E) (st : FS) := 2 * phiF n[g] hd[g] st

def CycleReturn (g : cp.ListGraph Cost E) (before : FS) (cycle : Array E) (t t' margin : Nat) : Prop :=
  CycleWitness g cycle.toList ∧ t' + before.sp ≤ t + reserve g before + margin + 3 * n[g]

structure RowComplete (g : cp.ListGraph Cost E) (before after : FS) (v : Nat)
    (res : RowState E) (t t' : Nat) : Prop where
  no_return : res.1 = none
  empty : res.2.2.2 = Array.empty
  result : Invariant g after
  active : Active g res.2.1 res.2.2.1 after
  height : after.sp = before.sp
  top : after.Sk (after.sp - 1) = v
  preserved : Parked (before.sp - 1) before after
  seen : VisitedPersists before after
  scanned : AtCursor g after v []
  work : t' + reserve g after ≤ t + reserve g before

structure SearchComplete (g : cp.ListGraph Cost E) (before after : FS)
    (res : SearchResult E) (t t' : Nat) : Prop where
  empty : res.2.2 = Array.empty
  result : Invariant g after
  active : Active g res.1 res.2.1 after
  height : after.sp = before.sp - 1
  preserved : Parked (before.sp - 1) before after
  seen : VisitedPersists before after
  work : t' + reserve g after ≤ t + reserve g before

private theorem tick_run (t : Nat) : tick.run t = some ((), t + 1) := rfl
private theorem pure_run {α : Type} (x : α) (t : Nat) : (pure x : M α).run t = some (x,t) := rfl
private theorem some_bind {α β : Type} (x : α) (f : α → Option β) : (some x >>= f) = f x := rfl

omit [Inhabited E] in
private theorem range_edge (g : cp.ListGraph Cost E) (valid : ValidGraph g) (v : Nat)
    (hv : v < n[g]) (edge : E) (he : edge ∈ edgesAt g v) :
    (let w := (Field.get (member := "to") edge : Int).toNat
     (w : Int) = Field.get (member := "to") edge ∧ w < n[g]) := by
  have ⟨_, hn, hb⟩ := valid.row v hv edge he
  rw [valid.size_eq] at hb
  dsimp only
  omega

omit [Inhabited E] [Field "from" E Int] in
private theorem reserve_height (g : cp.ListGraph Cost E) (s : FS) : s.sp ≤ reserve g s := by
  unfold reserve phiF
  omega

private theorem forIn_cons_yield (g : cp.ListGraph Cost E) (r : Nat) (v : Int) (edge : E) (row : List E)
    (s s' : RowState E) (t t' : Nat)
    (h : (rowStep g r v edge s).run t = some (.yield s', t')) :
    (forIn (edge :: row) s (rowStep g r v)).run t = (forIn row s' (rowStep g r v)).run t' := by
  rw [List.forIn_cons, StateT.run_bind, h]
  rfl

private theorem forIn_cons_done (g : cp.ListGraph Cost E) (r : Nat) (v : Int) (edge : E) (row : List E)
    (s s' : RowState E) (t t' : Nat)
    (h : (rowStep g r v edge s).run t = some (.done s', t')) :
    (forIn (edge :: row) s (rowStep g r v)).run t = some (s', t') := by
  rw [List.forIn_cons, StateT.run_bind, h]
  rfl

/-- Search from an active vertex. Its entry mark is already reflected in the ghost state. -/
def SearchPre (g : cp.ListGraph Cost E) (lim v : Nat) (visited : Array Int) (parents : Array E) (st : FS) : Prop :=
  Invariant g st ∧ Active g (set visited (v : Int) 1) parents st ∧ 0 < st.sp ∧
    st.Sk (st.sp - 1) = v ∧ st.It v = (hd[g] v : Int) ∧ n[g] + 1 ≤ lim + st.sp

/-- The generated recursive call either finishes its active frame or supplies an exact cycle. -/
def SearchSpec (g : cp.ListGraph Cost E) (lim : Nat) : Prop :=
  ∀ v visited parents st t, SearchPre g lim v visited parents st →
    ∃ (res : SearchResult E) (t' : Nat),
      (cp.ListGraph.find_cycle_dfs_rec lim g (v : Int) visited parents Array.empty).run t = some (res, t') ∧
        ((∃ after, SearchComplete g st after res t t') ∨ CycleReturn g st res.2.2 t t' 5)

/-- Scan an unread suffix of the current row under the induction hypothesis for a child call. -/
theorem scan_row (g : cp.ListGraph Cost E) (valid : ValidGraph g) (hfuel : n[g] < fuel)
    (r : Nat) (rec : SearchSpec g r) (v : Nat) (row : List E) :
    ∀ st (visited : Array Int) (parents : Array E) t,
      Invariant g st → Active g visited parents st → 0 < st.sp → st.Sk (st.sp - 1) = v →
      AtCursor g st v row → n[g] + 1 ≤ (r + 1) + st.sp →
      ∃ (res : RowState E) (t' : Nat),
        (forIn row (none, visited, parents, Array.empty) (rowStep g r (v : Int))).run t = some (res, t') ∧
          ((∃ after, RowComplete g st after v res t t') ∨
            CycleReturn g st (finishRow (v : Int) res).2.2 t t' 4) := by
  induction row with
  | nil =>
    intro st visited parents t inv active hsp top cursor hlim
    exact ⟨_, _, rfl, .inl ⟨st, rfl, rfl, inv, active, rfl, top, Parked.refl _ _, fun _ h => h, cursor, by omega⟩⟩
  | cons edge row ih =>
    intro st visited parents t inv active hsp top cursor hlim
    have hcolored : st.C v = 1 := top_gray inv hsp top
    have hv := inv.c_lt v (by omega)
    obtain ⟨q, hq, hscan, hqto, hedge⟩ := cursor.head hv
    let w := (Field.get (member := "to") edge : Int).toNat
    obtain ⟨hcast, hw⟩ := range_edge g valid v hv edge hedge
    have hcolor := active.color w hw
    rw [hcast] at hcolor
    have hhead := (inv.it_rng v (by omega)).1
    have hlimit : st.It v < (hd[g] (v + 1) : Int) := by omega
    rcases inv.c_rng w with hwhite | hgray | hblack
    · let child := fPush hd[g] st v w
      have hchildInv : Invariant g child := inv_push (directed_graph_view g valid) inv hsp top hq hscan hqto hwhite
      have hchildActive := active.enter_child inv hsp top hw hwhite hedge hcast.symm
      have hchildSp : child.sp = st.sp + 1 := rfl
      have hchildTop : child.Sk (child.sp - 1) = w := by rw [hchildSp, Nat.add_sub_cancel, show child.Sk st.sp = w from upd_same _ _ _]
      have hchildIt : child.It w = (hd[g] w : Int) := upd_same _ _ _
      have hpush := phiF_push n[g] hd[g] st v w hv hw (by omega) hwhite hhead hlimit
      have childReserve : reserve g child + 2 ≤ reserve g st := by
        simpa [reserve, child, Nat.mul_add] using Nat.mul_le_mul_left 2 hpush
      obtain ⟨out, tc, hchild, hpost⟩ := rec w visited (set parents (w : Int) edge) child (t + 1)
        ⟨hchildInv, hchildActive, by omega, hchildTop, hchildIt, by omega⟩
      have hstep := rowStep_white g r (v : Int) edge none visited parents (hcolor.trans hwhite) t
      have hcast' : (w : Int) = Field.get (member := "to") edge := hcast
      rw [← hcast', hchild] at hstep
      have hcons := forIn_cons_yield g r (v : Int) edge row _ (none, out) t tc hstep
      rcases hpost with ⟨after, hdid⟩ | hfound
      · have haSp : after.sp = st.sp := by rw [hdid.height, hchildSp, Nat.add_sub_cancel]
        have hparent := hdid.preserved (st.sp - 1) (by omega)
        have hchildParent : child.Sk (st.sp - 1) = v := (upd_ne _ _ _ _ (by omega)).trans top
        have haTop : after.Sk (after.sp - 1) = v := by rw [haSp, hparent.1, hchildParent]
        have hvw : v ≠ w := by intro he; rw [he, hwhite] at hcolored; contradiction
        have hchildNext : child.It v = st.It v + 1 := by
          change upd (upd st.It v (st.It v + 1)) w (hd[g] w : Int) v = _
          rw [upd_ne _ _ _ _ hvw, upd_same]
        have hNext : after.It v = st.It v + 1 := by
          rw [hchildParent] at hparent
          rw [hparent.2, hchildNext]
        have hcur := cursor.advance hNext
        have hp : Parked (st.sp - 1) st after :=
          (push_parked inv top hwhite).trans (hdid.preserved.lower (by omega))
        have hseen : VisitedPersists st after :=
          (persists_with_update (by decide : (1 : Int) ≠ 0) (show child.C = upd st.C w 1 from rfl)).trans hdid.seen
        obtain ⟨res, tt, hrun, hret⟩ := ih after out.1 out.2.1 tc hdid.result hdid.active (by omega)
          haTop hcur (by omega)
        have hc := hdid.work
        refine ⟨res, tt, hcons.trans (by simpa only [← hdid.empty] using hrun), ?_⟩
        rcases hret with ⟨final, hfinal⟩ | hfinal
        · have hcfinal := hfinal.work
          refine .inl ⟨final, hfinal.no_return, hfinal.empty, hfinal.result, hfinal.active,
            hfinal.height.trans haSp, hfinal.top, hp.trans (by simpa only [haSp] using hfinal.preserved),
            hseen.trans hfinal.seen, hfinal.scanned, by omega⟩
        · obtain ⟨witness, bound⟩ := hfinal
          exact .inr ⟨witness, by omega⟩
      · obtain ⟨witness, bound⟩ := hfound
        let stop := if row.isEmpty then 0 else 1
        have stop_bound : stop ≤ 1 := by dsimp [stop]; split <;> omega
        have htrail := scan_after_cycle g r (v : Int) row out witness.positive tc
        exact ⟨(none, out), tc + stop, hcons.trans htrail, .inr ⟨witness, by omega⟩⟩
    · obtain ⟨found, tc, hstep, witness, bound⟩ := gray_arc valid inv v hsp top active edge hedge
        (hcolor.trans hgray) hfuel r t
      have hr := reserve_height g st
      exact ⟨_, tc, forIn_cons_done g r (v : Int) edge row _ _ t tc hstep,
        .inr ⟨witness, by omega⟩⟩
    · let next := fSkip st v
      have hstep := rowStep_black g r (v : Int) edge none visited parents (hcolor.trans hblack) t
      have nextInv := inv_skip inv hsp top hq hscan hqto hblack
      have nextActive := active.skip v
      have nsp : next.sp = st.sp := rfl
      have hnext : next.It v = st.It v + 1 := upd_same _ _ _
      have nextReserve : reserve g next + 2 ≤ reserve g st := by
        have h := phiF_skip n[g] hd[g] st v hv (by omega) hhead hlimit
        simpa [reserve, next, Nat.mul_add] using Nat.mul_le_mul_left 2 h
      obtain ⟨res, tt, hrun, hret⟩ := ih next visited parents (t + 1) nextInv nextActive (by omega) top
        (cursor.advance hnext) (by omega)
      have hcons := forIn_cons_yield g r (v : Int) edge row _ _ t (t + 1) hstep
      refine ⟨res, tt, hcons.trans hrun, ?_⟩
      rcases hret with ⟨final, hfinal⟩ | hfinal
      · have hcfinal := hfinal.work
        exact .inl ⟨final, hfinal.no_return, hfinal.empty, hfinal.result, hfinal.active, hfinal.height.trans nsp,
          hfinal.top, (skip_parked inv top).trans hfinal.preserved, hfinal.seen, hfinal.scanned, by omega⟩
      · obtain ⟨witness, bound⟩ := hfinal
        exact .inr ⟨witness, by omega⟩

theorem recursive_search (g : cp.ListGraph Cost E) (valid : ValidGraph g) (hfuel : n[g] < fuel) :
    ∀ lim, SearchSpec g lim := by
  intro lim
  induction lim with
  | zero =>
    intro v visited parents st t pre
    have ⟨inv, _, _, _, _, hlim⟩ := pre
    have := inv.sp_le
    omega
  | succ r rec =>
    intro v visited parents st t pre
    obtain ⟨inv, act, hpos, htop, hstart, hlim⟩ := pre
    have cur : AtCursor g st v (edgesAt g v) := ⟨[], rfl, by simpa using hstart⟩
    obtain ⟨res, t', hrow, hret⟩ := scan_row g valid hfuel r rec v (edgesAt g v) st
      (set visited (v : Int) 1) parents (t + 1) inv act hpos htop cur hlim
    have hexec : (cp.ListGraph.find_cycle_dfs_rec (r + 1) g (v : Int) visited parents Array.empty).run t =
        some (finishRow (v : Int) res, t') := by
      rw [dfs_scan, StateT.run_bind, tick_run, some_bind, StateT.run_bind]
      change ((forIn (edgesAt g v) (none, set visited (v : Int) 1, parents, Array.empty)
        (rowStep g r (v : Int))).run (t + 1) >>= _) = _
      rw [hrow]
      rfl
    refine ⟨finishRow (v : Int) res, t', hexec, ?_⟩
    rcases hret with ⟨s, ret⟩ | hfound
    · let final := fPop s v
      have hspos : 0 < s.sp := by rw [ret.height]; exact hpos
      have hsgray := top_gray ret.result hspos ret.top
      have hv := ret.result.c_lt v (by omega)
      have hfInv : Invariant g final := inv_pop ret.result hspos ret.top (ret.scanned.done hv)
      have hfAct : Active g (set res.2.1 (v : Int) 2) res.2.2.1 final := ret.active.pop hv
      have hfDepth : final.sp = st.sp - 1 := by show s.sp - 1 = _; rw [ret.height]
      have hfPark : Parked (st.sp - 1) st final :=
        ret.preserved.trans (by simpa only [ret.height] using (pop_parked (st := s) (v := v)))
      have hfSeen := ret.seen.trans (persists_with_update (by decide : (2 : Int) ≠ 0)
        (show final.C = upd s.C v 2 from rfl))
      have hpop : reserve g final + 2 ≤ reserve g s := by
        simpa [reserve, final, Nat.mul_add] using
          Nat.mul_le_mul_left 2 (phiF_pop n[g] hd[g] s v hspos hsgray)
      have hrowWork := ret.work
      refine .inl ⟨final, ?_⟩
      have hf : finishRow (v : Int) res = (set res.2.1 (v : Int) 2, res.2.2.1, res.2.2.2) := by
        simp [finishRow, ret.no_return]
      rw [hf]
      exact ⟨ret.empty, hfInv, hfAct, hfDepth, hfPark, hfSeen, by omega⟩
    · obtain ⟨witness, bound⟩ := hfound
      exact .inr ⟨witness, by omega⟩

end Proofs.Cpp.ListFindCycle
