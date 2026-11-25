import Proofs.Cpp.ListLowlinkOutputProjection
import Proofs.Cpp.Lib.Basic

namespace Proofs.Cpp.ListLowlink

open Proofs.LowlinkInv Proofs.LowlinkRoot Proofs.LowlinkPush Proofs.LowlinkPop Proofs.LowlinkScan
open Proofs.LowlinkMultigraph

/-- While a DFS frame runs, the stack below it and discovery data of old vertices do not change.
Only the top frame can change a scan cursor, low or separating-child count of an old vertex. -/
structure SameFrame (before after : St) (top : Nat) : Prop where
  depth : after.sp = before.sp
  stack : ∀ i < before.sp, after.Sk i = before.Sk i
  grows : before.Vis <+: after.Vis
  visited : ∀ x ∈ before.Vis, after.O x = before.O x ∧ after.P x = before.P x
  paused : ∀ x ∈ before.Vis, x ≠ top →
    after.It x = before.It x ∧ after.L x = before.L x ∧ after.Sp x = before.Sp x ∧ after.Fi x = before.Fi x

theorem SameFrame.refl (st : St) (v : Nat) : SameFrame st st v :=
  ⟨rfl, fun _ _ => rfl, ⟨[], by simp⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

theorem SameFrame.trans {a b c : St} {v : Nat} (ab : SameFrame a b v) (bc : SameFrame b c v) :
    SameFrame a c v := by
  refine ⟨bc.depth.trans ab.depth, fun i hi => (bc.stack i (by rwa [ab.depth])).trans (ab.stack i hi),
    ab.grows.trans bc.grows, ?_, ?_⟩
  · intro x hx
    obtain ⟨ho, hp⟩ := ab.visited x hx
    obtain ⟨ho', hp'⟩ := bc.visited x (ab.grows.subset hx)
    exact ⟨ho'.trans ho, hp'.trans hp⟩
  · intro x hx hne
    obtain ⟨hi, hl, hs, hf⟩ := ab.paused x hx hne
    obtain ⟨hi', hl', hs', hf'⟩ := bc.paused x (ab.grows.subset hx) hne
    exact ⟨hi'.trans hi, hl'.trans hl, hs'.trans hs, hf'.trans hf⟩

theorem SameFrame.top {a b : St} {v : Nat} (h : SameFrame a b v) (hsp : 0 < a.sp)
    (ht : a.Sk (a.sp - 1) = v) : b.Sk (b.sp - 1) = v := by
  rw [h.depth, h.stack _ (by omega), ht]

theorem advance_same_frame (st : St) (v w : Nat) : SameFrame st (advanceVisited st v w) v := by
  unfold advanceVisited
  split
  · exact SameFrame.refl _ _
  · refine ⟨rfl, fun _ _ => rfl, ⟨[], by simp [scanS]⟩, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    intro x _ hne
    simp only [scanS, scanProjected]
    split <;> simp [upd_ne _ _ _ _ hne]

/-- Pushing a new child, running it with its ancestors paused, then popping it leaves the
caller's cursor advanced by exactly one arc and modifies only the caller's low and counter. -/
theorem return_child_frame {hd : Nat → Nat} {st done : St} {v w : Nat}
    (hv : v ∈ st.Vis) (hnew : w ∉ st.Vis)
    (run : SameFrame (pushS hd st v w) done w) :
    SameFrame st (popS done w) v ∧
      (popS done w).It v = st.It v + 1 ∧ done.P w = (v : Int) ∧
      done.L v = st.L v ∧ done.Sp v = st.Sp v := by
  let pushed := pushS hd st v w
  have hs' : done.sp = st.sp + 1 := run.depth
  have hvis : st.Vis <+: pushed.Vis := ⟨[w], rfl⟩
  have hw : w ∈ pushed.Vis := by simp [pushed, pushS]
  have hpar : done.P w = (v : Int) := (run.visited w hw).2.trans (upd_same _ _ _)
  have hvw : v ≠ w := fun e => hnew (e ▸ hv)
  obtain ⟨hIt, hL, hSp, _⟩ := run.paused v (hvis.subset hv) hvw
  refine ⟨⟨?_, ?_, hvis.trans run.grows, ?_, ?_⟩, ?_, hpar, ?_, ?_⟩
  · show done.sp - 1 = st.sp
    omega
  · intro i hi
    show done.Sk i = st.Sk i
    rw [run.stack i (by change i < st.sp + 1; omega)]
    exact upd_ne _ _ _ _ (by omega)
  · intro x hx
    have h := run.visited x (hvis.subset hx)
    have hne : x ≠ w := fun e => hnew (e ▸ hx)
    exact ⟨h.1.trans (upd_ne _ _ _ _ hne), h.2.trans (upd_ne _ _ _ _ hne)⟩
  · intro x hx hxv
    have hxw : x ≠ w := fun e => hnew (e ▸ hx)
    obtain ⟨hi, hl, hsep, hf⟩ := run.paused x (hvis.subset hx) hxw
    have hparx : ¬ (v : Int) = (x : Int) := by omega
    simp only [popS, hpar, hparx, ite_false, upd_ne _ _ _ _ hxw]
    exact ⟨hi.trans (by simp [pushS, upd_ne _ _ _ _ hxw, upd_ne _ _ _ _ hxv]),
      hl.trans (upd_ne _ _ _ _ hxw), hsep, hf⟩
  · exact hIt.trans (by simp [pushS, upd_ne _ _ _ _ hvw, upd_same])
  · exact hL.trans (upd_ne _ _ _ _ hvw)
  · exact hSp


section Cursor

open Proofs.Cpp

def edgeTargets {E : Type} [Field "to" E Int] (r : List E) : List Int :=
  r.map (Field.get (member := "to"))

def listTargets {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (v : Nat) : List Nat :=
  (edgeTargets (Row adj v).toList).map Int.toNat

abbrev rowHeads {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n : Nat) :=
  offsets (rows n (listTargets adj))

abbrev rowEnds {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n : Nat) :=
  endpoints (rows n (listTargets adj))

def cursorIdx {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n v : Nat)
    (pref : List E) : Nat :=
  rowHeads adj n v + (((edgeTargets pref).map Int.toNat).filter (fun w => decide (w ≠ v))).length

theorem cursor_nil {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n v : Nat) :
    cursorIdx adj n v [] = rowHeads adj n v := by simp [cursorIdx, edgeTargets]

theorem cursor_full {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)} {n v : Nat}
    (hv : v < n) : cursorIdx adj n v (Row adj v).toList = rowHeads adj n (v + 1) := by
  have hr : v < (rows n (listTargets adj)).length := by simpa [rows] using hv
  change cursorIdx adj n v (Row adj v).toList = offsets (rows n (listTargets adj)) (v + 1)
  rw [offsets_succ _ _ hr, row_get n (listTargets adj) v hv]
  rfl

theorem cursor_lookup {E : Type} [Inhabited E] [Field "to" E Int] {adj : Array (Array E)} {n v : Nat}
    {pref suff : List E} {e : E} (he : (Row adj v).toList = pref ++ e :: suff) (hv : v < n)
    (hne : (Field.get (member := "to") e : Int).toNat ≠ v) :
    cursorIdx adj n v pref < rowHeads adj n (v + 1) ∧
      rowEnds adj n (cursorIdx adj n v pref) = (Field.get (member := "to") e : Int).toNat := by
  apply row_cursor n (listTargets adj) v _ hv ((edgeTargets pref).map Int.toNat)
    ((edgeTargets suff).map Int.toNat) _ hne
  simp [listTargets, edgeTargets, he]

theorem cursor_step {E : Type} [Inhabited E] [Field "to" E Int] (adj : Array (Array E)) (n v : Nat)
    (pref : List E) (e : E) :
    cursorIdx adj n v (pref ++ [e]) = cursorIdx adj n v pref +
      if (Field.get (member := "to") e : Int).toNat = v then 0 else 1 := by
  by_cases h : (Field.get (member := "to") e : Int).toNat = v <;>
    simp [cursorIdx, edgeTargets, h, Nat.add_assoc]

theorem nonnegative_count (xs : List Int) (p : Nat) (hn : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map Int.toNat).count p = xs.count (p : Int) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hn x (by simp)
    have ht := ih fun y hy => hn y (List.mem_cons_of_mem _ hy)
    have he : x.toNat = p ↔ x = (p : Int) := by omega
    by_cases hp : x = (p : Int)
    · simp [ht, hp]
    · simp [List.count_cons, ht, hp, mt he.mp hp]

end Cursor

end Proofs.Cpp.ListLowlink
