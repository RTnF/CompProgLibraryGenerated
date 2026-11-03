import Proofs.FindCycleStep
import Proofs.LowlinkPhi

namespace Proofs.FindCyclePhi
open Proofs.LowlinkInv (upd upd_same upd_ne)
open Proofs.FindCycleInv Proofs.FindCycleStep
open Proofs.LowlinkPhi (sum_map_le sum_map_lt)

/-- The cost potential: arcs not yet scanned, white vertices, stack height. -/
def itNF (hd : Nat → Nat) (st : FS) (a : Nat) : Nat := if st.C a ≠ 0 then (st.It a).toNat else hd a

def unscF (n : Nat) (hd : Nat → Nat) (st : FS) : Nat :=
  ((List.range n).map (fun a => hd (a + 1) - itNF hd st a)).sum

def whiteF (n : Nat) (st : FS) : Nat := ((List.range n).map (fun a => if st.C a = 0 then 1 else 0)).sum

def phiF (n : Nat) (hd : Nat → Nat) (st : FS) : Nat := unscF n hd st + whiteF n st + st.sp

theorem phiF_skip (n : Nat) (hd : Nat → Nat) (st : FS) (v : Nat) (hvn : v < n) (hvc : st.C v ≠ 0)
    (h1 : (hd v : Int) ≤ st.It v) (h2 : st.It v < (hd (v + 1) : Int)) :
    phiF n hd (fSkip st v) + 1 ≤ phiF n hd st := by
  have t1 : itNF hd (fSkip st v) v = (st.It v).toNat + 1 := by
    unfold itNF
    rw [if_pos (show (fSkip st v).C v ≠ 0 from hvc)]
    show (upd st.It v (st.It v + 1) v).toNat = _
    rw [upd_same]; omega
  have t2 : ∀ a, a ≠ v → itNF hd (fSkip st v) a = itNF hd st a := by
    intro a ha
    unfold itNF
    show (if st.C a ≠ 0 then (upd st.It v (st.It v + 1) a).toNat else hd a) = _
    rw [upd_ne _ _ _ _ ha]
  have t0 : itNF hd st v = (st.It v).toNat := by unfold itNF; rw [if_pos hvc]
  have key : unscF n hd (fSkip st v) + 1 ≤ unscF n hd st := by
    unfold unscF
    apply sum_map_lt _ _ _ _ v (List.mem_range.mpr hvn) _ List.nodup_range
    · intro a _
      by_cases hav : a = v
      · subst hav; rw [t1, t0]; omega
      · rw [t2 a hav]
    · rw [t1, t0]; omega
  unfold phiF
  have hw : whiteF n (fSkip st v) = whiteF n st := rfl
  have hs : (fSkip st v).sp = st.sp := rfl
  rw [hw, hs]
  omega

theorem phiF_pop (n : Nat) (hd : Nat → Nat) (st : FS) (v : Nat) (hsp : 0 < st.sp) (hvc : st.C v = 1) :
    phiF n hd (fPop st v) + 1 ≤ phiF n hd st := by
  have hit : ∀ a, itNF hd (fPop st v) a = itNF hd st a := by
    intro a
    unfold itNF
    by_cases hav : a = v
    · subst hav
      have e1 : (fPop st a).C a = 2 := upd_same _ _ _
      rw [if_pos (by omega), if_pos (by omega)]
      rfl
    · have : (fPop st v).C a = st.C a := upd_ne _ _ _ _ hav
      rw [this]
      rfl
  have e : unscF n hd (fPop st v) = unscF n hd st := by
    unfold unscF
    congr 1
    apply List.map_congr_left
    intro a _
    rw [hit a]
  have ew : whiteF n (fPop st v) = whiteF n st := by
    unfold whiteF
    congr 1
    apply List.map_congr_left
    intro a _
    by_cases hav : a = v
    · subst hav
      have e1 : (fPop st a).C a = 2 := upd_same _ _ _
      rw [e1, if_neg (by omega), if_neg (by omega)]
    · have : (fPop st v).C a = st.C a := upd_ne _ _ _ _ hav
      rw [this]
  unfold phiF
  have hs : (fPop st v).sp = st.sp - 1 := rfl
  rw [e, ew, hs]
  omega

theorem phiF_push (n : Nat) (hd : Nat → Nat) (st : FS) (v w : Nat) (hvn : v < n) (hwn : w < n) (hvc : st.C v ≠ 0)
    (hwc : st.C w = 0) (h1 : (hd v : Int) ≤ st.It v) (h2 : st.It v < (hd (v + 1) : Int)) :
    phiF n hd (fPush hd st v w) + 1 ≤ phiF n hd st := by
  have hvw : v ≠ w := by intro e; subst e; omega
  have hCw : (fPush hd st v w).C w = 1 := upd_same _ _ _
  have hCo : ∀ a, a ≠ w → (fPush hd st v w).C a = st.C a := fun a ha => upd_ne _ _ _ _ ha
  have tv : itNF hd (fPush hd st v w) v = (st.It v).toNat + 1 := by
    unfold itNF
    rw [if_pos (by rw [hCo v hvw]; exact hvc)]
    show (upd (upd st.It v (st.It v + 1)) w (hd w : Int) v).toNat = _
    rw [upd_ne _ _ _ _ hvw, upd_same]; omega
  have tw : itNF hd (fPush hd st v w) w = itNF hd st w := by
    unfold itNF
    rw [if_pos (by rw [hCw]; omega), if_neg (by omega)]
    show (upd (upd st.It v (st.It v + 1)) w (hd w : Int) w).toNat = hd w
    rw [upd_same]; simp
  have t2 : ∀ a, a ≠ v → a ≠ w → itNF hd (fPush hd st v w) a = itNF hd st a := by
    intro a hav haw
    unfold itNF
    rw [hCo a haw]
    show (if st.C a ≠ 0 then (upd (upd st.It v (st.It v + 1)) w (hd w : Int) a).toNat else hd a) = _
    rw [upd_ne _ _ _ _ haw, upd_ne _ _ _ _ hav]
  have t0 : itNF hd st v = (st.It v).toNat := by unfold itNF; rw [if_pos hvc]
  have key : unscF n hd (fPush hd st v w) + 1 ≤ unscF n hd st := by
    unfold unscF
    apply sum_map_lt _ _ _ _ v (List.mem_range.mpr hvn) _ List.nodup_range
    · intro a _
      by_cases hav : a = v
      · subst hav; rw [tv, t0]; omega
      · by_cases haw : a = w
        · subst haw; rw [tw]
        · rw [t2 a hav haw]
    · rw [tv, t0]; omega
  have kw : whiteF n (fPush hd st v w) + 1 ≤ whiteF n st := by
    unfold whiteF
    apply sum_map_lt _ _ _ _ w (List.mem_range.mpr hwn) _ List.nodup_range
    · intro a _
      by_cases haw : a = w
      · subst haw; rw [hCw]; simp [hwc]
      · rw [hCo a haw]
    · rw [hCw]; simp [hwc]
  unfold phiF
  have hs : (fPush hd st v w).sp = st.sp + 1 := rfl
  rw [hs]
  omega

theorem phiF_root (n : Nat) (hd : Nat → Nat) (st : FS) (r : Nat) (hrn : r < n) (hrc : st.C r = 0) (hsp : st.sp = 0) :
    phiF n hd (fRoot hd st r) ≤ phiF n hd st := by
  have hCr : (fRoot hd st r).C r = 1 := upd_same _ _ _
  have hCo : ∀ a, a ≠ r → (fRoot hd st r).C a = st.C a := fun a ha => upd_ne _ _ _ _ ha
  have e : unscF n hd (fRoot hd st r) = unscF n hd st := by
    unfold unscF
    congr 1
    apply List.map_congr_left
    intro a _
    unfold itNF
    by_cases har : a = r
    · subst har
      rw [if_pos (by rw [hCr]; omega), if_neg (by omega)]
      show hd (a + 1) - (upd st.It a (hd a : Int) a).toNat = hd (a + 1) - hd a
      rw [upd_same]; simp
    · rw [hCo a har]
      show hd (a + 1) - (if st.C a ≠ 0 then (upd st.It r (hd r : Int) a).toNat else hd a) = _
      rw [upd_ne _ _ _ _ har]
  have kw : whiteF n (fRoot hd st r) + 1 ≤ whiteF n st := by
    unfold whiteF
    apply sum_map_lt _ _ _ _ r (List.mem_range.mpr hrn) _ List.nodup_range
    · intro a _
      by_cases har : a = r
      · subst har; rw [hCr]; simp [hrc]
      · rw [hCo a har]
    · rw [hCr]; simp [hrc]
  unfold phiF
  have hs : (fRoot hd st r).sp = 1 := rfl
  rw [e, hs]
  omega

end Proofs.FindCyclePhi
