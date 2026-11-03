import Proofs.LowlinkLists

namespace Proofs.LowlinkPhi
open Proofs.LowlinkInv Proofs.LowlinkScan Proofs.LowlinkPop Proofs.LowlinkPush Proofs.LowlinkRoot

/-- The cost potential: the arcs not yet scanned, the unvisited vertices and the stack. -/
def itN (hd : Nat → Nat) (st : St) (a : Nat) : Nat := if a ∈ st.Vis then (st.It a).toNat else hd a

def unsc (n : Nat) (hd : Nat → Nat) (st : St) : Nat :=
  ((List.range n).map (fun a => hd (a + 1) - itN hd st a)).sum

def phi (n : Nat) (hd : Nat → Nat) (st : St) : Nat := unsc n hd st + (n - st.Vis.length) + st.sp

theorem sum_map_le (l : List Nat) (f g : Nat → Nat) (hle : ∀ a ∈ l, g a ≤ f a) : (l.map g).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hle a (by simp)
    have := ih (fun c hc => hle c (List.mem_cons_of_mem _ hc))
    omega

theorem sum_map_lt (l : List Nat) (f g : Nat → Nat) (hle : ∀ a ∈ l, g a ≤ f a) (b : Nat) (hb : b ∈ l)
    (hlt : g b + 1 ≤ f b) (hnd : l.Nodup) : (l.map g).sum + 1 ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hb
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hb with rfl | hbt
    · have := sum_map_le t f g (fun c hc => hle c (List.mem_cons_of_mem _ hc))
      omega
    · have h1 := hle a (by simp)
      have := ih (fun c hc => hle c (List.mem_cons_of_mem _ hc)) hbt hnd.2
      omega


theorem phi_scan (n : Nat) (hd : Nat → Nat) (st : St) (v : Nat) (Lnew : Nat → Int) (hvn : v < n) (hvV : v ∈ st.Vis)
    (h1 : (hd v : Int) ≤ st.It v) (h2 : st.It v < (hd (v + 1) : Int)) :
    phi n hd (scanS st v Lnew) + 1 ≤ phi n hd st := by
  have t1 : itN hd (scanS st v Lnew) v = (st.It v).toNat + 1 := by
    unfold itN
    rw [if_pos (show v ∈ (scanS st v Lnew).Vis from hvV)]
    show (upd st.It v (st.It v + 1) v).toNat = _
    rw [upd_same]
    omega
  have t2 : ∀ a, a ≠ v → itN hd (scanS st v Lnew) a = itN hd st a := by
    intro a ha
    unfold itN
    have hm : a ∈ (scanS st v Lnew).Vis ↔ a ∈ st.Vis := Iff.rfl
    by_cases ham : a ∈ st.Vis
    · rw [if_pos (hm.mpr ham), if_pos ham]
      show (upd st.It v (st.It v + 1) a).toNat = _
      rw [upd_ne _ _ _ _ ha]
    · rw [if_neg (mt hm.mp ham), if_neg ham]
  have t0 : itN hd st v = (st.It v).toNat := by
    unfold itN; rw [if_pos hvV]
  have key : unsc n hd (scanS st v Lnew) + 1 ≤ unsc n hd st := by
    unfold unsc
    apply sum_map_lt _ _ _ _ v (List.mem_range.mpr hvn) _ List.nodup_range
    · intro a _
      by_cases hav : a = v
      · subst hav; rw [t1, t0]; omega
      · rw [t2 a hav]
    · rw [t1, t0]; omega
  unfold phi
  show unsc n hd (scanS st v Lnew) + (n - st.Vis.length) + st.sp + 1 ≤ _
  omega

theorem phi_pop (n : Nat) (hd : Nat → Nat) (st : St) (v : Nat) (hsp : 0 < st.sp) :
    phi n hd (popS st v) + 1 ≤ phi n hd st := by
  have e : unsc n hd (popS st v) = unsc n hd st := rfl
  unfold phi
  show unsc n hd (popS st v) + (n - st.Vis.length) + (st.sp - 1) + 1 ≤ _
  rw [e]
  omega

theorem phi_push (n : Nat) (hd : Nat → Nat) (st : St) (v w : Nat) (hvn : v < n) (hvV : v ∈ st.Vis) (hwV : w ∉ st.Vis)
    (hlt : st.Vis.length < n) (h1 : (hd v : Int) ≤ st.It v) (h2 : st.It v < (hd (v + 1) : Int)) :
    phi n hd (pushS hd st v w) + 1 ≤ phi n hd st := by
  have hvw : v ≠ w := fun e => hwV (e ▸ hvV)
  have hmem : ∀ a, a ∈ (pushS hd st v w).Vis ↔ a ∈ st.Vis ∨ a = w := by intro a; simp [pushS]
  have tv : itN hd (pushS hd st v w) v = (st.It v).toNat + 1 := by
    unfold itN
    rw [if_pos ((hmem v).mpr (Or.inl hvV))]
    show (upd (upd st.It v (st.It v + 1)) w (hd w : Int) v).toNat = _
    rw [upd_ne _ _ _ _ hvw, upd_same]
    omega
  have t2 : ∀ a, a ≠ v → a ≠ w → itN hd (pushS hd st v w) a = itN hd st a := by
    intro a hav haw
    unfold itN
    by_cases ham : a ∈ st.Vis
    · rw [if_pos ((hmem a).mpr (Or.inl ham)), if_pos ham]
      show (upd (upd st.It v (st.It v + 1)) w (hd w : Int) a).toNat = _
      rw [upd_ne _ _ _ _ haw, upd_ne _ _ _ _ hav]
    · rw [if_neg (fun h => ((hmem a).mp h).elim ham haw), if_neg ham]
  have t0 : itN hd st v = (st.It v).toNat := by
    unfold itN; rw [if_pos hvV]
  have tw' : itN hd (pushS hd st v w) w = itN hd st w := by
    unfold itN
    rw [if_pos ((hmem w).mpr (Or.inr rfl)), if_neg hwV]
    show (upd (upd st.It v (st.It v + 1)) w (hd w : Int) w).toNat = _
    rw [upd_same]
    simp
  have key : unsc n hd (pushS hd st v w) + 1 ≤ unsc n hd st := by
    unfold unsc
    apply sum_map_lt _ _ _ _ v (List.mem_range.mpr hvn) _ List.nodup_range
    · intro a _
      by_cases hav : a = v
      · subst hav; rw [tv, t0]; omega
      · by_cases haw : a = w
        · subst haw; rw [tw']
        · rw [t2 a hav haw]
    · rw [tv, t0]; omega
  unfold phi
  have hl : (pushS hd st v w).Vis.length = st.Vis.length + 1 := by simp [pushS]
  have hs : (pushS hd st v w).sp = st.sp + 1 := rfl
  rw [hl, hs]
  omega


theorem phi_root (n : Nat) (hd : Nat → Nat) (st : St) (r : Nat) (hrV : r ∉ st.Vis) (hlt : st.Vis.length < n)
    (hsp : st.sp = 0) : phi n hd (rootS hd st r) ≤ phi n hd st := by
  have hmem : ∀ a, a ∈ (rootS hd st r).Vis ↔ a ∈ st.Vis ∨ a = r := by intro a; simp [rootS]
  have e : unsc n hd (rootS hd st r) = unsc n hd st := by
    unfold unsc
    congr 1
    apply List.map_congr_left
    intro a _
    unfold itN
    by_cases har : a = r
    · subst har
      rw [if_pos ((hmem a).mpr (Or.inr rfl)), if_neg hrV]
      show hd (a + 1) - (upd st.It a (hd a : Int) a).toNat = hd (a + 1) - hd a
      rw [upd_same]
      simp
    · by_cases ham : a ∈ st.Vis
      · rw [if_pos ((hmem a).mpr (Or.inl ham)), if_pos ham]
        show hd (a + 1) - (upd st.It r (hd r : Int) a).toNat = hd (a + 1) - (st.It a).toNat
        rw [upd_ne _ _ _ _ har]
      · rw [if_neg (fun h => ((hmem a).mp h).elim ham har), if_neg ham]
  unfold phi
  have hl : (rootS hd st r).Vis.length = st.Vis.length + 1 := by simp [rootS]
  have hs : (rootS hd st r).sp = 1 := rfl
  rw [e, hl, hs]
  omega

end Proofs.LowlinkPhi
