import Proofs.FindCycleInv

namespace Proofs.FindCycleStep
open Proofs.LowlinkInv (upd upd_same upd_ne AdjH)
open Proofs.FindCycleInv

def fSkip (st : FS) (v : Nat) : FS :=
  { C := st.C, It := upd st.It v (st.It v + 1), Fi := st.Fi, Sk := st.Sk, sp := st.sp, nb := st.nb }

def fPush (hd : Nat → Nat) (st : FS) (v w : Nat) : FS :=
  { C := upd st.C w 1, It := upd (upd st.It v (st.It v + 1)) w (hd w : Int), Fi := st.Fi, Sk := upd st.Sk st.sp w,
    sp := st.sp + 1, nb := st.nb }

def fPop (st : FS) (v : Nat) : FS :=
  { C := upd st.C v 2, It := st.It, Fi := upd st.Fi v (st.nb : Int), Sk := st.Sk, sp := st.sp - 1, nb := st.nb + 1 }

def fRoot (hd : Nat → Nat) (st : FS) (r : Nat) : FS :=
  { C := upd st.C r 1, It := upd st.It r (hd r : Int), Fi := st.Fi, Sk := upd st.Sk 0 r, sp := 1, nb := st.nb }

section
variable {n : Nat} {hd tg : Nat → Nat} {st : FS}

theorem top_gray (I : FInv n hd tg st) {v : Nat} (hsp : 0 < st.sp) (hv : st.Sk (st.sp - 1) = v) : st.C v = 1 := by
  have := I.sk_gray (st.sp - 1) (by omega)
  rwa [hv] at this

/-- A black successor is skipped. -/
theorem inv_skip (I : FInv n hd tg st) {v w q : Nat} (hsp : 0 < st.sp) (hv : st.Sk (st.sp - 1) = v)
    (hq : (q : Int) = st.It v) (hit : q < hd (v + 1)) (hw : tg q = w) (hwb : st.C w = 2) :
    FInv n hd tg (fSkip st v) := by
  have hvg := top_gray I hsp hv
  have hrng := I.it_rng v (by omega)
  refine ⟨I.c_rng, I.c_lt, I.sk_gray, I.gray_sk, I.sk_inj, I.sk_arc, ?_, ?_, ?_, I.bl_fin, ?_⟩
  · intro a ha
    by_cases hav : a = v
    · subst hav
      show (hd a : Int) ≤ upd st.It a (st.It a + 1) a ∧ upd st.It a (st.It a + 1) a ≤ (hd (a + 1) : Int)
      rw [upd_same]
      omega
    · show (hd a : Int) ≤ upd st.It v (st.It v + 1) a ∧ upd st.It v (st.It v + 1) a ≤ (hd (a + 1) : Int)
      rw [upd_ne _ _ _ _ hav]; exact I.it_rng a ha
  · intro a ha q' hq1 hq2
    have ha' : st.C a ≠ 0 := ha
    by_cases hav : a = v
    · subst hav
      have hq2' : (q' : Int) < upd st.It a (st.It a + 1) a := hq2
      rw [upd_same] at hq2'
      by_cases hlt : (q' : Int) < st.It a
      · exact I.it_scan a ha' q' hq1 hlt
      · have : q' = q := by omega
        subst this
        show st.C (tg q') ≠ 0
        rw [hw]; omega
    · have hq2' : (q' : Int) < upd st.It v (st.It v + 1) a := hq2
      rw [upd_ne _ _ _ _ hav] at hq2'
      exact I.it_scan a ha' q' hq1 hq2'
  · intro i hi q' hq1 hq2
    have hi' : i < st.sp := hi
    by_cases hsv : st.Sk i = v
    · have hq2' : (q' : Int) < upd st.It v (st.It v + 1) (st.Sk i) := hq2
      rw [hsv, upd_same] at hq2'
      have hq1' : hd (st.Sk i) ≤ q' := hq1
      by_cases hlt : (q' : Int) < st.It v
      · rcases I.gray_scan i hi' q' hq1' (by rw [hsv]; exact hlt) with h | h
        · exact Or.inl h
        · exact Or.inr h
      · have : q' = q := by omega
        subst this
        left
        show st.C (tg q') = 2 ∧ st.Fi (tg q') < (st.nb : Int)
        rw [hw]
        have := (I.bl_fin w hwb).2
        exact ⟨hwb, this⟩
    · have hq2' : (q' : Int) < upd st.It v (st.It v + 1) (st.Sk i) := hq2
      rw [upd_ne _ _ _ _ hsv] at hq2'
      exact I.gray_scan i hi' q' hq1 hq2'
  · intro a ha
    have ha2 : st.C a = 2 := ha
    have hav : a ≠ v := by intro e; subst e; omega
    obtain ⟨h1, h2⟩ := I.bl_done a ha2
    refine ⟨?_, h2⟩
    show upd st.It v (st.It v + 1) a = _
    rw [upd_ne _ _ _ _ hav]; exact h1


/-- A white successor is pushed. -/
theorem inv_push (G : FGH n hd tg) (I : FInv n hd tg st) {v w q : Nat} (hsp : 0 < st.sp)
    (hv : st.Sk (st.sp - 1) = v) (hq : (q : Int) = st.It v) (hit : q < hd (v + 1)) (hw : tg q = w)
    (hwc : st.C w = 0) : FInv n hd tg (fPush hd st v w) := by
  have hvg := top_gray I hsp hv
  have hrng := I.it_rng v (by omega)
  have hadj : AdjH hd tg v w := ⟨q, by omega, hit, hw⟩
  have hwn := (G.adj_lt v w hadj).2
  have hvw : v ≠ w := by intro e; subst e; omega
  have hCw : (fPush hd st v w).C w = 1 := upd_same _ _ _
  have hCo : ∀ a, a ≠ w → (fPush hd st v w).C a = st.C a := fun a ha => upd_ne _ _ _ _ ha
  have hSk' : ∀ i, i ≠ st.sp → (fPush hd st v w).Sk i = st.Sk i := fun i hi => upd_ne _ _ _ _ hi
  have hSsp : (fPush hd st v w).Sk st.sp = w := upd_same _ _ _
  have hne : ∀ i, i < st.sp → st.Sk i ≠ w := by
    intro i hi e
    have := I.sk_gray i hi
    rw [e] at this; omega
  have hIw : (fPush hd st v w).It w = (hd w : Int) := upd_same _ _ _
  have hIo : ∀ a, a ≠ w → (fPush hd st v w).It a = (upd st.It v (st.It v + 1)) a := fun a ha => upd_ne _ _ _ _ ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a = w
    · subst ha; rw [hCw]; omega
    · rw [hCo a ha]; exact I.c_rng a
  · intro a ha
    by_cases haw : a = w
    · subst haw; exact hwn
    · have : st.C a ≠ 0 := by rw [← hCo a haw]; exact ha
      exact I.c_lt a this
  · intro i hi
    have hi' : i < st.sp + 1 := hi
    by_cases his : i = st.sp
    · subst his; rw [hSsp, hCw]
    · rw [hSk' i his, hCo _ (hne i (by omega))]; exact I.sk_gray i (by omega)
  · intro a ha
    by_cases haw : a = w
    · subst haw; exact ⟨st.sp, by show st.sp < st.sp + 1; omega, hSsp⟩
    · rw [hCo a haw] at ha
      obtain ⟨i, hi, hik⟩ := I.gray_sk a ha
      exact ⟨i, by show i < st.sp + 1; omega, by rw [hSk' i (by omega)]; exact hik⟩
  · intro i j hi hj hij
    have hi' : i < st.sp + 1 := hi
    have hj' : j < st.sp + 1 := hj
    by_cases his : i = st.sp
    · by_cases hjs : j = st.sp
      · omega
      · exfalso
        rw [his, hSsp, hSk' j hjs] at hij
        exact hne j (by omega) hij.symm
    · by_cases hjs : j = st.sp
      · exfalso
        rw [hjs, hSsp, hSk' i his] at hij
        exact hne i (by omega) hij
      · rw [hSk' i his, hSk' j hjs] at hij
        exact I.sk_inj i j (by omega) (by omega) hij
  · intro i hi
    have hi' : i + 1 < st.sp + 1 := hi
    by_cases hlast : i + 1 = st.sp
    · rw [hlast, hSsp, hSk' i (by omega)]
      have : i = st.sp - 1 := by omega
      rw [this, hv]; exact hadj
    · rw [hSk' i (by omega), hSk' (i + 1) hlast]
      exact I.sk_arc i (by omega)
  · intro a ha
    by_cases haw : a = w
    · subst haw
      rw [hIw]
      exact ⟨Int.le_refl _, by exact_mod_cast G.mono a hwn⟩
    · have ha' : st.C a ≠ 0 := by rw [← hCo a haw]; exact ha
      rw [hIo a haw]
      by_cases hav : a = v
      · subst hav; rw [upd_same]; omega
      · rw [upd_ne _ _ _ _ hav]; exact I.it_rng a ha'
  · intro a ha q' hq1 hq2
    by_cases haw : a = w
    · subst haw
      rw [hIw] at hq2
      omega
    · have ha' : st.C a ≠ 0 := by rw [← hCo a haw]; exact ha
      rw [hIo a haw] at hq2
      by_cases hav : a = v
      · subst hav
        rw [upd_same] at hq2
        by_cases hlt : (q' : Int) < st.It a
        · have := I.it_scan a ha' q' hq1 hlt
          by_cases htw : tg q' = w
          · rw [htw, hCw]; omega
          · rw [hCo _ htw]; exact this
        · have : q' = q := by omega
          subst this; rw [hw, hCw]; omega
      · rw [upd_ne _ _ _ _ hav] at hq2
        have := I.it_scan a ha' q' hq1 hq2
        by_cases htw : tg q' = w
        · rw [htw, hCw]; omega
        · rw [hCo _ htw]; exact this
  · intro i hi q' hq1 hq2
    have hi' : i < st.sp + 1 := hi
    by_cases his : i = st.sp
    · subst his
      rw [hSsp] at hq1 hq2
      rw [hIw] at hq2
      omega
    · have hi2 : i < st.sp := by omega
      rw [hSk' i his] at hq1 hq2
      have hsk := hne i hi2
      by_cases hsv : st.Sk i = v
      · rw [hsv] at hq2
        rw [hIo v hvw, upd_same] at hq2
        have hq1' : hd (st.Sk i) ≤ q' := hq1
        by_cases hlt : (q' : Int) < st.It v
        · rcases I.gray_scan i hi2 q' hq1' (by rw [hsv]; exact hlt) with h | h
          · left
            have htw : tg q' ≠ w := by
              intro e; rw [e] at h; omega
            rw [hCo _ htw]
            exact ⟨h.1, h.2⟩
          · right
            refine ⟨show i + 1 < st.sp + 1 by omega, ?_⟩
            rw [hSk' (i + 1) (by omega)]; exact h.2
        · right
          have : q' = q := by omega
          subst this
          have hisp : i + 1 = st.sp := by
            have := I.sk_inj i (st.sp - 1) hi2 (by omega) (by rw [hsv, hv])
            omega
          refine ⟨show i + 1 < st.sp + 1 by omega, ?_⟩
          rw [hisp, hSsp, hw]
      · rw [hIo _ (hne i hi2)] at hq2
        rw [upd_ne _ _ _ _ hsv] at hq2
        rcases I.gray_scan i hi2 q' hq1 hq2 with h | h
        · left
          have htw : tg q' ≠ w := by
            intro e; rw [e] at h; omega
          rw [hCo _ htw]
          exact ⟨h.1, h.2⟩
        · right
          refine ⟨show i + 1 < st.sp + 1 by omega, ?_⟩
          rw [hSk' (i + 1) (by omega)]; exact h.2
  · intro a ha
    have haw : a ≠ w := by
      intro e; subst e; rw [hCw] at ha; omega
    rw [hCo a haw] at ha
    exact I.bl_fin a ha
  · intro a ha
    have haw : a ≠ w := by
      intro e; subst e; rw [hCw] at ha; omega
    rw [hCo a haw] at ha
    have hav : a ≠ v := by intro e; subst e; omega
    obtain ⟨h1, h2⟩ := I.bl_done a ha
    refine ⟨?_, ?_⟩
    · rw [hIo a haw, upd_ne _ _ _ _ hav]; exact h1
    · intro q' hq1 hq2
      obtain ⟨h3, h4⟩ := h2 q' hq1 hq2
      have htw : tg q' ≠ w := by intro e; rw [e] at h3; omega
      rw [hCo _ htw]
      exact ⟨h3, h4⟩


/-- The top is finished. -/
theorem inv_pop (I : FInv n hd tg st) {v : Nat} (hsp : 0 < st.sp) (hv : st.Sk (st.sp - 1) = v)
    (hit : st.It v = (hd (v + 1) : Int)) : FInv n hd tg (fPop st v) := by
  have hvg := top_gray I hsp hv
  have hvn := I.c_lt v (by omega)
  have hCv : (fPop st v).C v = 2 := upd_same _ _ _
  have hCo : ∀ a, a ≠ v → (fPop st v).C a = st.C a := fun a ha => upd_ne _ _ _ _ ha
  have hFv : (fPop st v).Fi v = (st.nb : Int) := upd_same _ _ _
  have hFo : ∀ a, a ≠ v → (fPop st v).Fi a = st.Fi a := fun a ha => upd_ne _ _ _ _ ha
  have hne : ∀ i, i < st.sp - 1 → st.Sk i ≠ v := by
    intro i hi e
    have := I.sk_inj i (st.sp - 1) (by omega) (by omega) (by rw [e, hv])
    omega
  have hsc : ∀ q' : Nat, hd v ≤ q' → q' < hd (v + 1) → st.C (tg q') = 2 ∧ st.Fi (tg q') < (st.nb : Int) := by
    intro q' h1 h2
    rcases I.gray_scan (st.sp - 1) (by omega) q' (by rw [hv]; exact h1) (by rw [hv]; omega) with h | h
    · exact h
    · exfalso; have := h.1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a = v
    · subst ha; rw [hCv]; omega
    · rw [hCo a ha]; exact I.c_rng a
  · intro a ha
    by_cases hav : a = v
    · subst hav; exact hvn
    · rw [hCo a hav] at ha; exact I.c_lt a ha
  · intro i hi
    have hi' : i < st.sp - 1 := hi
    show (fPop st v).C (st.Sk i) = 1
    rw [hCo _ (hne i hi')]; exact I.sk_gray i (by omega)
  · intro a ha
    have hav : a ≠ v := by intro e; subst e; rw [hCv] at ha; omega
    rw [hCo a hav] at ha
    obtain ⟨i, hi, hik⟩ := I.gray_sk a ha
    refine ⟨i, ?_, hik⟩
    show i < st.sp - 1
    by_cases hlast : i = st.sp - 1
    · exfalso; apply hav; rw [← hik, hlast, hv]
    · omega
  · intro i j hi hj hij
    exact I.sk_inj i j (by have : i < st.sp - 1 := hi; omega) (by have : j < st.sp - 1 := hj; omega) hij
  · intro i hi
    exact I.sk_arc i (by have : i + 1 < st.sp - 1 := hi; omega)
  · intro a ha
    by_cases hav : a = v
    · subst hav
      show (hd a : Int) ≤ st.It a ∧ st.It a ≤ (hd (a + 1) : Int)
      have := I.it_rng a (by omega)
      omega
    · rw [hCo a hav] at ha; exact I.it_rng a ha
  · intro a ha q' hq1 hq2
    by_cases hav : a = v
    · subst hav
      have hq2' : (q' : Int) < st.It a := hq2
      rw [hit] at hq2'
      have hh := hsc q' hq1 (by omega)
      have htv : tg q' ≠ a := by intro e; rw [e] at hh; omega
      rw [hCo _ htv]; omega
    · rw [hCo a hav] at ha
      have := I.it_scan a ha q' hq1 hq2
      by_cases htv : tg q' = v
      · rw [htv, hCv]; omega
      · rw [hCo _ htv]; exact this
  · intro i hi q' hq1 hq2
    have hi' : i < st.sp - 1 := hi
    have hsv := hne i hi'
    have hq1' : hd (st.Sk i) ≤ q' := hq1
    have hq2' : (q' : Int) < st.It (st.Sk i) := hq2
    rcases I.gray_scan i (by omega) q' hq1' hq2' with h | h
    · left
      have htv : tg q' ≠ v := by intro e; rw [e] at h; omega
      rw [hCo _ htv, hFo _ htv]
      exact ⟨h.1, by show st.Fi (tg q') < ((st.nb + 1 : Nat) : Int); push_cast; omega⟩
    · by_cases hlast : i + 1 < st.sp - 1
      · right; exact ⟨hlast, h.2⟩
      · left
        have hi1 : i + 1 = st.sp - 1 := by omega
        have : tg q' = v := by rw [h.2, hi1, hv]
        rw [this, hCv, hFv]
        exact ⟨rfl, by show (st.nb : Int) < ((st.nb + 1 : Nat) : Int); push_cast; omega⟩
  · intro a ha
    by_cases hav : a = v
    · subst hav
      rw [hFv]
      exact ⟨Int.natCast_nonneg _, by show (st.nb : Int) < ((st.nb + 1 : Nat) : Int); push_cast; omega⟩
    · rw [hCo a hav] at ha
      rw [hFo a hav]
      have := I.bl_fin a ha
      exact ⟨this.1, by show st.Fi a < ((st.nb + 1 : Nat) : Int); push_cast; omega⟩
  · intro a ha
    by_cases hav : a = v
    · subst hav
      refine ⟨hit, ?_⟩
      intro q' hq1 hq2
      have hh := hsc q' hq1 hq2
      have htv : tg q' ≠ a := by intro e; rw [e] at hh; omega
      rw [hCo _ htv, hFo _ htv, hFv]
      exact ⟨hh.1, hh.2⟩
    · rw [hCo a hav] at ha
      obtain ⟨h1, h2⟩ := I.bl_done a ha
      refine ⟨h1, ?_⟩
      intro q' hq1 hq2
      obtain ⟨h3, h4⟩ := h2 q' hq1 hq2
      have htv : tg q' ≠ v := by intro e; rw [e] at h3; omega
      rw [hCo _ htv, hFo _ htv, hFo a hav]
      exact ⟨h3, h4⟩

/-- A new root. -/
theorem inv_root (G : FGH n hd tg) (I : FInv n hd tg st) {r : Nat} (hsp : st.sp = 0) (hrn : r < n)
    (hrc : st.C r = 0) : FInv n hd tg (fRoot hd st r) := by
  have hCr : (fRoot hd st r).C r = 1 := upd_same _ _ _
  have hCo : ∀ a, a ≠ r → (fRoot hd st r).C a = st.C a := fun a ha => upd_ne _ _ _ _ ha
  have hIr : (fRoot hd st r).It r = (hd r : Int) := upd_same _ _ _
  have hIo : ∀ a, a ≠ r → (fRoot hd st r).It a = st.It a := fun a ha => upd_ne _ _ _ _ ha
  have hS0 : (fRoot hd st r).Sk 0 = r := by show upd st.Sk 0 r 0 = r; exact upd_same _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a = r
    · subst ha; rw [hCr]; omega
    · rw [hCo a ha]; exact I.c_rng a
  · intro a ha
    by_cases har : a = r
    · subst har; exact hrn
    · rw [hCo a har] at ha; exact I.c_lt a ha
  · intro i hi
    have : i = 0 := by have : i < 1 := hi; omega
    subst this; rw [hS0, hCr]
  · intro a ha
    by_cases har : a = r
    · subst har; exact ⟨0, by show 0 < 1; omega, hS0⟩
    · rw [hCo a har] at ha
      obtain ⟨i, hi, _⟩ := I.gray_sk a ha
      omega
  · intro i j hi hj _
    have h1 : i < 1 := hi
    have h2 : j < 1 := hj
    omega
  · intro i hi
    have : i + 1 < 1 := hi
    omega
  · intro a ha
    by_cases har : a = r
    · subst har; rw [hIr]; exact ⟨Int.le_refl _, by exact_mod_cast G.mono a hrn⟩
    · rw [hCo a har] at ha; rw [hIo a har]; exact I.it_rng a ha
  · intro a ha q' hq1 hq2
    by_cases har : a = r
    · subst har; rw [hIr] at hq2; omega
    · rw [hCo a har] at ha; rw [hIo a har] at hq2
      have := I.it_scan a ha q' hq1 hq2
      by_cases htr : tg q' = r
      · rw [htr, hCr]; omega
      · rw [hCo _ htr]; exact this
  · intro i hi q' hq1 hq2
    have hi0 : i = 0 := by have : i < 1 := hi; omega
    subst hi0
    rw [hS0] at hq1 hq2
    rw [hIr] at hq2
    omega
  · intro a ha
    have har : a ≠ r := by intro e; subst e; rw [hCr] at ha; omega
    rw [hCo a har] at ha
    exact I.bl_fin a ha
  · intro a ha
    have har : a ≠ r := by intro e; subst e; rw [hCr] at ha; omega
    rw [hCo a har] at ha
    obtain ⟨h1, h2⟩ := I.bl_done a ha
    refine ⟨by rw [hIo a har]; exact h1, ?_⟩
    intro q' hq1 hq2
    obtain ⟨h3, h4⟩ := h2 q' hq1 hq2
    have htr : tg q' ≠ r := by intro e; rw [e] at h3; omega
    rw [hCo _ htr]
    exact ⟨h3, h4⟩

end

end Proofs.FindCycleStep
