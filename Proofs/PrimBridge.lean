import Proofs.PrimExec

namespace Proofs.PrimBridge
open Proofs.BellmanFordMath (Edge)
open Proofs.DijkstraMath (Eall mem_Eall mem_Eall_inv)
open Proofs.PrimMath
open Proofs.PrimStep (PInv StepOK)

/-- The arc of an edge with non-negative cost. -/
def toArc (e : Edge) : Arc := (e.1, e.2.1, e.2.2.toNat)

/-- `W` is the weight of a minimum spanning forest of the graph on `0 .. n-1` with the arcs `E`
(a spanning forest is given by a parent arc for every non-root vertex, so that no cycle can occur). -/
def IsMSF (n B : Nat) (E : List Arc) (W : Nat) : Prop :=
  (∃ par rank, Forest n E par rank ∧ Spans E par (B + 1) ∧ Weight n par = W) ∧
  ∀ par rank, Forest n E par rank → Spans E par (B + 1) → W ≤ Weight n par

theorem mem_take_iff_idx {D : List Nat} (hnd : D.Nodup) {x : Nat} (hx : x ∈ D) (j : Nat) :
    x ∈ D.take j ↔ D.idxOf x < j := by
  have hidx : D.idxOf x < D.length := List.idxOf_lt_length_of_mem hx
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j', hj', hget⟩
    have hj'D : j' < D.length := by simp at hj'; omega
    have : D.idxOf x = j' := by
      have h1 : D[D.idxOf x] = x := List.getElem_idxOf hidx
      have h2 : D[j'] = x := hget
      exact (List.Nodup.getElem_inj hnd).mp (h1.trans h2.symm)
    simp at hj'
    omega
  · intro h
    exact ⟨D.idxOf x, by simp; omega, List.getElem_idxOf hidx⟩

theorem primRun_of_PInv {n : Nat} {inf : Int} {Ed : List Edge} {Dd : List Int} {Dn : List Nat} {D : List Nat} {pk : List Int}
    (I : PInv n inf Ed Dd Dn D pk) (hlen : D.length = n) (hpk : ∀ x ∈ pk, 0 ≤ x)
    (hEd : ∀ e ∈ Ed, e.1 < n ∧ e.2.1 < n) :
    PrimRun n (Ed.map toArc) (fun j => D.getD j 0) (fun v => D.idxOf v) (fun j => (pk.getD j 0).toNat) := by
  have hperm := Proofs.PrimStep.D_perm_range I.nodup I.lt hlen
  have hmemD : ∀ v, v < n → v ∈ D := fun v hv => hperm.symm.subset (List.mem_range.mpr hv)
  have hidx : ∀ v, v < n → D.idxOf v < n := by
    intro v hv
    have := List.idxOf_lt_length_of_mem (hmemD v hv)
    omega
  have hget : ∀ j (hj : j < D.length), D.getD j 0 = D[j] := by
    intro j hj; simp [List.getD_eq_getElem?_getD, hj]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hjD : j < D.length := by omega
    rw [hget j hjD]
    refine ⟨I.lt _ (List.getElem_mem _), ?_⟩
    have hl := List.idxOf_lt_length_of_mem (List.getElem_mem hjD)
    have h1 : D[D.idxOf D[j]]'hl = D[j] := List.getElem_idxOf hl
    exact (List.Nodup.getElem_inj I.nodup).mp h1
  · intro v hv
    refine ⟨hidx v hv, ?_⟩
    have hl := List.idxOf_lt_length_of_mem (hmemD v hv)
    show D.getD (D.idxOf v) 0 = v
    rw [hget _ hl]
    exact List.getElem_idxOf hl
  · intro j hj
    have hjD : j < D.length := by omega
    have hst := I.steps j hjD
    have hpkj : pk.getD j 0 = (pk.getD j 0) := rfl
    have hpkn : 0 ≤ pk.getD j 0 := by
      have hjp : j < pk.length := by rw [I.len]; exact hjD
      have : pk.getD j 0 = pk[j] := by simp [List.getD_eq_getElem?_getD, hjp]
      rw [this]; exact hpk _ (List.getElem_mem _)
    have hmemarc : ∀ a ∈ Ed.map toArc, ∃ e ∈ Ed, toArc e = a := fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact ⟨e, he, rfl⟩
    have hpos : ∀ x, x < n → (D.idxOf x < j ↔ x ∈ D.take j) := fun x hx => (mem_take_iff_idx I.nodup (hmemD x hx) j).symm
    show ((pk.getD j 0).toNat = 0 ∧ ∀ a ∈ Ed.map toArc, D.idxOf a.1 < j → D.idxOf a.2.1 < j) ∨
      (∃ y, y < n ∧ D.idxOf y < j ∧ (y, D.getD j 0, (pk.getD j 0).toNat) ∈ Ed.map toArc ∧
        ∀ a ∈ Ed.map toArc, D.idxOf a.1 < j → j ≤ D.idxOf a.2.1 → (pk.getD j 0).toNat ≤ a.2.2)
    rw [hget j hjD]
    unfold StepOK at hst
    rcases hst with ⟨h0, hall⟩ | ⟨y, hy, hmem, hmin⟩
    · left
      refine ⟨by rw [h0]; rfl, ?_⟩
      intro a ha h1
      obtain ⟨e, he, rfl⟩ := hmemarc a ha
      have hb := hEd e he
      show D.idxOf e.2.1 < j
      rw [hpos _ hb.2]
      have h1' : e.1 ∈ D.take j := (hpos _ hb.1).mp h1
      exact hall e he h1'
    · right
      have hyn : y < n := I.lt y (List.mem_of_mem_take hy)
      refine ⟨y, hyn, (hpos y hyn).mpr hy, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨_, hmem, rfl⟩
      · intro a ha h1 h2
        obtain ⟨e, he, rfl⟩ := hmemarc a ha
        have hb := hEd e he
        have h1' : e.1 ∈ D.take j := (hpos _ hb.1).mp h1
        have h2e : j ≤ D.idxOf e.2.1 := h2
        have h2' : e.2.1 ∉ D.take j := fun h => by have := (hpos _ hb.2).mpr h; omega
        have := hmin e he h1' h2'
        show (pk.getD j 0).toNat ≤ e.2.2.toNat
        exact Int.toNat_le_toNat this

theorem sum_toNat_cast (l : List Int) (h : ∀ x ∈ l, 0 ≤ x) : (((l.map Int.toNat).sum : Nat) : Int) = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons]
    push_cast
    rw [hl]
    omega

theorem prim_msf {n : Nat} {inf Cm : Int} {Ed : List Edge} {Dd : List Int} {Dn : List Nat} {D : List Nat} {pk : List Int}
    (I : PInv n inf Ed Dd Dn D pk) (hlen : D.length = n) (hCm : 0 ≤ Cm)
    (hEd : ∀ e ∈ Ed, e.1 < n ∧ e.2.1 < n ∧ 0 ≤ e.2.2 ∧ e.2.2 ≤ Cm) (hsym : ∀ e ∈ Ed, (e.2.1, e.1, e.2.2) ∈ Ed)
    (hpk : ∀ x ∈ pk, 0 ≤ x) :
    IsMSF n Cm.toNat (Ed.map toArc) (pk.map Int.toNat).sum ∧ (((pk.map Int.toNat).sum : Nat) : Int) = pk.sum := by
  have R := primRun_of_PInv I hlen hpk (fun e he => ⟨(hEd e he).1, (hEd e he).2.1⟩)
  have G : Graph n Cm.toNat (Ed.map toArc) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact ⟨(hEd e he).1, (hEd e he).2.1⟩
    · intro a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact List.mem_map.mpr ⟨_, hsym e he, rfl⟩
    · intro a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact Int.toNat_le_toNat (hEd e he).2.2.2
  have hspec := prim_spec G R
  have hlenpk : pk.length = n := by rw [I.len]; exact hlen
  have hW : ssum n (fun j => (pk.getD j 0).toNat) = (pk.map Int.toNat).sum := by
    rw [ssum_eq_sum]
    congr 1
    apply List.ext_getElem
    · simp [hlenpk]
    · intro j h1 h2
      have hjp : j < pk.length := by simpa [hlenpk] using h1
      simp [List.getD_eq_getElem?_getD, hjp]
  refine ⟨?_, sum_toNat_cast pk hpk⟩
  rw [← hW]
  exact ⟨hspec.2.1, hspec.2.2⟩

end Proofs.PrimBridge
