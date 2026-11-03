import Proofs.LazySegCtor
import Proofs.LazySegRange

namespace Proofs.LazySegCtorRep
open Proofs.SegTreeMath Proofs.LazySegMath
open Proofs.LazySegChmin (chminMon)
open Proofs.SegmentTreeExec (maxMon)
open Proofs.LazySegBlocks (getD_dflt)

theorem rep_ctor (n N : Nat) (Vin Vf : List Int) (hN : 0 < N) (hnN : n ≤ N) (hVin : Vin.length = n)
    (hVinV : AllV maxMon Vin) (hTI : TInv maxMon Vf N) (hVf : AllV maxMon Vf) (hlen : Vf.length = 2 * N)
    (hleaf1 : ∀ i, i < n → Vf.getD (N + i) 0 = Vin.getD i 0)
    (hleaf2 : ∀ i, n ≤ i → i < N → Vf.getD (N + i) 0 = Proofs.LazySegCtor.EMIN) :
    Rep chminMon N (Vin ++ List.replicate (N - n) Proofs.LazySegCtor.EMIN) Vf (List.replicate N 9223372036854775807) := by
  have hemin : maxMon.V Proofs.LazySegCtor.EMIN := Proofs.LazySegCtor.emin_valid_c
  have hAlen : (Vin ++ List.replicate (N - n) Proofs.LazySegCtor.EMIN).length = N := by simp [hVin]; omega
  have hAV : AllV chminMon.toMon (Vin ++ List.replicate (N - n) Proofs.LazySegCtor.EMIN) := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hVinV x h
    · rw [(List.mem_replicate.mp h).2]; exact hemin
  have hlz : ∀ j, (List.replicate N (9223372036854775807 : Int)).getD j chminMon.fid = chminMon.fid := by
    intro j
    by_cases hj : j < N
    · simp [List.getD_eq_getElem?_getD, hj]; rfl
    · simp [List.getD_eq_getElem?_getD, hj]
  have hF : AllF chminMon (List.replicate N (9223372036854775807 : Int)) := by
    intro x hx
    rw [(List.mem_replicate.mp hx).2]; exact chminMon.fid_v
  refine ⟨hlen, by simp, hAlen, hVf, hF, hAV, ?_⟩
  intro d hd1 hd2 _
  rw [G_allfid chminMon _ hF hlz d, chminMon.mp_id _ (getD_Ve chminMon Vf hVf d (by omega))]
  rw [← getD_dflt Vf d 0 chminMon.e (by omega)]
  apply tr_of_tinv chminMon Vf N _ hTI _ d hd1 hd2
  intro x hx1 hx2
  unfold lfA
  obtain ⟨i, rfl⟩ : ∃ i, x = N + i := ⟨x - N, by omega⟩
  rw [Nat.add_sub_cancel_left]
  by_cases hi : i < n
  · rw [hleaf1 i hi, getD_dflt Vin i 0 chminMon.e (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hi, hVin]
  · rw [hleaf2 i (by omega) (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_replicate, if_pos (by omega)]
    rfl

end Proofs.LazySegCtorRep
