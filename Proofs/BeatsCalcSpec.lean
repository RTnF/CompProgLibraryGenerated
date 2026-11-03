import Proofs.BeatsCalcFrame
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

def specMax (qa qb : Nat) : CSpec qa qb where
  val := fun nd => nd.mx
  comb := max
  calcF := calcMaxBT qa qb
  idv := -INF
  RB := fun r => -INF ≤ r
  hstop := by
    intro t lo hi h
    have hs := clsR_stop qa qb t.nd lo hi h
    cases t with
    | leaf nd => conv_lhs => rw [calcMaxBT]
                 rw [if_pos hs]
    | node nd tg l r => conv_lhs => rw [calcMaxBT]
                        rw [if_pos hs]
  hwhole := by
    intro t lo hi h
    obtain ⟨hn, hc⟩ := clsR_whole qa qb t.nd lo hi h
    cases t with
    | leaf nd => conv_lhs => rw [calcMaxBT]
                 rw [if_neg hn]; rfl
    | node nd tg l r => conv_lhs => rw [calcMaxBT]
                        rw [if_neg hn, if_pos hc]; rfl
  hdown := by
    intro nd tg l r lo hi h
    obtain ⟨hn, hc⟩ := clsR_down qa qb nd lo hi h
    conv_lhs => rw [calcMaxBT]
    rw [if_neg hn, if_neg hc]
  hid := fun r hr => Int.max_eq_left hr
  hRB := fun r v hr => Int.le_trans hr (Int.le_max_left _ _)
  hassoc := fun r p q => by omega
  hvalid := fun r v hr hv => by
    rcases Int.le_total r v with h | h
    · rw [Int.max_eq_right h]; exact hv
    · rw [Int.max_eq_left h]; exact hr
  hvalNd := fun b i hV h0 h3 => by
    have := getD_mem_valid b.mxv i h0 hV.v0
    exact this

def specMin (qa qb : Nat) : CSpec qa qb where
  val := fun nd => nd.mn
  comb := min
  calcF := calcMinBT qa qb
  idv := INF
  RB := fun r => r ≤ INF
  hstop := by
    intro t lo hi h
    have hs := clsR_stop qa qb t.nd lo hi h
    cases t with
    | leaf nd => conv_lhs => rw [calcMinBT]
                 rw [if_pos hs]
    | node nd tg l r => conv_lhs => rw [calcMinBT]
                        rw [if_pos hs]
  hwhole := by
    intro t lo hi h
    obtain ⟨hn, hc⟩ := clsR_whole qa qb t.nd lo hi h
    cases t with
    | leaf nd => conv_lhs => rw [calcMinBT]
                 rw [if_neg hn]; rfl
    | node nd tg l r => conv_lhs => rw [calcMinBT]
                        rw [if_neg hn, if_pos hc]; rfl
  hdown := by
    intro nd tg l r lo hi h
    obtain ⟨hn, hc⟩ := clsR_down qa qb nd lo hi h
    conv_lhs => rw [calcMinBT]
    rw [if_neg hn, if_neg hc]
  hid := fun r hr => Int.min_eq_left hr
  hRB := fun r v hr => Int.le_trans (Int.min_le_left _ _) hr
  hassoc := fun r p q => by omega
  hvalid := fun r v hr hv => by
    rcases Int.le_total r v with h | h
    · rw [Int.min_eq_left h]; exact hr
    · rw [Int.min_eq_right h]; exact hv
  hvalNd := fun b i hV h0 h3 => by
    have := getD_mem_valid b.mnv i h3 hV.v3
    exact this

theorem wholeStep_max {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (hop : op = 0) :
    WholeStep mv pre P inf n op qa qb L (specMax qa qb) := by
  intro x Ev b sp W0 W1 W2 S H St hn hc
  obtain ⟨b', hit, h1, h2, h3, h4⟩ := cstep_whole0 Ev St hn hc hop
  refine ⟨b', ?_, h1, h2, h3, h4⟩
  have e : (if x < b.mxv.getD W0 0 then b.mxv.getD W0 0 else x) = max x (b.mxv.getD W0 0) := by
    by_cases h : x < b.mxv.getD W0 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [e] at hit; exact hit

theorem wholeStep_min {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (hop : op = 1) :
    WholeStep mv pre P inf n op qa qb L (specMin qa qb) := by
  intro x Ev b sp W0 W1 W2 S H St hn hc
  obtain ⟨b', hit, h1, h2, h3, h4⟩ := cstep_whole1 Ev St hn hc hop
  refine ⟨b', ?_, h1, h2, h3, h4⟩
  have e : (if b.mnv.getD W0 0 < x then b.mnv.getD W0 0 else x) = min x (b.mnv.getD W0 0) := by
    by_cases h : b.mnv.getD W0 0 < x
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [e] at hit; exact hit

end Proofs.BeatsRep
