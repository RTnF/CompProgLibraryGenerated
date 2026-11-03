import Proofs.BeatsFrame0
import Proofs.BeatsOp1Step
import Proofs.BeatsOp1Sums
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

abbrev Stp1 (qa qb : Nat) (x : Int) := stepF (clsMax qa qb x) (fun _ => Cellh.capMinC x)

theorem cls_stop1 (qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (h : clsMax qa qb x nd lo hi = Cls.stop) :
    stopP 1 qa qb x nd lo hi := by
  have : clsOf 1 qa qb x nd lo hi = Cls.stop := by simpa [clsOf] using h
  exact (clsOf_stop_iff 1 qa qb x nd lo hi (by decide)).mp this

theorem cls_whole1 (qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (h : clsMax qa qb x nd lo hi = Cls.whole) :
    ¬ stopP 1 qa qb x nd lo hi ∧ wholeP 1 qa qb x nd lo hi := by
  have : clsOf 1 qa qb x nd lo hi = Cls.whole := by simpa [clsOf] using h
  exact (clsOf_whole_iff 1 qa qb x nd lo hi (by decide)).mp this

theorem cls_down1 (qa qb : Nat) (x : Int) (nd : Nd) (lo hi : Nat) (h : clsMax qa qb x nd lo hi = Cls.down) :
    ¬ stopP 1 qa qb x nd lo hi ∧ ¬ wholeP 1 qa qb x nd lo hi := by
  constructor
  · intro hs
    have := (clsOf_stop_iff 1 qa qb x nd lo hi (by decide)).mpr hs
    simp [clsOf, h] at this
  · intro hw
    by_cases hs : stopP 1 qa qb x nd lo hi
    · have := (clsOf_stop_iff 1 qa qb x nd lo hi (by decide)).mpr hs
      simp [clsOf, h] at this
    · have := (clsOf_whole_iff 1 qa qb x nd lo hi (by decide)).mpr ⟨hs, hw⟩
      simp [clsOf, h] at this

/-- The statement proved for the subtree `t` at the heap node `k` covering `[lo, hi)` (continuation-passing). -/
def FrameI1 (mv : MV) (pre P : List Cell) (inf : Int) (n qa qb : Nat) (x : Int) (L : Nat) (Fin : BS → Nat → Prop)
    (F0 C0 Wc : Nat) (t : BT) (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap) : Prop :=
    Agree H t k → Shape lo hi t.skel → LeafOK t → BeatsModel.Inv t ys → chmaxSafe qa qb x t lo hi →
    HRel inf b H → ValidOK b → Lens b L → IdxOK t k L → LenOK b t k lo hi →
    StkRep b sp (⟨k, lo, hi⟩ :: S) → EntRep b ne E → sp + t.height + 2 ≤ L → ne + innerOf t + 1 < L → (lo ≤ hi ∧ 2 * hi < M31) →
    (∀ (bK : BS) (neK : Nat) (H' : Heap) (Enew : List Nat), HRel inf bK H' → StkRep bK (sp - 1) S → EntRep bK neK (Enew ++ E) →
      ValidOK bK → SameLen b bK →
      Star (Stp1 qa qb x) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ → (∀ e ∈ Enew, descN k e) → (∀ e ∈ Enew, InSk t k e) → SumsOK Enew H' → (∀ j, ¬ descN k j → H' j = H j) →
      Agree (upPhase Enew H') (travBT (clsMax qa qb x) (capMinBT x) t lo hi) k → Enew.length ≤ innerOf t →
      ∃ bf nef F, F ≤ F0 ∧ RunsE mv F P pre inf n 1 qa qb x bK (sp - 1) neK bf nef C0 Wc ∧ Fin bf nef) →
    ∃ bf nef F, F ≤ F0 + nodesOf t ∧ RunsE mv F P pre inf n 1 qa qb x b sp ne bf nef (nodesOf t * 117614 + C0) (nodesOf t * 47 + Wc) ∧ Fin bf nef

def FrameP1 (mv : MV) (pre P : List Cell) (inf : Int) (n qa qb : Nat) (x : Int) (L : Nat) (Fin : BS → Nat → Prop)
    (F0 C0 Wc : Nat) (t : BT) : Prop :=
  ∀ (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap),
    FrameI1 mv pre P inf n qa qb x L Fin F0 C0 Wc t k lo hi ys b sp ne S E H

theorem frame1_nodown {mv : MV} {pre P : List Cell} {inf : Int} {n qa qb : Nat} {x : Int} {L : Nat}
    (Ev : Env mv pre P inf n 1 qa qb x L) (hx : -INF < x ∧ x < INF) (Fin : BS → Nat → Prop) (F0 C0 Wc : Nat) (t : BT)
    (k lo hi : Nat) (ys : List Int) (b : BS) (sp ne : Nat) (S : List Fr) (E : List Nat) (H : Heap)
    (hnd : clsMax qa qb x t.nd lo hi ≠ Cls.down) : FrameI1 mv pre P inf n qa qb x L Fin F0 C0 Wc t k lo hi ys b sp ne S E H := by
  intro hag hsh hlf hinv hsafe hH hV hLens hidx hlen hstk hent hsp hne hlh K
  have St := stateOK_of hV hLens hidx hstk hent hH hsp hne hlh
  obtain ⟨hnd0, _⟩ := cell_of_agree inf b H hH t k lo hi hag hsh hlen
  have hroot : (H k).1 = t.nd := by
    have := hH k; rw [← this.1]; exact hnd0
  have hsp0 : 0 < sp := St.hsp
  have hspM : sp < M31 := by have := St.hspL; have := Ev.hLM; omega
  have hn1 : 1 ≤ nodesOf t := by cases t <;> (show 1 ≤ nodesS _; unfold nodesS; first | omega | (split <;> omega))
  have hcost : 117614 + C0 ≤ nodesOf t * 117614 + C0 := by have := Nat.mul_le_mul_right 117614 hn1; omega
  have hwk : 47 + Wc ≤ nodesOf t * 47 + Wc := by have := Nat.mul_le_mul_right 47 hn1; omega
  -- the traversal at this node is not a descent
  cases hc : clsMax qa qb x t.nd lo hi with
  | down => exact absurd hc hnd
  | stop =>
    have hst := cls_stop1 qa qb x t.nd lo hi hc
    rw [← hnd0] at hst
    obtain ⟨b', hit, h1, h2, h3, h4, h5⟩ := step_stop Ev St hst (by decide)
    have hK := K b' ne H [] h1 h2 (by simpa using h3) h4 h5 (Star.one (by simp [stepF, hroot, hc])) (by simp) (by simp) trivial (fun _ _ => rfl)
      (by rw [travBT_stop _ _ t lo hi hc]; simpa [upPhase] using hag) (by simp)
    obtain ⟨bf, nef, F, hFle, hr, hF⟩ := hK
    have hr' := runs_of_iter mv Ev.hnv P pre inf n 1 qa qb x b b' sp ne (sp - 1) ne hspM hsp0 hit F bf nef C0 Wc hr
    refine ⟨bf, nef, F + 1, by omega, runsE_weaken hr' hcost hwk, hF⟩
  | whole =>
    have hwh := cls_whole1 qa qb x t.nd lo hi hc
    rw [← hnd0] at hwh
    have hxne : x ≠ inf := by rw [Ev.hinfI]; exact Int.ne_of_lt hx.2
    obtain ⟨b', hit, h1, h2, h3, h4, h5⟩ := step_whole1 Ev St hwh.1 hwh.2 rfl hxne
    have hK := K b' ne (H.set k (Cellh.capMinC x (H k))) [] h1 h2 (by simpa using h3) h4 h5
      (Star.one (by simp [stepF, hroot, hc])) (by simp) (by simp) trivial
      (fun j hj => Heap.set_ne _ _ _ _ (fun e => hj (e ▸ descN_self _)))
      (by rw [travBT_whole _ _ t lo hi hc]; simpa [upPhase] using agree_capMinBT H t k x hag) (by simp)
    obtain ⟨bf, nef, F, hFle, hr, hF⟩ := hK
    have hr' := runs_of_iter mv Ev.hnv P pre inf n 1 qa qb x b b' sp ne (sp - 1) ne hspM hsp0 hit F bf nef C0 Wc hr
    exact ⟨bf, nef, F + 1, by omega, runsE_weaken hr' hcost hwk, hF⟩


end Proofs.BeatsRep
