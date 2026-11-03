import Proofs.BeatsRepInv
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.MultiVec
open Proofs.ForLoop (ci)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.BellmanFordExec (M31)
set_option maxRecDepth 100000

/-- The sums of the child counts that `update` computes at node `e` are valid `long long`s. -/
def SumOK (H : Heap) (e : Nat) : Prop :=
  s64.valid ((H (2 * e + 1)).1.mc + (H (2 * e + 2)).1.mc) = true ∧ s64.valid ((H (2 * e + 1)).1.mnc + (H (2 * e + 2)).1.mnc) = true

def SumsOK : List Nat → Heap → Prop
  | [], _ => True
  | e :: E, H => SumOK H e ∧ SumsOK E (updateH H e)

theorem SumsOK_append : ∀ (A B : List Nat) (H : Heap), SumsOK (A ++ B) H ↔ SumsOK A H ∧ SumsOK B (upPhase A H)
  | [], B, H => by simp [SumsOK, upPhase]
  | e :: A, B, H => by
    simp only [List.cons_append, SumsOK, upPhase_cons]
    rw [SumsOK_append A B (updateH H e)]
    exact and_assoc.symm

theorem descN_left (c e : Nat) (he : descN c e) : descN c (2 * e + 1) :=
  descN_trans he (descN.step _ (by omega) (by
    have : (2 * e + 1 - 1) / 2 = e := by omega
    rw [this]; exact descN.self))

theorem descN_right (c e : Nat) (he : descN c e) : descN c (2 * e + 2) :=
  descN_trans he (descN.step _ (by omega) (by
    have : (2 * e + 2 - 1) / 2 = e := by omega
    rw [this]; exact descN.self))

theorem SumOK_congr (c e : Nat) (he : descN c e) {G G' : Heap} (h : EqOn c G G') (hs : SumOK G e) : SumOK G' e := by
  have h1 := h _ (descN_left c e he)
  have h2 := h _ (descN_right c e he)
  unfold SumOK at hs ⊢
  rw [← h1, ← h2]; exact hs

theorem SumsOK_congr (c : Nat) : ∀ (E : List Nat), (∀ e ∈ E, descN c e) → ∀ (G G' : Heap), EqOn c G G' → SumsOK E G → SumsOK E G'
  | [], _, _, _, _, _ => trivial
  | e :: E, hE, G, G', h, hs => by
    refine ⟨SumOK_congr c e (hE e List.mem_cons_self) h hs.1, ?_⟩
    exact SumsOK_congr c E (fun x hx => hE x (List.mem_cons_of_mem _ hx)) _ _
      (updateH_local G G' e c (hE e List.mem_cons_self) h) hs.2

theorem desc_cnt (nd : Nd) (ys : List Int) (h : Desc nd ys) :
    0 ≤ nd.mc ∧ nd.mc ≤ ys.length ∧ 0 ≤ nd.mnc ∧ nd.mnc ≤ ys.length := by
  obtain ⟨-, -, h3, -, -, h6⟩ := h
  have a : cmxL ys ≤ ys.length := List.countP_le_length
  have b : cmnL ys ≤ ys.length := List.countP_le_length
  omega

theorem SumOK_of_desc (H : Heap) (e : Nat) (xl xr : List Int) (hl : Desc (H (2 * e + 1)).1 xl) (hr : Desc (H (2 * e + 2)).1 xr)
    (hb : xl.length + xr.length < M31) : SumOK H e := by
  obtain ⟨a1, a2, a3, a4⟩ := desc_cnt _ _ hl
  obtain ⟨b1, b2, b3, b4⟩ := desc_cnt _ _ hr
  have hM : M31 = 2147483648 := rfl
  unfold INF at *
  constructor <;> apply s64_valid_of_bounds <;> unfold INF <;> omega

end Proofs.BeatsRep
