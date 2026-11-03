import Proofs.CppNestedProgram

namespace Proofs.CppPeakComponents
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings

theorem max_mono (a : Nat) {b c : Nat} (h : b ≤ c) : max a b ≤ max a c :=
  Nat.max_le.mpr ⟨Nat.le_max_left _ _,Nat.le_trans h (Nat.le_max_right _ _)⟩

-- Historical outer peaks are carried separately from the two components.
structure Grows (s t : NState) : Prop where
  scalar : s.scalars.peak ≤ t.scalars.peak
  storage : s.frame.state.storage.peak ≤ t.frame.state.storage.peak
  outer : t.peak ≤ max s.peak (t.scalars.peak+t.frame.state.storage.peak)

theorem Grows.refl (s : NState) : Grows s s := ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_max_left _ _⟩

theorem Grows.trans {s t u : NState} (a : Grows s t) (b : Grows t u) : Grows s u := by
  refine ⟨Nat.le_trans a.scalar b.scalar,Nat.le_trans a.storage b.storage,?_⟩
  have sum := Nat.add_le_add b.scalar b.storage
  exact Nat.le_trans b.outer (Nat.max_le.mpr ⟨Nat.le_trans a.outer
    (max_mono _ sum),Nat.le_max_right _ _⟩)

theorem uncharged (s t : NState) (scalar : s.scalars.peak ≤ t.scalars.peak)
    (storage : s.frame.state.storage.peak ≤ t.frame.state.storage.peak) (peak : t.peak = s.peak) : Grows s t := by
  refine ⟨scalar,storage,?_⟩
  rw [peak]
  exact Nat.le_max_left _ _

theorem reframe_raw (s : NState) (frame : Frame) (peak : s.frame.state.storage.peak ≤ frame.state.storage.peak) :
    Grows s ({s with frame := frame} : NState) := uncharged _ _ (Nat.le_refl _) peak rfl

theorem observe (s : NState) : Grows s s.observe :=
  ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_refl _⟩

theorem reframe (s : NState) (frame : Frame) (peak : s.frame.state.storage.peak ≤ frame.state.storage.peak) :
    Grows s ({s with frame := frame} : NState).observe := ⟨Nat.le_refl _,peak,Nat.le_refl _⟩

theorem rescalar (s : NState) (scalars : Proofs.CppState.State) (peak : s.scalars.peak ≤ scalars.peak) :
    Grows s ({s with scalars := scalars} : NState).observe := ⟨peak,Nat.le_refl _,Nat.le_refl _⟩

theorem charge (s : NState) (work temporary : Nat) : Grows s (s.charge work temporary) := by
  apply rescalar s _
  exact Nat.le_max_left _ _

theorem release (s outer : NState) : Grows s (s.release outer) :=
  ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_max_left _ _⟩

theorem Grows.bound {s t : NState} (effects : Grows s t) (scalarBound storageBound : Nat)
    (scalar : t.scalars.peak ≤ scalarBound) (storage : t.frame.state.storage.peak ≤ storageBound) :
    t.peak ≤ max s.peak (scalarBound+storageBound) :=
  Nat.le_trans effects.outer (max_mono _ (Nat.add_le_add scalar storage))

end Proofs.CppPeakComponents
