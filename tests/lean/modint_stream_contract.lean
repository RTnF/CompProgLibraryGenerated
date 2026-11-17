-- Appended to a fresh canonical class model. Source stream operations retain
-- their own formatting, failure, exception and cost contracts.
open Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.ModIntStreamModel

variable (m : UInt32) [TemplateConstraint ((2 : UInt32) ≤ m)] [Streams]

section Input
local instance : Mod Int := ⟨Int.tmod⟩
variable [SourceStreamRead "long" Int]

theorem extract_eq (input : IStream) (value : cp.ModInt m) :
    cp.op_shr_istream_ModInt input value = (do
      tick
      let (raw, input) ← SourceStreamRead.read (source := "long") input (0 : Int)
      tick
      pure (input, input,
        (⟨UInt32.ofInt (ModIntMath.signedNormalize raw m.toNat)⟩ : cp.ModInt m))) := by
  rfl

theorem extract_run (input after : IStream) (previous : cp.ModInt m)
    (raw : Int) (start finish : Nat)
    (hr : (SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1) =
      some ((raw, after), finish)) :
    (cp.op_shr_istream_ModInt input previous).run start = some
      ((after, after, (⟨UInt32.ofInt (ModIntMath.signedNormalize raw m.toNat)⟩ : cp.ModInt m)),
        finish + 1) := by
  rw [extract_eq]
  change Option.bind ((SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1))
    (fun p => some ((p.1.2, p.1.2,
      (⟨UInt32.ofInt (ModIntMath.signedNormalize p.1.1 m.toNat)⟩ : cp.ModInt m)), p.2 + 1)) = _
  rw [hr]
  rfl

theorem extract_correct (input after : IStream) (previous : cp.ModInt m)
    (raw : Int) (start finish : Nat) (hm : 0 < m.toNat)
    (hr : (SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1) =
      some ((raw, after), finish)) :
    ∃ result : cp.ModInt m,
      (cp.op_shr_istream_ModInt input previous).run start = some ((after, after, result), finish + 1) ∧
      result.x.toNat = (Int.emod raw m.toNat).toNat ∧ result.x.toNat < m.toNat := by
  refine ⟨⟨UInt32.ofInt (ModIntMath.signedNormalize raw m.toNat)⟩,
    extract_run m input after previous raw start finish hr, ?_, ?_⟩
  all_goals rw [ModIntMath.signed_normalize_eq raw m.toNat (by omega)]
  all_goals
    have h0 := Int.emod_nonneg raw (by omega : (m.toNat : Int) ≠ 0)
    have h1 := Int.emod_lt_of_pos raw (by omega : (0 : Int) < m.toNat)
    rw [ModIntMath.u32_ofInt_toNat _ h0 (by have := UInt32.toNat_lt m; omega)]
  · rfl
  · omega

theorem extract_nonreturn (input : IStream) (previous : cp.ModInt m) (start : Nat)
    (hr : (SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1) = none) :
    (cp.op_shr_istream_ModInt input previous).run start = none := by
  rw [extract_eq]
  change Option.bind ((SourceStreamRead.read (source := "long") input (0 : Int)).run (start + 1)) _ = _
  rw [hr]
  rfl
end Input

section Output
variable [SourceStreamWrite "unsigned_int" UInt32]

theorem insert_eq (output : OStream) (value : cp.ModInt m) :
    cp.op_shl_ostream_ModInt output value = (do
      tick
      let output ← SourceStreamWrite.write (source := "unsigned_int") output value.x
      pure (output, output)) := by
  rfl

theorem insert_run (output after : OStream) (value : cp.ModInt m) (start finish : Nat)
    (hr : (SourceStreamWrite.write (source := "unsigned_int") output value.x).run (start + 1) =
      some (after, finish)) :
    (cp.op_shl_ostream_ModInt output value).run start = some ((after, after), finish) := by
  rw [insert_eq]
  change Option.bind ((SourceStreamWrite.write (source := "unsigned_int") output value.x).run (start + 1))
    (fun p => some ((p.1, p.1), p.2)) = _
  rw [hr]
  rfl

theorem insert_nonreturn (output : OStream) (value : cp.ModInt m) (start : Nat)
    (hr : (SourceStreamWrite.write (source := "unsigned_int") output value.x).run (start + 1) = none) :
    (cp.op_shl_ostream_ModInt output value).run start = none := by
  rw [insert_eq]
  change Option.bind ((SourceStreamWrite.write (source := "unsigned_int") output value.x).run (start + 1)) _ = _
  rw [hr]
  rfl
end Output

end Proofs.Cpp.ModIntStreamModel
