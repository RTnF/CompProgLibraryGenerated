-- Appended to the freshly generated complete original Ratio model by
-- tests/test_ratio_stream_model.py. All stream operations and their costs are parameters.
open Proofs.Cpp Proofs.Cpp.Gen

theorem ratio_extract_contract {T : Type} [Streams] [StreamRead T]
    (input : IStream) (r : cp.Ratio T) :
    cp.op_shr_istream_Ratio input r = (do
      tick
      let (n, input) ← StreamRead.read input r.n
      let (d, input) ← StreamRead.read input r.d
      pure (input, input, (⟨n, d⟩ : cp.Ratio T))) := by
  rfl

theorem ratio_insert_contract {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output : OStream) (r : cp.Ratio T) :
    cp.op_shl_ostream_Ratio output r = (do
      tick
      let mut output ← StreamWrite.write output r.n
      if decide (r.d > (1 : T)) then
        output ← StreamWrite.write output (⟨47⟩ : StreamChar)
        output ← StreamWrite.write output r.d
      pure (output, output)) := by
  rfl

open Std.Do

theorem ratio_extract_run {T : Type} [Streams] [StreamRead T]
    (input input₁ input₂ : IStream) (r : cp.Ratio T) (n d : T) (t0 c₁ c₂ : Nat)
    (hn : (StreamRead.read input r.n).run (t0 + 1) = some ((n, input₁), c₁))
    (hd : (StreamRead.read input₁ r.d).run c₁ = some ((d, input₂), c₂)) :
    (cp.op_shr_istream_Ratio input r).run t0 =
      some ((input₂, input₂, (⟨n, d⟩ : cp.Ratio T)), c₂) := by
  rw [ratio_extract_contract]
  change Option.bind ((StreamRead.read input r.n).run (t0 + 1)) (fun a =>
    Option.bind ((StreamRead.read a.1.2 r.d).run a.2)
      (fun b => some ((b.1.2, b.1.2, (⟨a.1.1, b.1.1⟩ : cp.Ratio T)), b.2))) = _
  rw [hn]
  simp only [Option.bind_some]
  rw [hd]
  rfl

theorem ratio_insert_integer_run {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output output₁ : OStream)
    (r : cp.Ratio T) (t0 c₁ : Nat) (hshort : ¬r.d > (1 : T))
    (hn : (StreamWrite.write output r.n).run (t0 + 1) = some (output₁, c₁)) :
    (cp.op_shl_ostream_Ratio output r).run t0 = some ((output₁, output₁), c₁) := by
  simp only [ratio_insert_contract, hshort, decide_false, Bool.false_eq_true, ↓reduceIte]
  change Option.bind ((StreamWrite.write output r.n).run (t0 + 1))
    (fun a => some ((a.1, a.1), a.2)) = _
  rw [hn]
  rfl

theorem ratio_insert_fraction_run {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output output₁ output₂ output₃ : OStream)
    (r : cp.Ratio T) (t0 c₁ c₂ c₃ : Nat) (hlong : r.d > (1 : T))
    (hn : (StreamWrite.write output r.n).run (t0 + 1) = some (output₁, c₁))
    (hslash : (StreamWrite.write output₁ (⟨47⟩ : StreamChar)).run c₁ = some (output₂, c₂))
    (hd : (StreamWrite.write output₂ r.d).run c₂ = some (output₃, c₃)) :
    (cp.op_shl_ostream_Ratio output r).run t0 = some ((output₃, output₃), c₃) := by
  simp only [ratio_insert_contract, hlong, decide_true, ↓reduceIte]
  change Option.bind ((StreamWrite.write output r.n).run (t0 + 1)) (fun a =>
    Option.bind ((StreamWrite.write a.1 (⟨47⟩ : StreamChar)).run a.2) (fun b =>
      Option.bind ((StreamWrite.write b.1 r.d).run b.2) (fun c => some ((c.1, c.1), c.2)))) = _
  rw [hn]
  simp only [Option.bind_some]
  rw [hslash]
  simp only [Option.bind_some]
  rw [hd]
  rfl

theorem ratio_extract_work {T : Type} [Streams] [StreamRead T]
    (input input₁ input₂ : IStream) (r : cp.Ratio T) (n d : T) (t0 c₁ c₂ work₁ work₂ : Nat)
    (hn : (StreamRead.read input r.n).run (t0 + 1) = some ((n, input₁), c₁))
    (hd : (StreamRead.read input₁ r.d).run c₁ = some ((d, input₂), c₂))
    (hc₁ : c₁ ≤ t0 + 1 + work₁) (hc₂ : c₂ ≤ c₁ + work₂) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_shr_istream_Ratio input r
    ⦃⇓ q c => ⌜q = (input₂, input₂, (⟨n, d⟩ : cp.Ratio T)) ∧
      c ≤ t0 + 1 + work₁ + work₂⌝⦄ := by
  exact triple_of_run _ _ (ratio_extract_run input input₁ input₂ r n d t0 c₁ c₂ hn hd)
    ⟨rfl, by omega⟩

theorem ratio_insert_integer_work {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output output₁ : OStream)
    (r : cp.Ratio T) (t0 c₁ work : Nat) (hshort : ¬r.d > (1 : T))
    (hn : (StreamWrite.write output r.n).run (t0 + 1) = some (output₁, c₁))
    (hc : c₁ ≤ t0 + 1 + work) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_shl_ostream_Ratio output r
    ⦃⇓ q c => ⌜q = (output₁, output₁) ∧ c ≤ t0 + 1 + work⌝⦄ := by
  exact triple_of_run _ _ (ratio_insert_integer_run output output₁ r t0 c₁ hshort hn) ⟨rfl, hc⟩

theorem ratio_insert_fraction_work {T : Type} [Streams] [One T] [LT T] [DecidableLT T]
    [StreamWrite T] [StreamWrite StreamChar] (output output₁ output₂ output₃ : OStream)
    (r : cp.Ratio T) (t0 c₁ c₂ c₃ work₁ work₂ work₃ : Nat) (hlong : r.d > (1 : T))
    (hn : (StreamWrite.write output r.n).run (t0 + 1) = some (output₁, c₁))
    (hslash : (StreamWrite.write output₁ (⟨47⟩ : StreamChar)).run c₁ = some (output₂, c₂))
    (hd : (StreamWrite.write output₂ r.d).run c₂ = some (output₃, c₃))
    (hc₁ : c₁ ≤ t0 + 1 + work₁) (hc₂ : c₂ ≤ c₁ + work₂) (hc₃ : c₃ ≤ c₂ + work₃) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.op_shl_ostream_Ratio output r
    ⦃⇓ q c => ⌜q = (output₃, output₃) ∧ c ≤ t0 + 1 + work₁ + work₂ + work₃⌝⦄ := by
  exact triple_of_run _ _
    (ratio_insert_fraction_run output output₁ output₂ output₃ r t0 c₁ c₂ c₃ hlong hn hslash hd)
    ⟨rfl, by omega⟩

/-- Fixed integer fields retained by extraction, plus the larger of the two
sequential stream-operation peaks. Stream buffers belong to those contracts. -/
theorem ratio_extract_payload (oldn oldd n d : Int) (bits first second peak : Nat)
    (holdn : oldn.natAbs ≤ 2 ^ bits) (holdd : oldd.natAbs ≤ 2 ^ bits)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hfirst : first ≤ peak) (hsecond : second ≤ peak) :
    RatioSpace.signedPayloadBits [oldn, oldd, n, d] + max first second ≤
      8 * (bits + 1) + peak := by
  exact Nat.add_le_add
    (RatioArithmeticSpace.equality_context_bits oldn oldd n d bits holdn holdd hn hd)
    (max_le hfirst hsecond)

/-- Output retains a fixed envelope of integer values; stream-operation peaks
are composed by maximum, not by the number of characters already emitted. -/
theorem ratio_insert_payload (n d : Int) (bits first slash last peak : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits)
    (hfirst : first ≤ peak) (hslash : slash ≤ peak) (hlast : last ≤ peak) :
    RatioSpace.signedPayloadBits (RatioArithmeticSpace.copyContext n d) +
      max first (max slash last) ≤ 8 * (bits + 1) + peak := by
  exact Nat.add_le_add (RatioArithmeticSpace.copy_context_bits n d bits hn hd)
    (max_le hfirst (max_le hslash hlast))
