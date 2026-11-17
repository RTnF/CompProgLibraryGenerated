-- Appended to a freshly translated source by test_lean_model_source_streams.py.
-- Stream states, formatting, failure and operation costs remain arbitrary.
open Proofs.Cpp Proofs.Cpp.Gen

theorem source_word_extract_contract [Streams] [SourceStreamRead "long" Int]
    (input : IStream) (value : cp.Word) :
    cp.op_shr_istream_Word input value = (do
      tick
      let (temporary, input) ← SourceStreamRead.read (source := "long") input (0 : Int)
      let value ← cp.Word.set_ value temporary
      pure (input, input, value)) := by
  rfl

theorem source_word_insert_contract [Streams] [SourceStreamWrite "unsigned_int" UInt32]
    (output : OStream) (value : cp.Word) :
    cp.op_shl_ostream_Word output value = (do
      tick
      let output ← SourceStreamWrite.write (source := "unsigned_int") output value.x
      pure (output, output)) := by
  rfl

theorem source_int_extract_contract [Streams] [SourceStreamRead "int" Int]
    (input : IStream) (old : Int) :
    cp.read32 input old = (do
      tick
      let (value, input) ← SourceStreamRead.read (source := "int") input old
      pure (input, input, value)) := by
  rfl

theorem source_long_extract_contract [Streams] [SourceStreamRead "long" Int]
    (input : IStream) (old : Int) :
    cp.readlong input old = (do
      tick
      let (value, input) ← SourceStreamRead.read (source := "long") input old
      pure (input, input, value)) := by
  rfl

theorem source_long_long_extract_contract [Streams] [SourceStreamRead "long_long" Int]
    (input : IStream) (old : Int) :
    cp.read64 input old = (do
      tick
      let (value, input) ← SourceStreamRead.read (source := "long_long") input old
      pure (input, input, value)) := by
  rfl
