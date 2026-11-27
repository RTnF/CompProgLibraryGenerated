import Proofs.Cpp.Gen.TreeMultiset

namespace Proofs.Cpp.TreeMultiset.IntBindings

instance : Proofs.Cpp.ConditionalResult Int Int := ⟨Int, id, id⟩

instance : Proofs.Cpp.Conv (Proofs.Cpp.ConditionalResult.Value (Left := Int) (Right := Int)) Int :=
  ⟨id⟩

end Proofs.Cpp.TreeMultiset.IntBindings
