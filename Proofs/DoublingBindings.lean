import Proofs.Generated.DoublingBindings

namespace Proofs.DoublingBindings
open Proofs.CppVectorBindings

-- Parameter metadata only: no theorem about doubling's function body.
theorem generated_parameters : DoublingBindingInstance.doubling =
    [.vector ⟨32,true,false⟩ false,.scalar ⟨64,false,false⟩ false true] := rfl

end Proofs.DoublingBindings
