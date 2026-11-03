-- Generated syntax-directed scalar state IR.
import Proofs.CppLoop

namespace Proofs.BitWidthU64Instance
open Proofs.CppScalar Proofs.CppState

open Proofs.CppLoop

def «bit_width_u64» : LoopProgram :=
  ⟨[⟨⟨64, false, false⟩, false, true⟩], ⟨32, true, false⟩,
   (.scope (.sequence (.sequence (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0))) .skip) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨64, false, false⟩ 0) (.cast ⟨64, false, false⟩ (.literal ⟨32, true, false⟩ (0)))) (.scope (.scope (.sequence (.assign 1 (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 1) (.literal ⟨32, true, false⟩ (1)))) (.sequence (.assign 0 (.divrem ⟨64, false, false⟩ false (.variable ⟨64, false, false⟩ 0) (.cast ⟨64, false, false⟩ (.literal ⟨32, true, false⟩ (2))))) .skip))))) (.sequence (.ret (.variable ⟨32, true, false⟩ 1)) .skip))))⟩

end Proofs.BitWidthU64Instance
