-- Generated syntax-directed scalar state IR.
import Proofs.CppState

namespace Proofs.SafeModInstance
open Proofs.CppScalar Proofs.CppState

def «safe_mod» : StateProgram :=
  ⟨[⟨⟨64, true, false⟩, false, true⟩, ⟨⟨64, true, false⟩, false, true⟩], ⟨64, true, false⟩,
   (.scope (.sequence (.assign 0 (.divrem ⟨64, true, false⟩ true (.variable ⟨64, true, false⟩ 0) (.variable ⟨64, true, false⟩ 1))) (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.variable ⟨64, true, false⟩ 0) (.cast ⟨64, true, false⟩ (.literal ⟨32, true, false⟩ (0)))) (.scope (.scope (.sequence (.assign 0 (.binary ⟨64, true, false⟩ .add (.variable ⟨64, true, false⟩ 0) (.variable ⟨64, true, false⟩ 1))) .skip))) .skip) (.sequence (.ret (.variable ⟨64, true, false⟩ 0)) .skip))))⟩

end Proofs.SafeModInstance
