-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.GcdU64Instance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «gcd_u64» : NProgram := ⟨[.scalar ⟨64, false, false⟩ false true, .scalar ⟨64, false, false⟩ false true],.scalar ⟨64, false, false⟩,(.sequence (.whileLoop (.binary ⟨1, false, true⟩ .ne (.variable ⟨64, false, false⟩ 1) (.cast ⟨64, false, false⟩ (.literal ⟨32, true, false⟩ (0)))) (.sequence (.scope (.sequence (.primitive (.declare ⟨64, false, false⟩ true (.divrem ⟨64, false, false⟩ true (.variable ⟨64, false, false⟩ 0) (.variable ⟨64, false, false⟩ 1)))) (.sequence (.primitive (.assign 0 ⟨64, false, false⟩ (.variable ⟨64, false, false⟩ 1))) (.sequence (.primitive (.assign 1 ⟨64, false, false⟩ (.variable ⟨64, false, false⟩ 2))) (.primitive .skip))))) (.primitive .skip))) (.sequence (.primitive (.ret (.variable ⟨64, false, false⟩ 0))) (.primitive .skip)))⟩

end Proofs.GcdU64Instance
