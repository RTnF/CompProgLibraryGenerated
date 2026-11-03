-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.CountrZeroInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «countr_zero_u64» : NProgram := ⟨[.scalar ⟨64, false, false⟩ false true],.scalar ⟨32, true, false⟩,(.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.whileLoop (.logical true (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 1) (.literal ⟨32, true, false⟩ (64))) (.binary ⟨1, false, true⟩ .eq (.divrem ⟨64, false, false⟩ true (.variable ⟨64, false, false⟩ 0) (.cast ⟨64, false, false⟩ (.literal ⟨32, true, false⟩ (2)))) (.cast ⟨64, false, false⟩ (.literal ⟨32, true, false⟩ (0))))) (.sequence (.scope (.sequence (.primitive (.assign 0 ⟨64, false, false⟩ (.divrem ⟨64, false, false⟩ false (.variable ⟨64, false, false⟩ 0) (.cast ⟨64, false, false⟩ (.literal ⟨32, true, false⟩ (2)))))) (.sequence (.primitive (.assign 1 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 1) (.literal ⟨32, true, false⟩ (1))))) (.primitive .skip)))) (.primitive .skip))) (.sequence (.primitive (.ret (.variable ⟨32, true, false⟩ 1))) (.primitive .skip))))⟩

end Proofs.CountrZeroInstance
