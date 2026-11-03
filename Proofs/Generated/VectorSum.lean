-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.VectorSumInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «vector_sum_std_vector_long_long» : NProgram := ⟨[.vector ⟨64, true, false⟩ false],.scalar ⟨64, true, false⟩,(.sequence (.primitive (.declare ⟨64, true, false⟩ true (.cast ⟨64, true, false⟩ (.literal ⟨32, true, false⟩ (0))))) (.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 2) (.cast ⟨32, true, false⟩ (.size (.integer ⟨64, true, false⟩) (.local 0)))) (.sequence (.scope (.sequence (.primitive (.assign 1 ⟨64, true, false⟩ (.binary ⟨64, true, false⟩ .add (.variable ⟨64, true, false⟩ 1) (.read ⟨64, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 2)))))) (.primitive .skip))) (.sequence (.primitive (.assign 2 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 2) (.literal ⟨32, true, false⟩ (1))))) (.primitive .skip)))) (.primitive .skip)))) (.sequence (.primitive (.ret (.variable ⟨64, true, false⟩ 1))) (.primitive .skip))))⟩

end Proofs.VectorSumInstance
