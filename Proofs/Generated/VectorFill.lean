-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.VectorFillInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «vector_fill_std_vector_long_long» : NProgram := ⟨[.vector ⟨64, true, false⟩ true, .scalar ⟨64, true, false⟩ false true],.unit,(.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 2) (.cast ⟨32, true, false⟩ (.size (.integer ⟨64, true, false⟩) (.local 0)))) (.sequence (.scope (.sequence (.primitive (.write (.local 0) ⟨64, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 2)) (.variable ⟨64, true, false⟩ 1))) (.primitive .skip))) (.sequence (.primitive (.assign 2 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 2) (.literal ⟨32, true, false⟩ (1))))) (.primitive .skip)))) (.primitive .skip)))) (.primitive .skip))⟩

end Proofs.VectorFillInstance
