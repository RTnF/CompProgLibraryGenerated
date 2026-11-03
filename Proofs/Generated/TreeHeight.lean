-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.TreeHeightInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «tree_height_std_vector_long_long» : NProgram := ⟨[.vector ⟨64, true, false⟩ false, .vector ⟨64, true, false⟩ false, .vector ⟨64, true, false⟩ true, .scalar ⟨32, true, false⟩ false true],.unit,(.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 4) (.variable ⟨32, true, false⟩ 3)) (.sequence (.scope (.sequence (.primitive (.declare ⟨64, true, false⟩ true (.read ⟨64, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 4))))) (.sequence (.primitive (.declare ⟨64, true, false⟩ true (.read ⟨64, true, false⟩ (.local 1) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 4))))) (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.variable ⟨64, true, false⟩ 5) (.variable ⟨64, true, false⟩ 6)) (.sequence (.scope (.sequence (.primitive (.write (.local 2) ⟨64, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 4)) (.variable ⟨64, true, false⟩ 6))) (.primitive .skip))) (.primitive .skip)) (.sequence (.scope (.sequence (.primitive (.write (.local 2) ⟨64, true, false⟩ (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 4)) (.variable ⟨64, true, false⟩ 5))) (.primitive .skip))) (.primitive .skip))) (.primitive .skip))))) (.sequence (.primitive (.assign 4 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 4) (.literal ⟨32, true, false⟩ (1))))) (.primitive .skip)))) (.primitive .skip)))) (.primitive .skip))⟩

end Proofs.TreeHeightInstance
