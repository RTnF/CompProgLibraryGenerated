-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.TreeArcCostsInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «tree_arc_costs_std_vector_long_long» : NProgram := ⟨[.vector ⟨64, true, false⟩ false, .vector ⟨64, true, false⟩ true, .scalar ⟨32, true, false⟩ false true],.unit,(.sequence (.scope (.sequence (.primitive (.declare ⟨32, true, false⟩ true (.literal ⟨32, true, false⟩ (0)))) (.sequence (.whileLoop (.binary ⟨1, false, true⟩ .lt (.variable ⟨32, true, false⟩ 3) (.variable ⟨32, true, false⟩ 2)) (.sequence (.scope (.sequence (.primitive (.declare ⟨64, true, false⟩ true (.read ⟨64, true, false⟩ (.local 0) (.cast ⟨64, false, false⟩ (.variable ⟨32, true, false⟩ 3))))) (.sequence (.primitive (.write (.local 1) ⟨64, true, false⟩ (.cast ⟨64, false, false⟩ (.binary ⟨32, true, false⟩ .mul (.literal ⟨32, true, false⟩ (2)) (.variable ⟨32, true, false⟩ 3))) (.variable ⟨64, true, false⟩ 4))) (.sequence (.primitive (.write (.local 1) ⟨64, true, false⟩ (.cast ⟨64, false, false⟩ (.binary ⟨32, true, false⟩ .add (.binary ⟨32, true, false⟩ .mul (.literal ⟨32, true, false⟩ (2)) (.variable ⟨32, true, false⟩ 3)) (.literal ⟨32, true, false⟩ (1)))) (.variable ⟨64, true, false⟩ 4))) (.primitive .skip))))) (.sequence (.primitive (.assign 3 ⟨32, true, false⟩ (.binary ⟨32, true, false⟩ .add (.variable ⟨32, true, false⟩ 3) (.literal ⟨32, true, false⟩ (1))))) (.primitive .skip)))) (.primitive .skip)))) (.primitive .skip))⟩

end Proofs.TreeArcCostsInstance
