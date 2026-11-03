-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.XorshiftInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «Xor64_new0» : NProgram := ⟨[.scalar ⟨64, false, false⟩ false true],.scalar ⟨64, false, false⟩,(.sequence (.primitive (.ret (.variable ⟨64, false, false⟩ 0))) (.primitive .skip))⟩
def «Xor64_get» : NProgram := ⟨[.scalar ⟨64, false, false⟩ true true],.scalar ⟨64, false, false⟩,(.sequence (.primitive (.declare ⟨64, false, false⟩ true (.variable ⟨64, false, false⟩ 0))) (.sequence (.primitive (.assign 1 ⟨64, false, false⟩ (.binary ⟨64, false, false⟩ .bxor (.variable ⟨64, false, false⟩ 1) (.binary ⟨64, false, false⟩ .shl (.variable ⟨64, false, false⟩ 1) (.literal ⟨32, true, false⟩ (7)))))) (.sequence (.primitive (.assign 0 ⟨64, false, false⟩ (.binary ⟨64, false, false⟩ .bxor (.variable ⟨64, false, false⟩ 1) (.binary ⟨64, false, false⟩ .shr (.variable ⟨64, false, false⟩ 1) (.literal ⟨32, true, false⟩ (9)))))) (.sequence (.primitive (.ret (.variable ⟨64, false, false⟩ 0))) (.primitive .skip)))))⟩

end Proofs.XorshiftInstance
