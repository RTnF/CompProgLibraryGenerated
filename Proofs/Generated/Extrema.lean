-- Generated from audited Clang vector operations and scalar syntax.
import Proofs.CppNestedCall

namespace Proofs.ExtremaLibInstance
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall

def «chmax_long_long» : NProgram := ⟨[.scalar ⟨64, true, false⟩ true true, .scalar ⟨64, true, false⟩ true false],.scalar ⟨1, false, true⟩,(.sequence (.primitive (.declare ⟨1, false, true⟩ true (.literal ⟨1, false, true⟩ (0)))) (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.variable ⟨64, true, false⟩ 0) (.variable ⟨64, true, false⟩ 1)) (.sequence (.scope (.sequence (.primitive (.assign 0 ⟨64, true, false⟩ (.variable ⟨64, true, false⟩ 1))) (.sequence (.primitive (.assign 2 ⟨1, false, true⟩ (.literal ⟨1, false, true⟩ (1)))) (.primitive .skip)))) (.primitive .skip)) (.primitive .skip)) (.sequence (.primitive (.ret (.variable ⟨1, false, true⟩ 2))) (.primitive .skip))))⟩
def «chmin_long_long» : NProgram := ⟨[.scalar ⟨64, true, false⟩ true true, .scalar ⟨64, true, false⟩ true false],.scalar ⟨1, false, true⟩,(.sequence (.primitive (.declare ⟨1, false, true⟩ true (.literal ⟨1, false, true⟩ (0)))) (.sequence (.branch (.binary ⟨1, false, true⟩ .lt (.variable ⟨64, true, false⟩ 1) (.variable ⟨64, true, false⟩ 0)) (.sequence (.scope (.sequence (.primitive (.assign 0 ⟨64, true, false⟩ (.variable ⟨64, true, false⟩ 1))) (.sequence (.primitive (.assign 2 ⟨1, false, true⟩ (.literal ⟨1, false, true⟩ (1)))) (.primitive .skip)))) (.primitive .skip)) (.primitive .skip)) (.sequence (.primitive (.ret (.variable ⟨1, false, true⟩ 2))) (.primitive .skip))))⟩

end Proofs.ExtremaLibInstance
