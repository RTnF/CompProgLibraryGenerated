# mod61

`cp::mod61` と `cp::mul61` は、ローリングハッシュが使う法 `2^61 - 1` の演算である。元の `experiments/library/cpp/string/rolling_hash.hpp` の `rh_in::mod` と `rh_in::mul` に対応し、名前空間 `rh_in` と 64 bit の補助定数は、共通変換器が扱える形（関数内の定数、複合代入を使わない）に書き換えた。

- `mod61(x)`: 前提なし（`uint64_t` の全値）。`x % (2^61 - 1)` を返す（結果は `[0, 2^61 - 1)`）。
- `mul61(a, b)`: 前提 `a < 2^61`、`b < 2^61`。`2^61 - 1` に関して `a * b` と合同な値を返す。結果は `2^64` 未満（途中で桁あふれしない）だが、完全には約されていない。`mod61` を通せば `a * b % (2^61 - 1)` になる。
- 時間と領域: どちらも分岐とループのない定数時間、定数個の局所変数。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/Mod61.lean` を生成する（`uint64_t` は `UInt64` で、演算は C++ と同じく 2^64 を法とする）。`Proofs/Cpp/Mod61.lean` が次を証明する。

- `mod61_spec`: 全ての `x` について `mod61(x) = x mod (2^61 - 1)`。tick 数 1。
- `mul61_spec`: `a, b < 2^61` のとき `mul61(a, b) ≡ a * b (mod 2^61 - 1)`。途中の `UInt64` 演算は 1 つも 2^64 を超えない（各 `toNat` の等式で示す）。数学的な核心は `Proofs/Math/Mod61Math.lean` の `mul61_math`（`2^61 ≡ 1` を使った乗算の恒等式）。tick 数 1。

差分テスト（`tests/diff/mod61.py`、境界値と乱数）と C++ のテスト `tests/mod61.cpp`（`__uint128_t` の剰余を独立した基準として照合する）で翻訳と実装を確かめる。
