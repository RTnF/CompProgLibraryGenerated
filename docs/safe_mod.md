# safe_mod

`cp::safe_mod(std::int64_t x, std::int64_t m)` は `x` を正の法 `m` で `[0, m)` に正規化した値を返す。元は `experiments/library/cpp/number_theory/floor_sum.hpp` の `safe_mod`。

前提: `m > 0`。計算量: O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/SafeMod.lean` を生成する（符号なし 64 bit は `UInt64`）。`Proofs/Cpp/SafeMod.lean` の `safe_mod_spec` が、`m > 0` の任意の整数について、結果が `x % m`（Lean の `Int.emod`、`[0, m)` の代表元）であり 1 tick であることを証明する。C++ の `%`（0 方向への丸め）は `Cpp.mod`（`Int.tmod`）として翻訳される。

差分テスト（`tests/diff/safe_mod.py`、境界値と乱数）と C++ のテスト（`tests/safe_mod.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

`std::` 修飾の固定幅整数型と名前空間のみ。
