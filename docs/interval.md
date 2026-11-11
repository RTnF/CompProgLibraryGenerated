# interval

`cp::Interval` は `long long` の半開区間 `[start, end)` で、空の区間かどうかの旗 `is_n` を持つ（3 フィールド `s`, `e`, `is_n`）。元は `experiments/library/cpp/interval/interval.hpp` の `Interval<T>`。

- 前提: `Interval(s, e)` は `s <= e`（`assert`）。`intersection` は 2 つの有効な区間について。
- 計算量: すべて O(1)。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/Interval.lean` を生成する。`Proofs/Cpp/Interval.lean` が、任意の全順序 `T` について次を証明する（いずれも 1〜2 tick）。

- 構築子 2 種とアクセサ（`start`、`end`、`is_null`、`length = e - s`）の値。
- 比較 6 種: `==` は等しさ、`!=` はその否定、`<` は `(s, e, is_n)` の辞書式順序 `ILt`（`false < true`）、`>` は逆向き、`<=`/`>=` は `ILt` または等しい。元の既定の `operator<=>` と同じ順序である。
- `intersection`: 重なるとき `[max, min)`、重ならないとき `[0, 0)`。

差分テスト（`tests/diff/interval.py`、`T = long long` と `T = int`）と C++ のテスト（`tests/interval.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

- 既定の `operator<=>`（C++20）は C++17 では書けないため、同じ順序を返す 6 演算子を明示的に定義した。
- フィールドを `struct` の公開メンバーにし、アクセサを `const` にした。`constexpr` は付けない。入出力演算子は方針により含めない（`docs/agent/handoff.md`）。
