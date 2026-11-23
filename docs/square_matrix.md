# square_matrix

`cp::SquareMatrix<T, n>`（`experiments/library/cpp/number/square_matrix.hpp` の `SquareMatrix`）は `n × n` の正方行列で、公開の C 配列 `T mat[n][n]` を持つ aggregate である。元のクラスをそのまま公開する。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `static O()` | 零行列 | O(n^2) |
| `static I()` | 単位行列（対角成分は `(i == j)` を `T` に変換した 1） | O(n^2) |
| `operator[](i)`（`const` 版も） | 行 `i`（`T (&)[n]`） | O(1) |
| `+=`, `-=`, 二項 `+`, `-` | 成分ごとの和・差 | O(n^2) |
| `*=`, 二項 `*` | 行列の積（各成分は `0` から `k` の順に足す） | O(n^3) |
| 単項 `+`, `-` | そのまま、成分ごとの符号反転 | O(n^2) |
| `==`, `!=` | 全成分の比較 | O(n^2) |
| `pow(e)` | `e` 乗（二乗法。最後のビットの後は二乗しない） | O(n^3 log e) |

- 前提: `T` は `0`、bool からの変換、`+`、`-`、`*`、`==` を持つ（算術型や `modint`）。値は `T` の範囲に収まる。`pow` は `0 <= e`（`assert` で検査）。
- `pow` が行列の冪に等しいことは、`T` が環（結合法則・分配法則を持つ）のときに示す。

## 元のソースからの変更

- 公開側では `namespace cp` に置き、`pow(ll e)` の `ll` を `long long` と書いた。本体は元と同じ（元の比較と `pow` の修正は 2026-11-02 に原本へ適用済み。`docs/agent/fixes.md`）。
- 2026-11-23 までの公開版（長さ `n * n` の vector に対する関数 `mat_mul` など 8 個）は、元のクラスに置き換えた。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がクラスを Lean の構造体 `cp.SquareMatrix (T : Type) (n : Int)`（`mat : Array (Array T)`）とメンバー・friend の関数に翻訳する（`Proofs/Cpp/Gen/SquareMatrix.lean`）。C 配列は長さ `n` の行の `Array`、既定構築は既定値の配列、`operator[]` は行の値を返す関数になる。

`Proofs/Cpp/SquareMatrix.lean` が、行列が `n` 行 `n` 列であること（`Wf`）を前提に次を示す。成分は `G m i j = mat[i][j]`。

- `zero_spec`、`one_spec`: `O()` は全成分 0、`I()` は `(i == j)` を `T` に変換した値。
- `add_assign_spec`、`sub_assign_spec`、`add_spec`、`sub_spec`、`neg_spec`、`pos_spec`: 成分ごとの演算。`+=`・`-=` の戻り値（`*this`）は更新後の値。
- `mul_assign_spec`、`mul_spec`: 成分は `mulF n (G a) (G b)`（`Σ_k a[i][k] * b[k][j]` を `k` の順に足した値。`Proofs/Cpp/Lib/SquareMatrixMath.lean`）。`c *= c` のように両辺が同じでもよい。
- `eq_spec`、`ne_spec`: 全成分が等しいか。途中で返す二重ループは、返した場合にカーソルが末尾にある不変条件で扱う。
- `index_spec`、`index_const_spec`: 行 `i` を返す。参照を通した書き込みはモデルに含めない（寿命・別名関係は証明の対象外。`docs/trust_policy.md`）。
- `pow_spec`（`T` は環、`0 <= e < 2^63`）: 結果は `PW n (G a) e`（`a` を `e` 回掛けた行列）。不変条件は `r * y^e` が一定（`pow_round`）。tick 数は `3 + n(1+n) + bitWidth(e) (1 + 2 Kmul n)` 以下（`Kmul n` は 1 回の `*=` の手数）。

差分テスト（`tests/diff/square_matrix.py`、`n = 2, 3`。オブジェクトは `O()`・`I()` と演算で作る）と C++ のテスト（`tests/square_matrix.cpp`、`n = 1, 2, 3` の乱択と素朴な実装との比較、aggregate と型の性質、`pow` の境界）で翻訳と実装を確かめる。
