# fenwick_tree

`cp::FenwickTree<T>` は Binary Indexed Tree（Fenwick 木）のクラステンプレートである。元の `experiments/library/cpp/segment_tree/binary_indexed_tree.hpp` の `BinaryIndexedTree<T>` と同じ構成子とメンバー関数を持つ。配列 `A`（`n` 要素）を、大きさ `n + 1` の vector `tree`（1 始まり、`tree[0]` は未使用、`tree[k]` は `A` の `[k - lowbit(k), k)` の和）で持つ。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `FenwickTree()` | 空の木 | O(1) |
| `FenwickTree(int n)` | 長さ `n` の零配列 | O(n) |
| `FenwickTree(const std::vector<T> &v)` | 配列 `v` の木 | O(n) |
| `sum(int r)` | `A[0, r)` の和 | O(log n) |
| `sum(int l, int r)` | `A[l, r)` の和（`sum(r) - sum(l)`） | O(log n) |
| `add(int i, T val)` | `A[i] += val` | O(log n) |

型 `T` はテンプレート引数のままで、元と同じく任意の整数型・加法の型で使える。検証した具体化は `FenwickTree<long long>`（`template class FenwickTree<long long>;` で明示的に具体化している）。

型の演算要件も元に合わせ、構築時に `+=` が使える型へ追加で二項 `operator+` を要求しない。2026-11-02に公開構築子の `a = a + b` を `a += b` へ戻した。`tests/fenwick_tree.cpp` は `+=` と `-` があり `+` のない型でも、3種類の構築子・更新・両方の和を確認する。この型のLean証明が済んだという意味ではなく、Leanの具体化は引き続き `long long` である。

元のソースからの変更（検証できる形にするために書き換えた。機能は減らしていない）:

- `i & -i` を符号なしの演算 `(unsigned)i & (0u - (unsigned)i)` で書いた（検証できるビット演算は符号なしだけ）。値は同じ。
- `sum(l, r)` は 2 つの接頭辞和を局所変数に取ってから引く。
- `vector` からの構築の 2 番目のループは、修正済みの元ソースと同じく、添字が範囲内（`v.size()` 以下）のときだけ `+=` で加算する。元ソースの範囲外書込みは2026-10-28に修正済み（`docs/agent/fixes.md`）。ループの上限は `tree.size()` ではなく `v.size()` で書いてある（メンバー初期化子により `tree.size() == v.size() + 1`）。
- 構築の最初のループ（`tree[i + 1] = v[i]`）も含めて、`vector` からの構築子のすべてを検証している（以前の公開版は構築子を含んでいなかった）。

前提:

- `tree.size() <= 2^30`（`i + (i & -i)` が `int` に収まるため）。
- `add`: `0 <= i < 2^31 - 1`（`i` が範囲外なら何も変化しない）。更新後の `tree` の全要素が `T` に収まること（符号付きの桁あふれは契約の外）。
- `sum(r)`: `0 <= r < tree.size()`、辿る節点の部分和が `T` に収まること。`sum(l, r)`: `l` と `r` の両方についてその前提と、2 つの接頭辞和の差が収まること。`l > r` のときは `-(A[r, l)` の和)` になる。
- `vector` からの構築: `v.size() + 1 <= 2^30`、更新で現れる値（`j = k + lowbit(k) <= v.size()` に対する `A[j-1] + pre(A, k) - pre(A, j - lowbit(j))`）が `T` に収まる（Lean の `BOkT`）。

証明する内容（`Proofs/FenwickTreeCall.lean`。すべて `T = long long` について、一般の入力で）:

- `fenwick_tree_add_correct`（`add`、`Proofs/FenwickCall.lean`）: 呼び出し後の `tree` は `fadd val tree (i + 1)`。`fadd_inv` により、`tree` が配列 `A` の Fenwick 木（`FInv tree A`）なら、結果は `A[i] += val` の Fenwick 木。仕事量は `31 * (log2 tree.size() + 1)` の程度、書き込みは高々 `log2 tree.size() + 1` 回。
- `fenwick_tree_sum_correct`（`sum(r)`）: 結果は `fsumR tree r`。`fsumR_correct` により、`FInv tree A` なら `A` の先頭 `r` 個の和。仕事量は `31 * (log2 tree.size() + 1)` の程度。`tree` は変化しない。
- `fenwick_tree_range_correct`（`sum(l, r)`、`Proofs/FenwickRangeCall.lean`）: 結果は `fsumR tree r - fsumR tree l`。仕事量は `62 * log2(tree.size()) + 300` 以下、追加領域は定数、`tree` は変化しない。
- `fenwick_tree_from_vector_correct`（`vector` からの構築子、`Proofs/FenwickTreeVecCall.lean`）: 構築子の本体（メンバー初期化子 `tree(v.size() + 1)` の後に実行される 2 つのループ）の後、`tree` は `FInv tree v`（`tree[k] = v` の `[k - lowbit(k), k)` の和）を満たす。仕事量は `560 * v.size() + 200` 以下、`tree` への書き込みは `2 * v.size()` 回以下、追加領域は局所変数 4 個。`tree[0]` の値は使わない。
- 数学的な内容: `Proofs/FenwickMath.lean` が `lowbit` の値、更新経路、反復回数の `log2` 上界を、`Proofs/FenwickBuildMath.lean` が構築のループの不変条件 `BInv`（`binv_init`、`binv_step`、`binv_final`）を証明する。

定理に含めていないこと:

- `FenwickTree()` は本体が空、`FenwickTree(int n)` も本体が空でメンバー初期化子 `tree(n + 1)` だけなので、検証する関数にならない。結果（長さ `n + 1` の零 vector）は標準ライブラリの `std::vector<T>(size_type)` の契約による（`docs/trust_policy.md`、`Proofs/StlContracts.lean`）。`vector` からの構築子の定理も、`tree` がこの標準の構築子で作られた直後であることを前提にしている（`tree.size() == v.size() + 1`）。
- `add` で `i` が範囲外のとき何も変化しないこと（C++ ではそのとおり動くが、定理は結果を `fadd` で述べている）。`T` が `long long` 以外のときの検証。
- 構築で作った木と `add` の反復で作った木の等しさ。C++ のテスト `tests/fenwick_tree.cpp` で、サイズ 0〜4097 の乱択配列について確認する。

C++ のテストは `tests/fenwick_tree.cpp` で、素朴な累積和を基準として、長さ 0〜70 の乱数操作、範囲外の `i`、`2^20` 要素の木、全 `(l, r)` の組の区間和、構築子 3 種、`T = int`・`unsigned long long` の具体化を確認する。
