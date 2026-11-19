# fenwick_tree

`cp::FenwickTree<T>` は Binary Indexed Tree（Fenwick 木）のクラステンプレートである。元の `experiments/library/cpp/segment_tree/binary_indexed_tree.hpp` の `BinaryIndexedTree<T>` と同じ構成子とメンバー関数を持つ。配列 `A`（`n` 要素）を、大きさ `n + 1` の vector `tree`（1 始まり、`tree[0]` は未使用、`tree[k]` は `A` の `[k - lowbit(k), k)` の和）で持つ。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `FenwickTree()` | 空の木 | O(1) |
| `FenwickTree(int n)` | 長さ `n` の零配列 | O(n) |
| `FenwickTree(const std::vector<T> &v)` | 配列 `v` の木 | O(n) |
| `sum(int r)` | `A[0, r)` の和 | O(log n) |
| `sum(int l, int r)` | `A[l, r)` の和（`sum(r) - sum(l)`） | O(log n) |
| `add(int i, T val)` | `A[i] += val`（`0 <= i < n` でなければならない） | O(log n) |

型 `T` はテンプレート引数のままで、元と同じく `+=`（と `sum(l, r)` では `-`）を持つ任意の型で使える。元のクラス名 `BinaryIndexedTree` は型の別名として残した。

前提: `n >= 0`、`n + 1 < 2^31`（`v.size() + 1 < 2^31`）。`sum(r)` は `0 <= r <= n`、`sum(l, r)` は `0 <= l <= r <= n`、`add` は `0 <= i < n`。`T` が整数型なら途中の和が `T` に収まること。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/FenwickTree.lean`（`structure cp.FenwickTree T` と 6 つのメンバー関数）を生成する。`Proofs/Cpp/FenwickTree.lean` が、任意の可換加法モノイド `T`（`sum(l, r)` は可換群）について次を証明する。木が配列 `A : Nat → T`（`n` 要素）を表すことを `Rep t n A`（節点 `k` が `A` の `[k - lowb k, k)` の和を持つ）で述べる。

- `init_0_spec`: `FenwickTree()` は空の配列を表す。1 tick。
- `init_int_spec`: `FenwickTree(n)` は `n` 個の 0 を表す（`T()` が 0 であることを仮定）。`n + 2` tick。
- `init_vec_spec`: `FenwickTree(v)` は `A j = v[j]` を表す。`3 n + 2` tick 以下。2 番目のループの不変条件は `Proofs/Math/FenwickBuildMath.lean` の被覆範囲 `Wc` を使う（`BuildInv`、`build_step`）。
- `sum_spec`: `sum(r)` は `A 0 + ... + A (r - 1)` を返し、木を変えない。tick 数は `stepsS r + 2`（`log2 n + 3` 以下）。
- `sum_range_spec`: `sum(l, r)` は `A l + ... + A (r - 1)`。`2 log2 n + 7` tick 以下。
- `add_spec`: `0 <= i < n` のとき、`add(i, val)` の後の木は `A i += val` を表す。tick 数は `stepsA (n + 1) (i + 1) + 2`（`log2 (n + 1) + 3` 以下）。

`i & -i` が最下位ビット `lowb i` であることは `Proofs/Cpp/Lib/Lowbit.lean`、`lowb` の性質と反復回数の上界は `Proofs/Math/FenwickMath.lean` による。すべての定理は停止（結果が得られること）を含む。

差分テスト（`tests/diff/fenwick_tree.py`、`T = long long` と `T = int`、前提を満たす乱択操作）と C++ のテスト（`tests/fenwick_tree.cpp`、素朴な累積和と元のクラスの逐語コピーとの比較、`+` を持たない型の具体化）で翻訳と実装を確かめる。

## 元のソースからの変更

- `std::` 修飾と名前空間のみ。元の `vector` からの構築子にあった範囲外書き込み（2 番目のループの上限検査がない）は直した（`docs/agent/fixes.md`）。
