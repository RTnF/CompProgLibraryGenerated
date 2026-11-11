# tree_arc_costs

`cp::tree_arc_costs(cost, ac, m)` は、辺リストで与えられた木の辺の費用を、2 つの弧に写す。`experiments/library/cpp/tree/tree.hpp` のコンストラクタ `Tree(int root, vector<int> &from, vector<int> &to, vector<Cost> &cost)` の、費用を隣接リストに追加する部分に対応する。端点側は `cp::tree_arcs_from_list` が同じ位置 `2 * i`、`2 * i + 1` に書く。

`i = 0, ..., m - 1` について `ac[2 * i] = ac[2 * i + 1] = cost[i]` とする。費用なしのコンストラクタ（元は費用 1）では、全要素が 1 の `cost` を渡す。

元のソースからの変更:
- 隣接リストの代わりに、弧リスト `ac` の位置 `2 * i`、`2 * i + 1` に書く。`tree_arcs_from_list` と同じ位置で、`cp::csr_build` のあとで CSR の並びに合わせて並べ替える手順は `docs/tree_arcs.md` と同じ。
- 検証した型は `Cost = long long`（`template void tree_arc_costs<long long>` の明示的な実体化）。テンプレート自体は任意の `Cost` で使える。他の型は同じ形の実体化を足して検証する。
- 元の範囲の `assert` は前提条件とする。

前提: `0 <= m < 2^29`、`cost.size() >= m`、`ac.size() >= 2 * m`。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TreeArcCosts.lean` を生成し、`Proofs/Cpp/TreeArcCosts.lean` が前提を満たす全入力について次を証明する。

- `tree_arc_costs_spec`: 任意の `Cost` について、`0 <= m`、`2m <= ac.size()` のとき、終了後 `ac[2i] == ac[2i+1] == cost[i]`（`i < m`）、`2m` 以降の要素と長さは変わらない。
- tick 数はちょうど `m + 1`。

差分テスト（`tests/diff/tree_arc_costs.py`）と C++ のテスト `tests/tree_arc_costs.cpp` で翻訳と実装を確かめる。
