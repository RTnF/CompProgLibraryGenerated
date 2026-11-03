# tree_distance

`cp::tree_distance(cost_depth, u, v, lca)` は、根付き木の 2 頂点 `u`、`v` の距離（経路の費用の和）を、根からの費用 `cost_depth` と最近共通祖先 `lca` から返す: `cost_depth[u] + cost_depth[v] - cost_depth[lca] * 2`。`experiments/library/cpp/tree/tree.hpp` の `Tree::distance` から、検証できる形に書き直した。`Cost` はテンプレートのまま残し、検証した具体化は `long long`。

元のソースからの変更:
- `cost_depth_[root_]` と、メンバー関数 `lowest_common_ancestor(u, v)` の呼び出しを、引数 `cost_depth`（`tree_root` が求める配列）と `lca`（呼び出し側が `tree_ancestor` と `tree_lca_same_depth` で求める）に変える。元の `distance` は入力の範囲を `assert` で確かめるが、ここでは前提条件とする。
- 3 回の配列の読み出しを別々の宣言に分ける（検証済みの式の言語は、配列の読み出しを宣言か代入の右辺にだけ許すため）。計算は元と同じ順序（`a + b - c * 2`）。
- 元の関数全体（LCA を内部で求める形）としての検証は、`tree_ancestor`、`tree_lca_same_depth` との合成（C++ の呼び出し側）になる。分けたことは `docs/experiments_status.md` の違反一覧に載せた。

前提: `0 <= u, v, lca < cost_depth.size() < 2^31 - 1`、`cost_depth[u] + cost_depth[v]`、`cost_depth[lca] * 2`、最後の差がどれも `long long` に収まる。

結果（`Proofs/TreeDistanceCall.lean`、一般の入力について証明）: 返り値は `cost_depth[u] + cost_depth[v] - 2 * cost_depth[lca]`（整数としての値）。`lca` が `u`、`v` の最近共通祖先で `cost_depth` が根からの費用なら、これは `u` から `v` への経路の費用になる（C++ のテストで確認している。Lean の定理には含めない）。

時間と領域: モデル上の仕事量は呼び出し側の引数評価を除いて 200 以下（定数時間）、追加領域は局所変数だけ。

証明は `Proofs/TreeDistanceExec.lean`（`pexecM` による実行）、`Proofs/TreeDistancePrepare.lean`/`Proofs/TreeDistanceCall.lean`（呼び出し）。C++ のテストは `tests/tree_distance.cpp`（頂点数 1〜14 のランダムな根付き木で、負の辺の費用を含めて経路の費用と照合する）。
