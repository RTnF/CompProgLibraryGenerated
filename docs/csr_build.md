# csr_build

`cp::csr_build(from, to, head, target, pos, n)` は、辺リストから CSR 配列（`head`/`target`）を作る。`prim`・`dijkstra`・`lowlink`・`find_cycle` などが受け取る CSR 形式のグラフを、`experiments/library/cpp/graph/graph_list.hpp` の `ListGraph::add_edge` が作る辺の集まりから構築する部品である。

辺 `i` は `from[i] -> to[i]`（無向辺は両方向を並べて渡す）。計数ソートで作るので、構築後の `target[head[v] .. head[v + 1])` は頂点 `v` から出る辺の行き先で、入力の順に並ぶ（安定）。

元のソースからの変更: `ListGraph` は頂点ごとの `vector<Edge>`（`vector<vector<>>`）で、辺の構造体（ID、重み、流量）を持つ。ここでは辺の属性を持たない整数の平行配列と CSR 配列に置き換えた。`edge`/`edge_flow` の静的カウンタ `next_id` と標準入出力は方針により対象外（`docs/experiments_status.md`）。

前提: `from.size() == to.size() == target.size() == m`、`head.size() == n + 1` で全要素が `0`、`pos.size() == n`（作業用、中身は何でもよい）、すべての `from[i]` が `[0, n)`、すべての `to[i]` が非負の `int`（グラフとして使うなら `[0, n)`）、`n < 2^31 - 2`、`m < 2^31 - 2`。

結果（`Proofs/CsrBuildCall.lean` の `csr_build_correct`、一般の入力について証明）: 返り値の `head`、`target` について `CSROut`（`Proofs/CsrBuildSpec.lean`）が成り立つ。
- `HeadOK`: `head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == m`（`target.size()`）。
- 隣接: `u -> w` が CSR 配列の辺（`head[u] <= q < head[u + 1]` かつ `target[q] == w` となる `q` がある）であることと、`from[i] == u` かつ `to[i] == w` となる `i` があることは同値。
- 安定性: 頂点 `u = from[j]` から出る辺のうち `j` 番目の辺より前にある本数を `k` とすると、`target[head[u] + k] == to[j]`。
- 証明は `Proofs/CsrBuildMath.lean`（計数 `cnt`/`ocnt` の補題）、`CsrBuildProg.lean`（C++ 本体のモデル）、`CsrBuildExec.lean`（4 つのループの不変条件と仕事量）、`CsrBuildSpec.lean`（最終状態から仕様）、`CsrBuildPrepare.lean`/`CsrBuildCall.lean`（呼び出し）。

時間と領域: 仕事量は呼び出し側の引数評価を除いて高々 `800 * (n + m) + 420`（粗い上限。実際は `O(n + m)`）、追加領域は局所変数と `pos` だけ。

定理に含めていないこと: `to[i]` が負の場合（証明は非負の `int` に限る）。C++ のテストは `tests/csr_build.cpp`（頂点数 1〜8 のランダムな辺リストを、頂点ごとに入力順で集めた基準と比較する）。
