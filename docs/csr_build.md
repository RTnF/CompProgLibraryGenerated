# csr_build

`cp::csr_build(from, to, head, target, pos, n)` は、辺リストから CSR 配列（`head`/`target`）を作る。`prim`・`dijkstra`・`lowlink`・`find_cycle` などが受け取る CSR 形式のグラフを、`experiments/library/cpp/graph/graph_list.hpp` の `ListGraph::add_edge` が作る辺の集まりから構築する部品である。

辺 `i` は `from[i] -> to[i]`（無向辺は両方向を並べて渡す）。計数ソートで作るので、構築後の `target[head[v] .. head[v + 1])` は頂点 `v` から出る辺の行き先で、入力の順に並ぶ（安定）。

前提: `from.size() == to.size() == target.size() == m`、`head.size() == n + 1` で全要素が `0`、`pos.size() == n`（作業用、中身は何でもよい）、すべての `from[i]` が `[0, n)`、`n < 2^31 - 2`、`m < 2^31 - 1`。計算量 O(n + m)、追加領域は `pos` だけ。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/CsrBuild.lean` を生成する。`Proofs/Cpp/CsrBuild.lean` の `csr_build_spec` が、前提を満たす全入力について次を証明する。

- `head[k]`（`k <= n`）は始点が `k` 未満の辺の数（`Proofs/CsrBuildMath.lean` の `ocnt`）。したがって `head[0] = 0`、`head` は非減少、`head[n] = m`。
- 辺 `i` の行き先 `to[i]` は `target[head[from[i]] + c]` に置かれる。`c` は `i` より前の、始点が同じ辺の数（`cnt`）。異なる辺の置き場所は異なり、すべて `[0, m)` に入る（`pos_ne`、`pos_lt`）。これにより頂点 `u` から出る辺は `target[head[u], head[u + 1])` に入力の順で並ぶ。
- tick 数はちょうど `2 (n + m) + 1`。

4 つのループの不変条件は、数え上げ（`cnt`）、累積和（`ocnt`）、`pos` の初期化、配置の各段階を表す（`inv1_step`〜`inv4_step`）。

差分テスト（`tests/diff/csr_build.py`）と C++ のテスト（`tests/csr_build.cpp`）で翻訳と実装を確かめる。

## 元のソースからの変更

元の `ListGraph`（隣接リスト）を、検証済みのグラフ部品が受け取る CSR 配列に変換する補助部品である（`docs/experiments_status.md` の違反一覧を参照）。
