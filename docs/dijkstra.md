# dijkstra

`cp::dijkstra(head, target, cost, dist, done, parent, n, inf)` は、非負の辺コストの単一（複数）始点最短経路（ダイクストラ法）の配列版である。`experiments/library/cpp/graph/dijkstra.hpp` の `ListGraph::dijkstra` から、検証できる形に書き直した。

元のソースからの変更:
- グラフは CSR 形式の配列で渡す: 頂点 `v` から出る辺の行き先は `target[head[v] .. head[v + 1])`、コストは同じ位置の `cost[...]`。
- `priority_queue` の代わりに、確定していない頂点のうち `dist` が最小のものを線形探索で選ぶ。計算量は `O(n^2 + m)`（元は `O((n + m) log n)`）。親の配列 `parent`（経路復元）は元と同じく、確定した頂点 `best` から辺 `best -> w` で `dist[w]` が小さくなるたびに `parent[w] = best` と書く。

使い方: 呼び出し側が `dist[始点] = 0`、それ以外を `inf`（まだ届いていない印）にし、`done` を長さ `n` の 0 の配列、`parent` を長さ `n` の配列（元の経路復元と同じく全部 -1）にして渡す。始点の初期値は 0 以外の有限値でもよく、複数の始点を同時に置ける。

前提: `head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size()`、すべての `target[p]` が `[0, n)`、すべての `cost[p]` が `[0, 2^61]`、`dist.size() == done.size() == parent.size() == n`、`dist` の全要素が `[lo, inf]`（`lo ≥ -2^62`）、`inf ≤ 2^62`、`done` は全部 0、`n < 2^31 - 2`、`target.size() < 2^31 - 1`。このとき途中の和 `bd + cost` はすべて `long long` に収まる。

結果（`Proofs/DijkstraCall.lean`、一般の入力について証明）: 初期の `dist` を `d0` とする。
- 健全性: `dist[v] != inf` なら、`d0[w] != inf` の頂点 `w` から `v` へのウォークがあり、`dist[v]` は `d0[w]` にそのウォークのコストを足した値に等しい。
- 完全性: `inf` が「`d0[w]` ＋ 任意のウォークのコスト」より大きいとき（ウォークの長さは問わない）、`w` から `v` への任意のウォーク（コスト `c`）について `dist[v] ≤ d0[w] + c`。したがって `dist[v]` は最短距離に等しい。
- 親: 各 `v` について `parent[v]` は初期値のままか、確定した頂点 `u = parent[v]`（`done[u] = 1`）から `v` への辺があり `dist[v] = dist[u] + その辺のコスト` が成り立つ（`ParInv`、`Proofs/DijkstraPMath.lean`）。
- 証明は `Proofs/DijkstraMath.lean`（確定した頂点の集合 `D` についての不変条件 `Dj`: 確定した頂点の `dist` は最短で、確定していない頂点の `dist` は確定した頂点からの辺で緩和済み、確定した頂点の `dist` は確定していない頂点のものより小さい）、`Proofs/DijkstraScan.lean`（最小値の探索ループ）、`Proofs/DijkstraExec.lean`（緩和ループと外側のループ）、`Proofs/DijkstraPMath.lean`（親の更新と不変条件）、`Proofs/DijkstraPrepare.lean`/`Proofs/DijkstraCall.lean`（呼び出し。vector は 6 本）。

時間と領域: 外側 `n` 周、各周で `n` 個の探索と選んだ頂点の出辺の緩和で、モデル上の仕事量は呼び出し側の引数評価を除いて高々 `(320 * n + 420 * m + 420) * n + 150`（粗い上限。実際の反復は `O(n^2 + m)` 回）。追加領域は局所変数だけ。

定理に含めていないこと: `done` の最終的な内容（C++ のテストで、到達できる頂点が 1 になることを確認している）、負の辺（前提で除く）、`priority_queue` 版。親をたどると始点に着くことは C++ のテストで確認している。C++ のテストは `tests/dijkstra.cpp`（頂点数 1〜9 のランダムなグラフ、1〜2 個の始点を、フロイド–ワーシャルから作った基準と比較する）。


費用の型 `Cost` はテンプレート引数のままで、元と同じく任意の型で使える。検証した具体化はヘッダー末尾の明示的な具体化 `dijkstra<long long>`。
