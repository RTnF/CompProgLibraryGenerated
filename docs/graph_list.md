# graph_list

`cp::ListGraph<Cost, E>` は隣接リストで表した有向グラフのクラスである。元の `experiments/library/cpp/graph/graph_list.hpp` を公開する。`Cost` の既定は `long long`、辺の型 `E` の既定は `cp::Edge<Cost>`（`docs/edge.md`）。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `UNREACHABLE` | `numeric_limits<Cost>::max() >> 2` | — |
| `NEGATIVE_CYCLE` | `numeric_limits<Cost>::min() >> 2` | — |
| `ListGraph()` / `ListGraph(int n)` | 頂点 0 個 / `n` 個、辺なし | O(1) / O(n) |
| `operator[](i)` | 頂点 `i` から出る辺の行（参照。書き換えてよい） | O(1) |
| `add_node()` | 頂点を 1 個足す | O(1)（＋表の消去） |
| `add_edge(from, to, args...)` | 辺 `E(from, to, args...)` を `from` の行の末尾に足す | O(1)（＋表の消去） |
| `add_bidirectional_edge(from, to, args...)` | `E(from, to, args...)` を `from` の行に、`E(to, from, args...)` を `to` の行に足す | O(1)（＋表の消去） |
| `reset_shortest()` | 最短路の表（始点 → 距離・親の配列）を消す | O(表の大きさ) |
| `distance(from, to)` / `distance(from)` | 始点 `from` の距離（表から読む。表にない始点の `distance(from)` は空の配列を表に入れて返す） | O(1) / O(n)（平均） |
| `shortest_path(from, to)` | 始点 `from` の親の配列を `to` から `-1` までたどり、逆順にした頂点列 | O(経路長)（平均） |
| `dijkstra(start)` | 始点 `start` からの距離と親を計算して表に入れる（辺の費用は非負。計算済みなら何もしない） | O((n + m) log(n + m))（＋表の操作） |
| `operator<<` | `N = n, M = m` と全辺を出力する | O(n + m) |

- 前提: 頂点の引数は `[0, n)`。`distance(from, to)`・`shortest_path(from, …)` は始点 `from` の最短路を計算した後に呼ぶ（計算するメンバーは下記）。`E` は `E(from, to, args...)` で構築でき、公開フィールド `from`・`to`（`int`）と `cost`（`Cost`）を持つ。
- 表は `std::unordered_map`。辺や頂点を足すと消える。

## 元のソースからの変更

- `namespace cp` に置き、`std::` を明示した。本体は元のまま。
- `dijkstra` は元の `experiments/library/cpp/graph/dijkstra.hpp` の本体をクラス内に置いた。`Cost v = p.second;` を `int v = p.second;` にした（`v` は頂点の番号で、`adj[v]`・`dist[v]` の添字にしか使わない。整数の `Cost` では同じ値。浮動小数の `Cost` でも番号は正確に表せる範囲なので結果は同じ）。
- 元のヘッダは `dijkstra`・`bellman_ford`・`prim`・`lowlink`・`find_cycle_directed`・`topological_sort`・`topological_sort_minimum` を宣言だけし、定義はそれぞれのヘッダ（`dijkstra.hpp` など）にある。公開側では 1 つのクラスにまとめるため、各ヘッダを移植するときに本体ごとこのクラスに加える。まだ移植していないメンバーは宣言も置いていない（宣言だけでは呼び出しがリンクできないので、使える機能は元のヘッダ単体と同じ）。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がクラスを構造体 `cp.ListGraph Cost E` とメソッドに翻訳する（`Proofs/Cpp/Gen/GraphList.lean`）。

- 表 `std::unordered_map<int, std::vector<X>>` は `Cpp.UMap`（キーの重複しない連想リスト、`Proofs/Cpp/Lib/UMap.lean`）。`m[k]` はない鍵に空の配列を入れる。手数は文書化された最悪の場合（1 回の参照・消去で `size + 1`）。
- 辺の型 `E` は型引数のままで、`e.to` などは既定の引数 `Edge<Cost>` のフィールドの型で `Cpp.Field` に翻訳する。`add_edge` の `args...` は型 `Args`（引数の組。空なら `Unit`）の 1 つの値で、構築は `Cpp.Construct E (Int × Int × Args)`、構築子が共有する状態（`Edge` の番号のカウンタ）は `Cpp.ConstructState E` の値として引数と戻り値で受け渡す。`E = Edge<T>` のインスタンスは `Proofs/Cpp/GraphListEdge.lean`。
- `operator<<` は利用者の決定（2026-10-12）により翻訳から除き、C++ のテストだけで確かめる。`operator[]` の戻り値の参照を通した書き換えはモデルに含めない（モデルは行の値を返す）。

証明（`Proofs/Cpp/GraphList.lean`）:

- `init_0_spec`、`init_int_spec`、`op_index_spec`、`reset_shortest_spec`、`add_node_spec`: フィールドの値と手数（任意の `Cost`・`E`）。
- `add_edge_cost_spec`・`add_edge_spec`・`add_bidirectional_edge_cost_spec`・`add_bidirectional_edge_spec`: `E = Edge<T>` で、足した辺が `⟨from, to, id, cost⟩`（`id` はカウンタの値、費用を省くと `1`）であり、カウンタが 1（両方向では 2）増え、`m_` が増え、表が消えること。
- `distance_int_int_spec`・`distance_int_spec`: 表の値の読み出し（表にない始点の挿入を含む）。
- `shortest_path_spec`: 親の配列 `P` が表にあり、`to` から親をたどる列が `-1` で終わる（`Chain P to L`）とき、結果は `L` を逆にした列で、グラフは変わらない。`L.length < 2^64` のとき停止し、手数は `2 + L.length * (表の大きさ + 5)`。

- `dijkstra_spec`（`Cost = long long`、任意の `E`。前提: 始点 `< n`、`adj` の大きさが `n`、全辺の端点が `[0, n)` で費用が非負（`Valid`）、始点が未計算、`2(n + m) + 1 < 2^64`）: 表に入る距離 `d` と親 `par` は終了時の不変条件 `Inv`（`Proofs/Math/ListDijkstraMath.lean`）を満たす。手数は `C1 + K (2(n + m) + 1) + 3 + 表の大きさ` 以下（`K = log2(2(n + m) + 2) + 3`、`C1 = 4 + 表の大きさ + 2n`）。`dijkstra_cached_spec`: 計算済みなら何も変わらない。
- `dijkstra_correct`: 終了時の不変条件から、各頂点 `t` について `d[t] ≤ UNREACHABLE`、`d[t]` は始点から `t` へのすべての歩道の費用以下、`d[t] < UNREACHABLE` なら `t` から親をたどると `-1` で終わり（`shortest_path_spec` の前提 `Chain`）、その列は費用の和が `d[t]` の歩道（`WalkB`）である。つまり `d[t]` は最短の歩道の費用で、`shortest_path` は最短路を返す。
- 証明の要点: 済みの頂点の列 `D` と最後に取り出したキー `L` を幽霊変数とし、キュー内の組 `(k, x)` は `d[x] ≤ k`・`L ≤ k`、有限の距離の頂点は済みかキューに `(d[x], x)` がある、済みの頂点の辺は緩和済みで距離は `L` 以下、`(d[x], x)` はキューに高々 1 つ、済みの頂点の残りの組は古い、親は先に済んだ頂点。取り出しは古い組（何もしない）か新しく済む頂点で、済みの頂点を再び処理することはない（`not_redone`）。停止の測度は `|Q| + Σ_{x ∉ D}(deg x + 1)`。
- 数値の範囲: 距離と `dist[v] + cost` が `long long` に収まること（例えば費用の総和が `UNREACHABLE` 未満）は前提として C++ 側で負う。Lean の証明は数学的整数で行う。

C++ のテスト（`tests/graph_list.cpp`）は既定の型の辺の番号・費用、両方向の辺、`add_node`、静的メンバー、`operator<<`、別の辺の型（追加の構築子引数）、`operator[]` を通した書き換えを確かめる。差分テスト（`tests/diff/graph_list.py`、`Cost = long long`、`E = Edge<long long>`）は 2 種の構築子、`add_node`、費用ありとなしの `add_edge`・`add_bidirectional_edge`、`reset_shortest`、表にない始点の `distance(from)` を混ぜ、全行を `operator[]` で比べる。費用が非負のグラフで `dijkstra`（2 回目の呼び出しを含む）、`distance` 2 種、全頂点への `shortest_path` を比べる。C++ のテストは Bellman–Ford と距離を比べ、経路が実在の辺をたどり費用が距離に等しいことを確かめる。
