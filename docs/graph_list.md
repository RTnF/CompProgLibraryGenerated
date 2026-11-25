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
| `operator<<` | `N = n, M = m` と全辺を出力する | O(n + m) |

- 前提: 頂点の引数は `[0, n)`。`distance(from, to)`・`shortest_path(from, …)` は始点 `from` の最短路を計算した後に呼ぶ（計算するメンバーは下記）。`E` は `E(from, to, args...)` で構築でき、公開フィールド `from`・`to`（`int`）と `cost`（`Cost`）を持つ。
- 表は `std::unordered_map`。辺や頂点を足すと消える。

## 元のソースからの変更

- `namespace cp` に置き、`std::` を明示した。本体は元のまま。
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

C++ のテスト（`tests/graph_list.cpp`）は既定の型の辺の番号・費用、両方向の辺、`add_node`、静的メンバー、`operator<<`、別の辺の型（追加の構築子引数）、`operator[]` を通した書き換えを確かめる。差分テスト（`tests/diff/graph_list.py`、`Cost = long long`、`E = Edge<long long>`）は 2 種の構築子、`add_node`、費用ありとなしの `add_edge`・`add_bidirectional_edge`、`reset_shortest`、表にない始点の `distance(from)` を混ぜ、全行を `operator[]` で比べる。
