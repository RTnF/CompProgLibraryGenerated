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
| `bellman_ford(start)` | 始点からの距離と親を計算して表に入れる（負の辺可）。到達不能は `UNREACHABLE`、負閉路から届く頂点は `NEGATIVE_CYCLE`（親 `-1`）。計算済みなら何もしない | O(n (n + m)) |
| `prim()` | 最小全域森の重み（辺は `add_bidirectional_edge` で入れた無向辺、費用は非負） | O((n + m) log(n + m)) |
| `lowlink()` | 無向多重グラフの関節点と橋。橋は小さい端点を先にした組。両配列を昇順で返す | O(1 + n + m + k log(k + 1))、`k = min(n, m)` |
| `find_cycle_directed()` | 有向グラフの単純閉路を辺 `E` の列で1つ返す。閉路がなければ空 | O(1 + n + m) |
| `operator<<` | `N = n, M = m` と全辺を出力する | O(n + m) |

- 前提: 頂点の引数は `[0, n)`。`distance(from, to)`・`shortest_path(from, …)` は始点 `from` の最短路を計算した後に呼ぶ（計算するメンバーは下記）。`E` は `E(from, to, args...)` で構築でき、公開フィールド `from`・`to`（`int`）と `cost`（`Cost`）を持つ。
- 表は `std::unordered_map`。辺や頂点を足すと消える。

`lowlink` では各無向辺を両端の行に1本ずつ置く。端点は `[0, n)` とする。平行辺、自己ループ、孤立頂点、空グラフを扱う。関節点は取り除くと連結成分数が増える頂点、橋は1本だけ取り除くと連結成分数が増える辺である。費用には依存せず、辺の型から読むのは `to` だけである。ここで `m` は隣接リストに入っている弧の総数で、追加領域は再帰フレームと結果を含めて O(n) である。

## 元のソースからの変更

- `namespace cp` に置き、`std::` を明示した。本体は元のまま。
- `dijkstra` は元の `experiments/library/cpp/graph/dijkstra.hpp` の本体をクラス内に置いた。`Cost v = p.second;` を `int v = p.second;` にした（`v` は頂点の番号で、`adj[v]`・`dist[v]` の添字にしか使わない。整数の `Cost` では同じ値。浮動小数の `Cost` でも番号は正確に表せる範囲なので結果は同じ）。
- `prim` は元の `experiments/library/cpp/graph/prim.hpp` の本体をクラス内に置いた。ラムダ `span` は、参照引数を取る非公開の const メンバー関数 `prim_span(start_node, mst_dist, dist, used)` にした（同じ処理）。`Cost v = p.second;` を `int v = p.second;` にした（`dijkstra` と同じ理由）。
- `bellman_ford` は元の `experiments/library/cpp/graph/bellman_ford.hpp` の本体をそのままクラス内に置いた。
- `lowlink` は元の `experiments/library/cpp/graph/lowlink.hpp` の本体をクラス内に置いた。再帰ラムダを参照引数のある非公開の const メンバー関数に移した。親への辺は1本だけ読み飛ばし、平行な戻り辺を low の更新に使う。原本にも同じ不具合修正を適用した。
- `find_cycle_directed` は元の `experiments/library/cpp/graph/find_cycle.hpp` の本体をクラス内に置き、再帰ラムダを参照引数のある非公開メンバー関数に移した。隣接行は元と同じ順に非 const 参照で走査し、辺の構築・代入も元の参照の型を保つ。仕様と検証は [find_cycle](find_cycle.md) にまとめた。
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
- `bf_spec`（`Cost = long long`、任意の `E`。前提: 始点が未計算）: 表に入る配列は、辺を走査順（行ごと）に並べた列 `allE` について、前半 `n - 1` 周（`round1`）と後半 `n` 周（`round2`）の結果 `bfFinal`。手数は `BB0 + 2n (1 + (行の数) + 3m) + 2 + 表の大きさ` 以下（`BB0 = 3 + 表の大きさ + 2n`）。`bellman_ford_cached_spec`: 計算済みなら何も変わらない。
- `bellman_ford_correct`（`Proofs/Math/ListBellmanFordMath.lean` の `bf_correct`。前提: 端点が `[0, n)`、`|cost| ≤ C`、`n C < UNREACHABLE`、`NEGATIVE_CYCLE + C` が有限の距離の下限 `-(1 + (n-1) m) C` より小さい）: 各頂点 `v` について、始点から到達できなければ `UNREACHABLE`、負の閉路を通って到達できる（`NegReach`）なら `NEGATIVE_CYCLE`、それ以外は最短の歩道の費用（全歩道の費用以下で `UNREACHABLE` 未満）で、親をたどると `-1` で終わり（`Chain`）、その列は費用が距離の歩道（`WalkB`）。証明の要点: 前半は完全性（`r` 周で `r` 辺以下の歩道の費用以下）、健全性（有限の距離は歩道の費用）、最後の更新時刻の幽霊変数による親の不変条件（親が後で更新されると不等号が厳密）、鳩の巣による閉路の除去（負閉路に届かない頂点の歩道は `n - 1` 辺以下にできる）。後半は、負閉路に届かない頂点は変わらず、負閉路のどれかの頂点が 1 周目に印を受け、印が 1 周に 1 辺以上広がる。
- `prim_spec`（`Cost = long long`、任意の `E`。前提: 全辺の行き先が `[0, n)` で費用が `[0, UNREACHABLE)`、辺の集合が対称（`add_bidirectional_edge` で入れた無向グラフ）、`2(n + m) + 1 < 2^64`）: 返り値は非負で、最小全域森の重み（`IsMSF`: その重みの全域森があり、どの全域森の重みもそれ以上。`Proofs/Math/PrimBridge.lean` の既存の証明を使う）。手数は `2 + 2n + K' 2(n + m) + n (K' + 4)` 以下（`K' = log2(2(n + m) + 2) + 3`）。証明は、キューから取り出した新しい頂点が未訪問の頂点の中で距離が最小であること（`Proofs/Math/ListPrimMath.lean` のキューの不変条件 `QI` と、各連結成分の最初の頂点の状態 `SpanB`）を示し、既存の不変条件 `PInv` を進める（`span_spec`）。
- 数値の範囲: 距離と `dist[v] + cost` が `long long` に収まること（例えば費用の総和が `UNREACHABLE` 未満）は前提として C++ 側で負う。Lean の証明は数学的整数で行う。
- `lowlink_spec` は任意の `Cost` と、行き先を読める任意の `E` について、停止、結果の完全性と重複なし、整列順、グラフの保持を示す。隣接リストの多重度を保ち、自己ループを除いた射影上で DFS の順序、親、low と再帰スタックの不変条件を維持する。各出力は `k` 件以下で、手数は `1 + 6n + 2m + 2k(log₂ k + 1)` 以下。探索中に保持する頂点配列、出力要素と定数サイズの再帰フレームのモデル上の個数は `lowlink_workspace_slots` により `6n` 以下。整列する配列は各 `k` 件以下である。入力の整数と途中の値が C++ の型の範囲内にあることを前提とする。

C++ のテスト（`tests/graph_list.cpp`）は既定の型の辺の番号・費用、両方向の辺、`add_node`、静的メンバー、`operator<<`、別の辺の型（追加の構築子引数）、`operator[]` を通した書き換えを確かめる。差分テスト（`tests/diff/graph_list.py`、`Cost = long long`、`E = Edge<long long>`）は 2 種の構築子、`add_node`、費用ありとなしの `add_edge`・`add_bidirectional_edge`、`reset_shortest`、表にない始点の `distance(from)` を混ぜ、全行を `operator[]` で比べる。費用が非負のグラフで `dijkstra`（2 回目の呼び出しを含む）、`distance` 2 種、全頂点への `shortest_path` を比べる。C++ のテストは Bellman–Ford と距離を比べ、経路が実在の辺をたどり費用が距離に等しいことを確かめる。`bellman_ford` は負の辺と負閉路を含むグラフで、到達可能性・負閉路の判定（参照実装）と比べ、全頂点への `shortest_path` の費用を確かめる。差分テストも負の費用のグラフで `bellman_ford`、`distance`、`shortest_path` を比べる。`prim` は無向の多重グラフ（自己ループ、非連結を含む）でクラスカル法と比べ、差分テストでも比べる。

`lowlink` は頂点・辺を1つずつ除いて連結成分数を数える基準実装と、4頂点の多重グラフ全11,664通りを正順・逆順で比較する。原本と公開版に同じ ASan/UBSan 回帰を実行し、差分テストでは生成 Lean と同じグラフを2回ずつ探索する。 [多重グラフの回帰テスト](../tests/imports/lowlink_multigraph.cpp)
