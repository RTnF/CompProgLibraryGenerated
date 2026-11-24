# graph_matrix

`cp::MatrixGraph<Cost>` は隣接行列で表した有向グラフのクラスである。元の `experiments/library/cpp/graph/graph_matrix.hpp`（クラス本体）と `experiments/library/cpp/graph/warshall_floyd.hpp`（クラス外で定義したメンバー `warshall_floyd`）を 1 つのクラスとして公開する。`Cost` の既定は `long long`。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `UNREACHABLE` | `numeric_limits<Cost>::max() >> 2`（辺がないことを表す値。`long long` では `2^61 - 1`） | — |
| `MatrixGraph(int n)` | 頂点 `0 .. n-1`、辺なし（`mat` は対角が 0、他が `UNREACHABLE`） | O(n²) |
| `add_edge(from, to, cost = 1)` | `mat[from][to] = cost`（同じ組への 2 回目は上書き）、辺の数を数える | O(1) |
| `warshall_floyd()` | 全点対の最短距離と経路復元用の親を求め、負閉路の有無を記録する。2 回目以降の呼び出しは何もしない | O(n³) |
| `distance(from, to)` | 最短距離。到達できなければ `UNREACHABLE` | O(1) |
| `get_shortest_path(from, to)` | 最短経路の頂点列（`from` から `to` まで）。到達できなければ空。`from == to` なら `{from}` | O(n) |
| `has_negative_cycle()` | 負閉路があるか | O(1) |
| `operator<<` | `N = n, M = m` と行列を出力する | O(n²) |

- 前提: `0 <= n < 2^31`。頂点の引数は `[0, n)`。`distance`・`get_shortest_path` は `warshall_floyd` の後に呼ぶ。`get_shortest_path` は負閉路がないときに呼ぶ（負閉路があると親をたどっても止まらないことがある）。
- 前提（値の範囲）: 費用と `warshall_floyd` の途中の値が `Cost` に収まる。`long long` で負閉路がないとき、`|cost| * n` が `UNREACHABLE / 4` 程度以下なら、到達できない組の値（`UNREACHABLE` に負の辺を足したもの）は `UNREACHABLE / 2` を超え、最後に `UNREACHABLE` に置き換わる。負閉路があると値が指数的に小さくなりうるので、頂点数と費用を小さく保つ。
- `Cost` に必要な操作: `+`、`<`、`>`、`/ 2`、`>> 2`、`numeric_limits<Cost>::max()`（整数型。`double` では `>>` がなくコンパイルできない。元と同じ）。

## 元のソースからの変更

- `warshall_floyd` をクラス内で定義し、`namespace cp` に置き、`std::` を明示した。`operator<<` はクラス内の hidden friend にし、`" \n"[j == n - 1]` を条件演算子にした（出力は同じ）。
- 不具合の修正（`docs/agent/fixes.md`）: 元の `warshall_floyd` は親の行列を対角だけ `i`、他を `-1` で初期化していたため、直接の辺の親が `-1` のままになり、`get_shortest_path` は `from != to` のすべての組で空を返していた。辺のある組（`mat[i][j] < UNREACHABLE`）の親を `i` にした（`if (mat[i][j] < UNREACHABLE || i == j)`）。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がクラスを Lean の構造体 `cp.MatrixGraph Cost` とメソッドに翻訳する（`Proofs/Cpp/Gen/GraphMatrix.lean`）。静的メンバー `UNREACHABLE` は値を返す静的メンバー関数、`>> 2` は `Cpp.ShiftInt`、`std::reverse` は `Array.reverse` になる。`operator<<` は利用者の決定（2026-10-12、入出力は証明しない）により翻訳から除き（TOML の `unverified_functions`）、C++ のテストだけで確かめる。

証明（`Proofs/Cpp/GraphMatrix.lean`、数学は `Proofs/Math/GraphMatrixMath.lean`）は `Cost = long long`（`Int`、`UNREACHABLE = 2^61 - 1`）について示す。重み `W` は `mat` の値そのもの（`UNREACHABLE` も重みとして扱う）、歩道 `i → l₀ → … → j` の重みは `wt W i l j`。

- `init_spec`、`add_edge_spec`、`distance_spec`、`has_negative_cycle_spec`: フィールドの値と手数。
- `warshall_floyd_spec`: 結果の距離は in-place の三重ループ `fwK`（純粋関数モデル）の値の `UNREACHABLE / 2` を超える成分を `UNREACHABLE` にしたもの、親は `fwK` の親、負閉路の印は「対角に負の成分がある」こと。手数は `8 (n + 1)^3` 以下。前提は計算前（`shortest_path_dist` が空、印が `false`）。
- `fw_correct`: `fwK` の各成分は頂点 `< n` の歩道の重みであり、頂点が重複しない歩道の重み以下である（前提なし）。負の閉路がなければ、すべての歩道の重み以下、つまり最短の歩道の重み。対角に負の成分があることと負の閉路があることは同値（負の閉路から頂点が重複しない負の閉路を取り出す `simple_neg`）。負の閉路がなければ、親は不変条件 `PInv` を満たす。
- `PInv`（`pinv_fw`）: 各行 `i` で、親 `p = P i j`（`-1` でなければ）について、`p = i` なら辺 `i → j` の重みが成分以下、そうでなければ成分 `(i, p)` に辺 `p → j` を足したものが成分以下。さらに親をたどると減る順位がある（負の閉路がないとき、1 ラウンドは全成分を同時に更新したものに等しく（`round_sim`）、親の連鎖は「行 `k` の連鎖のあとに行 `i` の `k` からの連鎖」になる）。
- `get_shortest_path_spec`: `PInv` のもとで、親をたどるループは止まり（順位を頂点数以下に正規化した `nrank` が減る）、結果は `from == to` なら `{from}`、そうでなければ空か、`from` から `to` への頂点 `< n` の歩道でその重みが成分以下。`shortest_path_weight` により、負の閉路がなければその重みは最短距離に等しい。手数は `4n + 10` 以下。

到達できない組で経路が空になること、到達できる組で空にならないこと、`UNREACHABLE / 2` による置き換えが到達不能と一致すること（費用の範囲の前提が要る）は証明していない。C++ のテスト（`tests/graph_matrix.cpp`、Bellman–Ford の素朴な実装との比較。経路が実在の辺をたどり重みが距離に等しいこと、負閉路の判定、`int` の具体化、出力）で確かめる。

差分テスト（`tests/diff/graph_matrix.py`、負の辺を含む乱択のグラフ）で翻訳と実装を確かめる。
