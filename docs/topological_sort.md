# topological_sort

`cp::ListGraph<Cost, E>` の `topological_sort()` と `topological_sort_minimum()` は、カーンの方法で全頂点を並べる。元の `experiments/library/cpp/graph/topological_sort.hpp` の2メンバーを `library/graph/graph_list.hpp` に置いた。通常版は入次数ゼロの頂点を元と同じスタックで管理する。辞書順最小版は最小ヒープを使う。閉路がある場合はどちらも空の配列を返す。頂点数ゼロのグラフの完全な順序も空である。

## 前提と計算量

- 各辺の `to` は `[0, n)`。走査する辺数 `m` は実際の隣接行の弧の総数で、平行辺と自己ループを含む。`operator[]` から加えた辺にも同じ条件を適用する。入次数など、入力と途中の整数は C++ の型の範囲に収まるものとする。辺の費用や ID に依存しない。
- 通常版の時間は O(1 + n + m)、辞書順最小版は O(1 + m + n log(n + 1))。追加領域はどちらも O(n)。
- 元のソースからの変更はクラス内への配置、標準ヘッダと名前修飾、コメントの整理である。スタックと最小ヒープの選択、頂点と隣接行を読む順、作業領域の確保、戻り値の型は元と同じ。

## `ListGraph` メンバーの検証

`Proofs/Cpp/GraphList.lean` の `topological_sort_spec` と `topological_sort_minimum_spec` は、生成モデルの停止、グラフの保持、結果、手数を示す。完全な順序では各頂点が1回現れ、辺は前から後ろへ向かう。空でないグラフで結果が空なら、完全なトポロジカル順序は存在しない。辞書順最小性は、他の完全な順序と最初に異なる位置で返り値の頂点が小さいことを `TopologicalResult.lexicographically_minimal` が示す。

入次数は未処理の頂点から入る弧の個数であり、待機集合には未処理の入次数ゼロの頂点だけが入る。この不変条件を、平行辺を1本ずつ数えるモデルで証明した。辞書順最小版では待機集合の最小値を選ぶ。手数は通常版で `2 + 10n + 2m` 以下、辞書順最小版で `2 + (3k + 7)n + 2m` 以下（`k = log₂(n + 1) + 1`）。頂点ごとの挿入と取り出しを計上するため、ヒープの費用上界は辺数に掛からない。`topological_sort_workspace_slots` は入次数、予約した順序、待機集合と戻り値のコピーを含むモデル上の個数を `4n` 以下に抑える。

C++ の回帰は全順列から得た辞書順最小の有効順序と照合し、独自の辺型、平行辺、自己ループ、空グラフも扱う。C++ と生成 Lean の差分では、DAG と一般の有向多重グラフで両版の頂点列を照合する。

## CSR の自由関数

`cp::topological_sort(head, target, indeg, order, n)` は、CSR 配列で表した有向グラフのカーンの方法を実装する。

グラフは CSR 形式の配列で渡す: 頂点 `v` から出る辺の行き先は `target[head[v] .. head[v + 1])`。結果は呼び出し側の `order` に書き、並べた頂点の個数 `k` を返す。

`order` 自体をキューとして使う。`k < n` は閉路があることを表す。呼び出し側は作業領域 `indeg` を 0 で埋めて渡す。

前提: `head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size()`、すべての `target[p]` が `[0, n)`、`indeg.size() == order.size() == n`、`indeg` の全要素が 0、`n < 2^31 - 2`、`target.size() < 2^31 - 1`。

結果（`Proofs/Cpp/TopologicalSort.lean` の `topological_sort_correct`、一般の入力について証明）: 返り値 `k` と `order` の先頭 `k` 個 `Q` について
- `Q` の要素は互いに異なり、すべて `[0, n)` で、`k ≤ n`。
- `Q[j]` の入ってくる辺の始点 `u`（`Q[j]` が `u` の行き先に含まれる）は、必ず `Q` の `j` 番目より前にある。
- `Q` に含まれない頂点 `w` には、`Q` に含まれない始点 `u` からの辺 `u → w` がある（したがって `k < n` ならグラフに閉路がある）。`k = n` なら `order` は全頂点の置換で、すべての辺は前から後ろへ向かう。
`order` の `k` 番目以降は元の値のまま、`indeg` は元の入次数から処理した辺の本数を引いた値になる。

### CSR の検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TopologicalSort.lean` を生成する。`Proofs/Cpp/TopologicalSort.lean` は、翻訳した 3 つのループの配列が純関数モデル（`Proofs/Math/TopoSortMath.lean` の `initSt`・`kahnL`・`decr`）の状態に常に一致することを示し（`Rel`。入次数の計数 `count_step`、入次数 0 の頂点の投入 `enq_step`、辺 1 本の処理 `decr_step`）、モデルの `kahn_final` から上の結果を導く。

- tick 数は `1 + m + n + n + W` で、`W`（取り出した頂点の出辺の数の和）は `m` 以下（`W_le`）。全体で `1 + 2n + 2m` 以下、`O(n + m)`。
- 定理に含めていないこと: 辞書順最小版、返り値が `n` であることと閉路が無いことの同値の Lean での定理（上の 3 点から従うが、証明はしていない。C++ のテストで確認している）、`indeg` が 0 でない入力（未定義の挙動ではなく単に結果が変わる）。

差分テスト（`tests/diff/topological_sort.py`、DAG と一般のグラフ）と C++ のテスト `tests/topological_sort.cpp`（頂点数 0〜8 のランダムな DAG と一般のグラフを、到達可能性の閉包による閉路判定と照合し、3 つの性質を直接確認する） で翻訳と実装を確かめる。
