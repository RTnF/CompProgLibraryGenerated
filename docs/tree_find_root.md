# tree_find_root

`cp::tree_find_root(parent, n)` は、根を指定しない親配列で与えられた木の根を返す: `parent[i] == i` または `parent[i] < 0` を満たす最後の添字 `i < n`、なければ `-1`。`experiments/library/cpp/tree/tree.hpp` のコンストラクタ `Tree(vector<int> &parent)` の根を探すループを書き直した。

元のソースからの変更:
- 条件 `parent[i] == i || parent[i] < 0` を、2 つの入れ子の `if`（`parent[i] == i` でなければ `parent[i] < 0` を調べる）で書く（短絡評価と同じ結果）。
- 根が見つからない場合、元は `assert(r >= 0)` で失敗する。ここでは返り値 `-1` で表し、呼び出し側が確かめる。
- 根を決めたあとの辺の構築（`tree_edges_from_parent`）と `build_depth`（`tree_root`）は別の公開部品。

前提: `0 <= n < 2^31 - 1`、`parent.size() >= n`。

結果（`Proofs/TreeFindRootCall.lean`、一般の入力について証明）: 返り値は `rootT parent n`（`rootT` は、`i` の昇順に条件を満たす `i` で更新する関数）。つまり条件を満たす最後の添字、なければ `-1`。

時間と領域: モデル上の仕事量は呼び出し側の引数評価を除いて `220 * n + 200` 以下、追加領域は局所変数だけ。

証明は `Proofs/TreeFindRootExec.lean`（`rootT`、代入 `yas_exec`、1 反復 `bfr_exec`、全体 `body_exec`。入れ子の `if` には `Proofs/TreeEdgesExec.lean` の `wrap_true`/`wrap_false` を使う）、`Proofs/TreeFindRootPrepare.lean`/`Proofs/TreeFindRootCall.lean`（呼び出し）。C++ のテストは `tests/tree_find_root.cpp`（自己親・負の親・大きな値を含むランダムな配列で、元のループと照合する）。
