# tree_order

`cp::tree_order(head, target, parent, ord, root, n)` は、根付き木の幅優先の頂点の並びを `ord` に書く。`tree_full_dp` に渡す `ord`（各頂点が親より後に来る並び）を作るための部品で、元のソース（`experiments/library/cpp/tree/tree.hpp` の `Tree::full_tree_dp`）が再帰の呼び出し順で暗黙に持っていた「親が先」の順序に相当する。

木は CSR 配列（頂点 `v` の隣接頂点は `target[head[v] .. head[v + 1])`）と、`tree_root` が書く親配列 `parent`（`parent[root] == root`、他の頂点 `w` では `w` から `root` への経路上の隣）で渡す。`ord[0] = root` から始め、`ord[i]` の子（`parent[w] == ord[i]` を満たす隣接頂点 `w`）を末尾へ追加していく。

前提: `n >= 1`、`n + 2 < 2^31`、`head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size() < 2^31 - 1`、すべての `target[p]` が `[0, n)`、グラフは対称な木（連結、自己ループ・閉路・多重辺なし）、`0 <= root < n`、`parent` は上のとおり（`parent.size() == n`）、`ord.size() == n`（呼び出し前の中身は何でもよい）。

結果（`Proofs/TreeOrderCall.lean` の `tree_order_correct`、上の前提のもとで一般の入力について証明。前提は `Proofs/TreeOrderMath.lean` の `TO` にまとめてある）: 終了後の `ord` は `0 .. n - 1` の順列で、`ord[0] == root`、`root` 以外の各頂点は自分の親より後に来る。停止し、`ord` の範囲外への書き込みなど未定義動作は起きない。

時間と領域: 辺の数 `m = target.size()` について、モデル上の仕事量は呼び出し側の引数評価を除いて `1100 * m + 1600 * n + 700` 以下、vector への書き込みは `m + 2 * n + 6` 回以下。追加領域はスカラーのセル高々 400 個（呼び出し側の frame に加えて、入力の大きさによらない定数）。

定理に含めていないこと: 前提を破る入力（未定義動作）、`parent` を作る部分（`tree_root`）。C++ のテストは `tests/tree_order.cpp`（ランダムな木で、`ord` が順列であること、`ord[0] == root`、親が子より先であることを、`ord` の初期値を乱数にして確かめる）。
