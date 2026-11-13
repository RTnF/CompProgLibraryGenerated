# tree_full_dp

`cp::tree_full_dp<P>(head, target, parent, ord, dp, pre, suf, up, full, root, n)` は、全方位木 DP（rerooting）である。`experiments/library/cpp/tree/tree.hpp` の `Tree::full_tree_dp` から、検証できる形に書き直した。`P` は DP の方針（`e()`、`op(a, b)`、`sum_up(x)`）で、頂点の DP 値は `sum_up(op(e(), 子の DP 値...))` である。`op` は可換・結合的で、単位元は `e()` とする。検証した具体化は `DpHeight<long long>`（`e() = 0`、`op = max`、`sum_up(x) = x + 1`。頂点の値は、そこから出る最長の下り経路にある頂点の数）。

グラフは CSR 配列（頂点 `v` から出る辺は `target[head[v] .. head[v + 1])`）で渡し、木の根付けは `tree_root` が書く親配列 `parent` と、親が子より先に来る頂点の並び `ord`（たとえば深さの昇順）で渡す。結果は呼び出し側の vector に書く。

結果:
- `full[v]`: 木全体を `v` を根として見たときの `v` の DP 値、つまり `v` の各隣接頂点 `w` について「辺 `(v, w)` を除いた `w` 側の成分を `w` を根として見たときの DP 値」を `op` で束ねて `sum_up` をかけた値。
- `dp[v]`: 木を `root` を根として見たときの `v` の部分木の DP 値。
- `up[w]`（`w != root`）: 辺 `(parent[w], w)` を除いた `parent[w]` 側の成分を `parent[w]` を根として見たときの DP 値。`up[root] = e()`。
- `pre[p]` / `suf[p]`（`p` は親から子への辺）: 同じ親の、`p` より前 / 後の子の DP 値の `op` による積。

元のソースからの変更（検証できる形にするために書き換えた）:
- 再帰（深さ優先探索）をやめ、親が子より先に来る頂点の並び `ord` を引数に取る反復に変えた。下から上へ（`ord` の逆順）`dp`・`pre`・`suf`、上から下へ（`ord` の順）`up`・`full` を求める。元の再帰が返す値と同じ値を、呼び出し側の vector に書く。
- 隣接リストの代わりに CSR 配列を使う。`ord` は呼び出し側が用意する（`tree_root` が書く親配列と合わせて使う）。
- 元は `P` を型パラメータに持たず関数オブジェクトの組を取る形だが、ここでは `e`・`op`・`sum_up` を静的関数に持つ型 `P` を取る。値の型 `T` は `P::value_type` のままテンプレートである。

前提: `n >= 1`、`n + 2 < 2^31`、`head.size() == n + 1`、`head[0] == 0`、`head` は広義単調増加、`head[n] == target.size() < 2^31 - 1`、すべての `target[p]` が `[0, n)`、グラフは対称な木（連結、自己ループ・閉路・多重辺なし、各辺 `u -> v` に逆辺 `v -> u` がある）、`0 <= root < n`、`parent` は `root` を根とする親配列（`parent[root] == root`、他の頂点では経路上の隣）、`ord` は `0 .. n - 1` の順列で各頂点が親より後に来る、各 vector の長さ（`parent`・`ord`・`dp`・`up`・`full` は `n`、`pre`・`suf` は `target.size()`）。`dp` と `up` は呼び出し前に `[0, n]` の値を持つ（たとえばゼロ初期化）。`pre`・`suf`・`full` の呼び出し前の値は何でもよい。

結果（新方式、`docs/translation.md`。`Proofs/Cpp/TreeFullDp.lean` の `tree_full_dp_spec`）: 翻訳器は `P::e()` などポリシーの静的メンバーの呼び出しを、明示的な引数 `P : cp.tree_full_dp.Policy_P T`（使われた静的メンバーを持つ構造体）のフィールドの呼び出しに翻訳する。定理は任意のポリシーについて、その 3 つの関数が可換モノイド `M`（`Proofs/TreeDpAlg.lean` の `CM`。値の集合 `V` の上で結合・可換・単位元 `e()`、`sum_up` は `V` を保つ）の演算を tick 1 で計算するという仮定のもとで述べる。上の前提（`Pre`: CSR 配列の範囲と単調性、木の構造 `TS`）と、`dp`・`up` の呼び出し前の値が `V` に属することのもとで、終了後の `dp'`・`up'`・`full'` が、すべての `v < n` で `dp'[v]`、すべての `w != root` で `up'[w]`、すべての `v < n` で `full'[v]` について、上の意味の値（`Proofs/TreeDpSpec.lean` の `Ef`）に等しく、tick 数は `2 + 7 n + 8 m` 以下（`m = target.size()`）。証明は下から上の走査を不変条件 `P1`（内側ループ `I2`、`I3`）、上から下の走査を `P2`（内側ループ `I5`）で書き、`final_facts` で旧来の `Proofs/TreeDpMath.lean` の `dp_deriv`・`up_deriv`・`full_deriv` の前提に変える。具体化 `DpHeight<long long>` は `heightCM`（非負整数上の `max`、`sum_up(x) = x + 1`）と `height_e`・`height_op`・`height_sum_up` で仮定を満たす。差分テストは `tests/diff/tree_full_dp.py`。

定理に含めていないこと: 静的メンバーが tick 1 で計算しない `P`、`ord`・`parent` を作る部分（別の関数）、上の前提を破る入力（未定義動作）。C++ のテストは `tests/tree_full_dp.cpp`（ランダムな木で、`dp`・`up`・`full` を再帰による定義どおりの高さと比較する）。


## 順序生成との接続

`Proofs/TreeOrderToDp.lean` の `TreeOrderMath.TO.toTS` は、`tree_order_correct` が返す長さ・重複なし・頂点範囲・根が先頭・親が先行するという順序の性質から、全方位 DP の `TS` を構成する。ただし、辺が親子関係のいずれかであること（`cls`）と、各非根頂点から親への逆辺（`parArc`）も必要である。これらは上記の対称な木の条件に含まれる。順序生成側の `TO` だけからは導かない。

`tests/test_tree_order_dp.py` は、実際の順序生成の数学的結果から有効な2頂点の木の `TS` を構成する例と、親配列 `[0,0,0]` の三角形では順序 `[0,1,2]` が生成できても `TS` が成立しない反例を確認する。`tests/tree_full_dp.cpp` は `cp::tree_order` で作った順序を `cp::tree_full_dp` に渡し、ランダムな根・頂点ラベル・隣接順序を含む3000例で素朴な高さ計算と比較する。

これは各関数の呼出し証明の前提をつなぐ数学的な補題であり、任意の C++ 呼出し元全体の証明や、一般の方針型 `P` の実行証明を追加したものではない。
