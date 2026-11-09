# tree_lca_same_depth

`cp::tree_lca_same_depth(anc, u, v, depth)` は、同じ深さ `depth` にある 2 頂点 `u`、`v` の最近共通祖先（2 つの根への経路が最初に合流する頂点）を、ダブリング表 `anc` から返す。`experiments/library/cpp/tree/tree.hpp` の `Tree::lowest_common_ancestor` の後半（深い方を `ancestor` で持ち上げて深さを揃えたあとの二分探索）を、検証できる形に書き直した。深さを揃える前半は `cp::tree_ancestor` で行う。

元のソースからの変更:
- `Tree` の他のメンバー（`depth_`、`root_`、`ancestor_`）を使わない関数にし、表 `anc` と共通の深さ `depth` を引数で渡す。`u == v` なら `u` を返す。
- 2026-11-08以前の原本の `bit_width((unsigned)du)` は、`2^top <= depth` を満たす最大の `top` を求める `while` ループに変える。降下は元より 1 段浅い `top` から始める（元の最上段では `u`、`v` のどちらも根に着くので何も動かない）。降下の `for (k = ...; k >= 0; k--)` は `while` ループで書く。
- 最後の表の読み出し `return anc[0][u]` は、検証済みの式の言語が「行の読み出しは宣言か代入の右辺だけ」を許すため、一度ローカル変数に受けてから返す。
- 元の `lowest_common_ancestor` は深さ配列を使って深さを揃えるところまでを 1 つの関数に持つ。ここでは分けており、元の関数全体としての検証は `tree_ancestor` と本関数の合成（C++ の呼び出し側）になる。分けたことは `docs/experiments_status.md` の違反一覧に載せた。

前提: `0 <= depth < 2^30`、`u`、`v` は根付き木（根の親は根自身）の頂点で、どちらも深さ `depth`、`0 <= u, v < n`、`n < 2^31`、`depth < 2^(K+1)` を満たす `K` について、各レベル `k <= K` の行 `anc[k]` が `n` 個の要素を持ち、すべて `[0, n)` にある。表は `anc[k][x] == f^(2^k)(x)`（`f` は親写像）。

結果（`Proofs/TreeLcaCall.lean`、一般の入力について証明）: 返り値 `w` は `n` 未満で、ある `k` について `f^k(u) == w == f^k(v)` かつ `s < k` なら `f^s(u) != f^s(v)`（2 つの軌道が最初に合流する点）。`u == v` なら `k = 0`、`w == u`。木の深さの性質（根の深さ 0、親の深さ +1 = 子の深さ）から、各軌道が `depth` ステップ後に根に着くため合流点が存在する。

時間と領域: `top` の求めと降下で合わせて `O(log depth)` 回の反復で、モデル上の仕事量は呼び出し側の引数評価を除いて `300 * (K + 1) + 500` 以下。追加領域は局所変数だけ。

証明は `Proofs/TreeLcaMath.lean`（最初に合流する時刻の存在 `first_meet`、降下の関数版 `descA` とその不変条件 `descA_spec`: `u = f^a(u0)`、`v = f^a(v0)`、まだ合流していない、残り距離が `2^c` 未満）、`Proofs/TreeLcaExec.lean`（`pexecM` による 3 つのループと全体の実行）、`Proofs/TreeLcaPrepare.lean`/`Proofs/TreeLcaCall.lean`（呼び出し）。

定理に含めていないこと: 表が `doubling` の出力であること、返り値が「共通祖先のうち深さ最大のもの」であることの Lean での定理（合流点なので従うが、証明はしていない）、深さの異なる頂点（`tree_ancestor` で揃える）。C++ のテストは `tests/tree_lca_same_depth.cpp`（頂点数 1〜14 のランダムな根付き木で、同じ深さのランダムな 2 頂点を素朴な持ち上げと照合する）。


2026-11-08の原本修正:

`Tree::lowest_common_ancestor` は降順ループを `(int)ancestor_.size()-1` から開始するよう更新された。旧上限 `bit_width((unsigned)du)` は、親配列 `[0,0,1,1]` で頂点2/3を問い合わせると `du=2`、表は2行なのに行2を読み範囲外になる。利用者の変更はこの誤りを直す。`build_ancestor()` の表は `bit_width(n_-1)` 行で、`n_>=2` と有効な頂点・根付き木、構築済み表を前提とすれば最終行からの降下は安全である。余分な高位段では両頂点が根へ達し、更新されない。全行を調べる原本の検索時間は `O(log N)`、追加領域は `O(1)`。この公開関数の深さに基づく開始段と既存C++生成モデルは変更していない。

`TreeLcaMath.lca_all_rows_spec` は、表全体が正しいダブリング表で共通深さが `2^T.length` 未満なら、`descA T T.length` が最初の合流点の直前を返すことを既存の降下不変条件から示す。`all_rows_lca_correct` は同一頂点の早期returnも含めて、返却値が頂点範囲内かつ最初の共通祖先であることを示す。`all_rows_indices` は走査段がちょうど実在する行であることを示す。登録回帰 `test_original_tree_lca.py` はこれら3 rootsを独立kernelで検査し、原本ヘッダーそのものをC++20/UBSanとvector境界検査で確認する。C++20は原本 `doubling` の `bit_width` に必要である。

この更新は元class全体の自動生成C++モデルや全メンバーの証明ではない。既存公開関数のC++由来の一般証明と、元classに対する新しい数学仕様・C++回帰の範囲を区別する。singletonの `lowest_common_ancestor(0,0)` は表を読まず成功するが、元の `build_ancestor()` が `doubling(...,0)` のassertに達する残件はこの変更で直っていない。
