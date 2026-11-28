# tree_lca_same_depth

`cp::tree_lca_same_depth(anc, u, v, depth)` は、同じ深さ `depth` にある 2 頂点 `u`、`v` の最近共通祖先（2 つの根への経路が最初に合流する頂点）を、ダブリング表 `anc` から返す。`experiments/library/cpp/tree/tree.hpp` の `Tree::lowest_common_ancestor` の後半（深い方を `ancestor` で持ち上げて深さを揃えたあとの二分探索）を、検証できる形に書き直した。深さを揃える前半は `cp::tree_ancestor` で行う。

元のソースからの変更:
- `Tree` の他のメンバー（`depth_`、`root_`、`ancestor_`）を使わない関数にし、表 `anc` と共通の深さ `depth` を引数で渡す。`u == v` なら `u` を返す。
- `depth > 0` の降下は `std::bit_width(static_cast<unsigned>(depth)) - 1` から始める。この段は `2^k <= depth` を満たす最大の `k` で、表にそれより上の行がなくてもよい。
- 最後の表の読み出し `return anc[0][u]` は、検証済みの式の言語が「行の読み出しは宣言か代入の右辺だけ」を許すため、一度ローカル変数に受けてから返す。
- 元の `lowest_common_ancestor` は深さ配列を使って深さを揃えるところまでを 1 つの関数に持つ。ここでは分けており、元の関数全体としての検証は `tree_ancestor` と本関数の合成（C++ の呼び出し側）になる。分けたことは `docs/experiments_status.md` の違反一覧に載せた。

前提: `0 <= depth < 2^30`、`u`、`v` は根付き木（根の親は根自身）の頂点で、どちらも深さ `depth`、`0 <= u, v < n`、`n < 2^31`、`depth < 2^(K+1)` を満たす `K` について、各レベル `k <= K` の行 `anc[k]` が `n` 個の要素を持ち、すべて `[0, n)` にある。表は `anc[k][x] == f^(2^k)(x)`（`f` は親写像）。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/TreeLcaSameDepth.lean` を生成し、`Proofs/Cpp/TreeLcaSameDepth.lean` が前提を満たす全入力について次を証明する。

- `tree_lca_same_depth_spec`: `f` が `[0, n)` をそれ自身に写し、`u`、`v` が `[0, n)` にあり、`depth < 2^30`、`f^depth(u) == f^depth(v)`、表が `k = 0` と `2^k <= depth` の各 `k` について `anc[k][x] == f^(2^k)(x)`（`TabLca`）のとき、返り値 `w` は 2 つの経路が最初に合流する点（`FirstMeet`: ある `a` について `f^a(u) == w == f^a(v)` かつ `s < a` なら `f^s(u) != f^s(v)`）。根付き木で同じ深さの 2 頂点なら、どちらも `depth` ステップで根に着くので前提を満たし、`w` は最近共通祖先である。
- tick 数は `2 bitWidth(depth) + 4` 以下（`O(1 + log(depth + 1))`）。降下の不変条件 `Inv2` は、`(u', v') = (f^a(u), f^a(v))` がまだ合流しておらず、`2^(k+1)` ステップ以内に合流すること（`step_diff`、`step_same`）。
- 定理に含めていないこと: 表が `doubling` の出力であること、深さの異なる頂点（`tree_ancestor` で揃える）。

差分テスト（`tests/diff/tree_lca_same_depth.py`）と C++ のテスト `tests/tree_lca_same_depth.cpp`（頂点数 1〜14 のランダムな根付き木で、同じ深さのランダムな 2 頂点を素朴な持ち上げと照合する） で翻訳と実装を確かめる。

2026-11-08の原本修正:

`Tree::lowest_common_ancestor` は降順ループを `(int)ancestor_.size()-1` から開始するよう更新された。旧上限 `bit_width((unsigned)du)` は、親配列 `[0,0,1,1]` で頂点2/3を問い合わせると `du=2`、表は2行なのに行2を読み範囲外になる。利用者の変更はこの誤りを直す。`build_ancestor()` の表は `bit_width(n_-1)` 行で、`n_>=2` と有効な頂点・根付き木、構築済み表を前提とすれば最終行からの降下は安全である。余分な高位段では両頂点が根へ達し、更新されない。全行を調べる原本の検索時間は `O(log N)`、追加領域は `O(1)`。公開関数は共通深さに基づく開始段を使う。

`TreeLcaMath.lca_all_rows_spec` は、表全体が正しいダブリング表で共通深さが `2^T.length` 未満なら、`descA T T.length` が最初の合流点の直前を返すことを既存の降下不変条件から示す。`all_rows_lca_correct` は同一頂点の早期returnも含めて、返却値が頂点範囲内かつ最初の共通祖先であることを示す。`all_rows_indices` は走査段がちょうど実在する行であることを示す。2026-11-08 の回帰ではこれら3 rootsを独立kernelで検査し、原本ヘッダーを当時の C++20/UBSan と vector 境界検査で確認した。原本の `doubling` は標準の `bit_width` を使う。

この更新は元class全体の自動生成C++モデルや全メンバーの証明ではない。既存公開関数のC++由来の一般証明と、元classに対する新しい数学仕様・C++回帰の範囲を区別する。singletonの `lowest_common_ancestor(0,0)` は表を読まず成功するが、元の `build_ancestor()` が `doubling(...,0)` のassertに達する残件はこの変更で直っていない。
