# 持ち込みコードの検証で見つけた不具合・注意点

2026-10-09 時点。検証（C++ の実行と Lean の証明）の過程で確認した、元の `experiments/` のコードの問題を残す。いずれも元のソースは変更していない。

| 元のコード | 内容 | 確認 | 公開版での扱い |
| --- | --- | --- | --- |
| `segment_tree/binary_indexed_tree.hpp` の `BinaryIndexedTree(const vector<T>&)` | 構築の第 2 ループ `tree[i + (i & -i)] += tree[i]` が `i + (i & -i) > v.size()` の場合に範囲外へ書き込む（`v.size() = 3`、`i = 2` で添字 4。`tree.size()` は 4）。上限の検査がない。 | `std::vector::at` で `out_of_range` を再現（2026-10-09） | `fenwick`（`fenwick_add`/`fenwick_sum`）には構築を含めていない。構築は `fenwick_add` の反復で作るか、`i + (i & -i) <= n` を検査して直す必要がある。 |
| `algebraic_structure/group.hpp` の `GroupMul::inv()` | `1 / _x`。整数型では `_x = ±1` 以外で 0 になり、コンストラクタの `assert(x != 0)` が失敗する。浮動小数の `T` を想定した実装。 | `group` の `groupmul_inv_correct` の前提（`x = 1 ∨ x = -1`）として明記 | `docs/group.md` に記載 |
| `algebraic_structure/monoid.hpp` の `MonoidMul::op` | 符号付き整数の積が桁あふれすると未定義動作。 | `mul_op_correct` の前提に `x * y` が収まることを含めた | `docs/monoid.md` に記載 |
| `array/cumulative_sum.hpp` の `CumulativeSum` | 部分和 `cs[b] - cs[a]` と累積 `cs[i-1] + v[i-1]` が符号付き桁あふれし得る。 | `prefix_sums_correct` の前提（累積和が収まること） | `docs/prefix_sums.md` に記載 |


## 2026-10-31: Segment Tree Beats 公開候補の構築サイズ

`library/segment_tree_beats.hpp` の構成子は、節点配列の長さを `8 * (int)a.size() + 8` で計算する。これは符号付き `int` の演算なので、`n >= 1` だけでなく `8*n+8 < 2^31` が必要である。サイズ計算を変更せず、`docs/segment_tree_beats.md` の前提を公開定理 `segment_tree_beats_new0` の `8*n+8 <= L < 2^31` と合わせた。大きい入力を実際に確保したとは扱わない。

## 2026-10-31: 修正済み持ち込みコードの追跡

冒頭の表は2026-10-09時点の記録である。現在は Fenwick 木の構築の境界チェックと SquareMatrix の単項マイナス代入が元ファイルにも修正済み（`docs/agent/fixes.md`）。台帳をこの2ファイルの実コードで再走査し、単項マイナスの検査は修正後の値を確認する回帰検査へ更新した。行列比較の存在しない `x` 参照と `pow(1)` の不要な最終二乗の桁あふれは残る。


## 2026-10-31: Beats の実スタックと証明前提の不一致

`BeatsRepInv.Lens b L` はnode/entered配列と3本のDFSスタックに共通の容量Lを要求する。実構成子ではnode配列8*n+8に対しスタックは各256なので、n≥32で構築定理の8*n+8≤Lと両立しない。C++の不具合と断定する根拠はなく、証明の適用範囲の不足である。中点分割Shapeから高さ≤31を示し、node容量Lとstack容量Sを分離する構築/操作証明を準備中。公開Call全体の接続と独立kernel検査は未完了であり、n≤31へ制限して解決済みとはしない。


## 2026-11-01: Beats配列拡大による入力範囲の縮小

持ち込みSegmentTreeBeatsは4*n要素を確保し、n0を次の2冪へ丸めて2*n0までを使う。n=2^28、n0=nのときこれらと木の添字は32-bit intに収まる。一方公開版の8*n+8はintの上限を超える。公開版は未使用節点/葉の子への無条件参照に合わせて配列を広げているため、その長さ計算と子添字演算も併せて改善する必要がある。現在の8*n+8<2^31前提により元の入力範囲を狭めていることを、experiments_statusの違反一覧と部品docへ明記した。Cppは未修正、巨大入力の実確保なし。Leanのi32.validで旧4*n/2*n0がtrue、新8*n+8がfalseとなる算術回帰例を追加した。


## 2026-11-02: SquareMatrixの比較と不要な最終二乗を原本で修正

原本の比較をmatの各要素へ直し、powは指数を右シフトして残りがある場合だけ二乗するようにした。pow(ll) const、行配列参照、公開mat配列、aggregate/trivial/standard-layoutの性質を保つ。元の非負指数の用途を明示し、負の指数はassertで拒否する。修正記録はdocs/agent/fixes.md、原本の回帰はtests/imports/square_matrix_source.cpp。全クラスの共通変換器対応とLean証明は引き続き未完了で、C++の修正だけで公開・検証完了とは扱わない。
