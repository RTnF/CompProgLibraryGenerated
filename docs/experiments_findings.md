# 持ち込みコードの検証で見つけた不具合・注意点

## 2026-11-05: groupの公開側で暗黙変換呼出しが失われている

元のGroupSum/GroupMulの非テンプレートhidden friendと、公開版の関数テンプレートopでは、引数推論と暗黙変換の適用が異なる。元の`GroupSum<long long> a(2); op(a,3LL); op(3LL,a);`と`GroupMul<long long> m(2); op(m,3LL);`はコンパイル/実行に成功し、値5/5/6になる。公開版は同じ呼出しをコンパイルできない。これは元コードの不具合ではなく、公開側の書換えによる未修正のAPI縮小である。オブジェクト同士のlong long演算の既存証明を、この呼出しまで検証済みとは扱わない。

GCC 13.3.0/C++17/offlineでの再現とログは`.cache/wip/group_api_review_20261105/{original.cpp,published.cpp,state.json}`。`docs/group.md`と違反一覧へ反映した。元のフレンド形式を保ち、検証に必要な本文の具体化を共通変換器で扱う方法を調べる。公開C++はまだ修正していない。

同日の追加確認では、コピーと整数からの構築を記録する`Traced`を`GroupAffine`へ渡すと、元の既定構築の2回のコピーが公開版では0回だった。`e()`の構築順も元の1→0から公開版の0→1へ変わる。値1/0は両方で一致する。GCC13.3.0/C++17/-O2の再現は`group_api_review_20261105/constructor_{original,published,guarded}.cpp`と`constructor_observers_state.json`。暗黙変換を直す隔離候補guardedにもこの差が残るため、元の全APIを復元した候補とは扱わない。元の委譲構築・波括弧初期化と、その共通変換・証明への接続を残件として維持する。公開C++は未修正。

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

## 2026-11-05: Groupの公開側の暗黙変換・構築形式を復元

同日に再現した暗黙変換の縮小と、Affineの既定構築のコピー回数/e()の構築順の差を、公開CPPの元hidden friend・委譲・return形式を復元して修正した。元ソースは維持する。記録はdocs/agent/fixes.md、仕様と検証範囲はdocs/group.md。元と同じLLの一般定理と生成モデルの一致を候補で確認後に正本へ統合し、追加後の全件検証は進行中。任意TのLean証明や完全なobject/lifetime ASTの検証が完了したとは扱わない。

## 2026-11-05: library3のGroup/Mappingは同一APIとして統合できていない

GCC13.3.0/C++17で旧版と公開版を直接比較した。旧Groupのpublic field `x/a/b` への書込みは旧版でコンパイル・実行成功、公開版はコンパイル失敗。旧Mappingの `Affine<long long>(2,1).apply(0.5)` は2、公開GroupAffineは引数をlong longへ変換して1。旧GroupSum<double>の正の0の逆元は `e().x-x` により正の0だが、公開版の単項minusでは負の0になる。証拠は `.cache/wip/group_legacy_api_review_20261105/receipt.json` と各CPP/log。元ソースの不具合と断定せず、公開側が旧API/汎用性を保持していない未解消差として台帳を訂正した。

全137件の検証では、元のpublic field・異型Uのapply・値渡し・ide/compose・演算の定義を維持して扱う必要がある。単一の整数具体化やgetterへの置換で旧版検証完了とはしない。独立したnamespaceの元APIを共通変換器と証明で扱う対応も含め、解消まで未完了。

## 2026-11-06: Monoidの公開側で暗黙変換と型の制約が縮小（正本修正・全件gate成功、CI反映前）

GCC13.3.0/C++17で比較し、`op(MonoidMul<int>(2), 3)`と逆順は原本2系列でコンパイル・実行成功、修正前の公開版は関数テンプレートの型推論でコンパイル失敗した。原本の非テンプレートhidden friendをnamespaceの関数テンプレートへ置き換えたため、モノイドへ暗黙変換できる引数を受け付けなくなっている。

コピー構築はできるがコピー代入を削除した型でも、原本のMonoidMax/Minは成功し、修正前の公開版は`r.x = b.x`でコンパイル失敗した。元のstd::max/minで選んだ値をコピーする実装には不要だった代入演算を追加し、Tの制約を狭めている。

証拠は`.cache/wip/monoid_original_review_20261106/native_api_receipt.json`と各compile/runログ。9比較で原本の成功、公開版の想定した診断、隔離候補の成功、既存qualified呼出しの保持を確認した。原本は変更していない。候補のC++成功だけでモデル生成・Lean証明の完了とはしない。正本へhidden friendと元の委譲構築、generic Tのmax/min・ADLを復元した。公開C++/ASan/UBSan/template-firstは成功し、既存公開定理のLeanビルドも成功。独立kernel・全件gateの最新状態はhandoffを参照し、任意Tと完全object/lifetimeの検証は部分対応を維持する。

## 2026-11-06: monoid_lazyの原本APIとコピー効果の差（未修正）

原本`RangeAddRangeMaxMin<long long>::RangeAdd::id()`はC++/UBSanで成功するが、
対応する公開`cp::RangeAdd<long long>::id()`はメンバーが存在せずコンパイルできない。
原本の4 outer classとnested class、static e/id、member applyは、公開側ではflatな3クラスと
別のmember名になっている（入れ子の型の不足はソースでも確認した）。

`RangeSetRangeMaxMin<Observed>::RangeSet`のcomposeは2引数を値渡しし、選んだ引数を返す。
公開`cp::RangeSet<Observed>`はconst参照で受け、Tとflagから作り直す。
コピー構築をカウンタで観測する型で比較すると、同じ入力に対し結果vはともに2だが、
原本のコピー回数3に対して公開側は2となった。元にあるコピーの副作用を保持していない。
原本・公開CPPはこの調査では変更していない。修正済みとしてfixesへは載せない。

GCC13.3.0/C++17/UBSan/offlineの4比較の証拠は
`.cache/wip/monoid_lazy_original_review_20261106/native_api_receipt.json`とcompile/runログ。
`identity.cpp`と`copy_effects.cpp`を同じdirectoryに保存した。
現状の共通入口はnested非template型の選択とrecord型のmember template引数を扱えない。
型要求を構造化し、同じTUのalias/nested/outer/primary IDと元sourceへの帰属を照合する拡張を進める。
LLの既存flatモデルの成功で元の全APIや任意Tの検証完了とはしない。
この調査は322c987後のローカル変更で、そのCI/リリースに含まれない。
