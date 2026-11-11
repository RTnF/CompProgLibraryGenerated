# 持ち込みコードの検証で見つけた不具合・注意点

## 2026-11-08: Max/Minの浮動小数単位元と修正範囲

元の `monoid_lazy.hpp` のAdd/Set両系統で、RangeMax<double>::e()は最小の正の正規化数を返すため、
負値-7に対して `op(a,e()).x == a.x` が偽になった。
RangeMin<double>::e()も有限の最大値を返すため、正の無限大の入力で同じ単位元則が破れた。
G++/UBSanで4例を再現した（`.cache/wip/extrema_object_factory_20261108/floating_identity.cpp`）。
この原本4箇所は標準浮動小数型だけconstexpr分岐し、無限大対応型には±infinity、他ではlowest/maxを使うよう修正済み。
非浮動小数の従来min/max経路を残し、演算子を持たないOpaque型でもe()が使えることを回帰した。
修正の表とdriverは `docs/agent/fixes.md` / `tests/imports/monoid_lazy_floating_identity.cpp` を参照する。
浮動小数のLean誤差/identity/lifetime全検証を完了したとは扱わず、NaNのmonoid則も主張しない。

**追跡対象も修正・関連検査成功（2026-11-08）:** `library/algebraic_structure/monoid.hpp` と `experiments/library/cpp/algebraic_structure/monoid.hpp` の
MonoidMax/MonoidMinにも同じmin/maxの不具合があった。
`.cache/wip/extrema_object_factory_20261108/monoid_identity_followup.cpp` をG++/UBSanで実行し、
public/originalのMax(-7)とMin(+infinity)の4例で単位元則が偽であることを確認した。
両ファイルも同じ標準浮動小数のconstexpr分岐へ修正し、非浮動小数のAPIを保持した。
新driver `tests/imports/monoid_floating_identity.cpp` は両版の修正前で終了1を確認済み。
演算子を持たないOpaque型と、min/maxだけを持つnumeric_limits特殊化でもe()が使えることを含めて、
native回帰と既存LL生成・証明、公開sanitizer/template-first/fresh bridgeと独立kernel検査が成功した。
原本3639/公開3668宣言、入力hash不変を含む結果はhandoffを参照する。
浮動小数を検証対象から外したり、-7を禁止したりして解消扱いにしない。

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

（2026-11-11 に公開を取り下げた）`library/segment_tree/segment_tree_beats.hpp` の構成子は、節点配列の長さを `8 * (int)a.size() + 8` で計算する。これは符号付き `int` の演算なので、`n >= 1` だけでなく `8*n+8 < 2^31` が必要である。サイズ計算を変更せず、`docs/segment_tree_beats.md` の前提を公開定理 `segment_tree_beats_new0` の `8*n+8 <= L < 2^31` と合わせた。大きい入力を実際に確保したとは扱わない。

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

## 2026-11-07: 複数fieldの投影と他fieldの計算

原本 `RangeAddRangeSum<long long>` のRangeAdd/RangeSumを同一TUから選ぶ隔離候補は、
原CPPを変更せず13モデルを生成し、通常入力のnative/UBSan比較に成功した。
原object全体の検証へ進むには、結果として返さないfieldの計算も扱う必要がある。

`v = LLONG_MAX`、値fieldが1、sizeが2という演算範囲外の入力では、元のapplyが
`size * v`でUBSanのsigned overflowとなる。一方、従来の投影を使った候補では、
xモデルが失敗してもsizeモデルだけは2を返す。この二つのモデル結果をLeanと固定nanoda
1973依存宣言で確認した。証拠はローカルの
`monoid_lazy_original_review_20261106/mixed_projection_counterexample.json`、
`MixedProjectionCounterexample.lean`、`mixed_add_sum_overflow_native.txt`に保存した。
元CPPの成功条件には全ての中間演算の型範囲条件が必要であり、投影一つの成功だけでは
原object全体の未定義動作不在・総資源を検証したことにはならない。

全constructor引数を一度ずつ評価し、宣言順で全fieldを初期化してから結果fieldを選ぶ
隔離候補も用意した。同じ13モデルとnative比較に成功し、上記入力を両fieldが拒否すること、
通常のv=3/x=7/size=4でx=19/size=4となることを固定nanoda1978依存宣言で確認した。
証拠は`strict_mixed_projection_receipt.json`と`StrictMixedProjectionCheck.lean`。
この候補のapply2モデルは、任意の有効なcallerに対する引数準備・結果・停止・元メモリ保持と
`ScalarPost2 caller Sinit res (1+e1.nodes+e2.nodes) 100 ...`を固定nanoda3580依存宣言で確認した。
非const receiverの書込み権限、long long/intの値引数、積と和の型範囲条件を保ち、
sizeの結果についても全中間演算の範囲条件を要求する。
証拠は`strict_mixed_call_receipt.json`と`StrictMixedCallCorrectness.lean`。

他field内の除算失敗、宣言順でのfield初期化、未初期化field読取り拒否の3ケースも検査し、
構築/makeの各fieldについて16roots・固定nanoda2008依存宣言とnative比較に成功した。
委譲のないconstructorも候補では生成対象へ含め、原本13モデルのbyte不変を確認した。
この候補は正本へ未統合で、全13モデルの一般caller証明、広い拒否境界と関連回帰、
条件付きrecord返却/return xの対応は残る。
任意T/完全object lifetimeを検証済みとする台帳のフラグはfalseを維持する。

### 2026-11-07: strict mixed候補の全13有限モデルと一般caller

原本 `RangeAddRangeSum<long long>` の13モデル（RangeAddの構築/id/compose/applyの2field、RangeSumの構築2種/e/opの各2field）を再生成し、全constructor引数と全fieldを評価する保存モデルとのbyte一致を確認した。`StrictMixedCompleteFixture.lean` の一般定理は任意の有効なcallerについてprepareから返却までの結果・停止・元メモリ保持・work/space上界を示す。固定nanoda3673宣言に成功した（実48190終了0）。値渡しcompose、非const receiver、負のint sizeを保持し、積/和の範囲条件は全fieldの評価に必要なものを課す。

証拠は `.cache/wip/monoid_lazy_original_review_20261106/strict_mixed_complete_receipt.json`、同 `strict_mixed_complete_inputs.json`、`StrictMixedCompleteFixture.lean`。この候補は正本変換器/公開ライブラリには未統合で、任意T・完全なobject lifetime・field投影を組み合わせた単一object呼出しの費用対応は未証明。既存の有限モデルの成功を原本ファイル全体の検証済みフラグへ拡大しない。RangeSetの条件付きcopy/return x、境界回帰、正本統合が残る。

### 2026-11-07: RangeSetRangeSumの暗黙copy/move返却候補

原本はnoop/通常/負sizeを扱えるが、strict mixed候補は `return x` の `void (RangeSum &&)` を未対応として拒否した。別名のcopy_return候補は、既存のtrivial copy/move/destruction guardに加えて同recordの暗黙構成子署名・parameterの全field IDを照合し、条件付きcopyでは選択branchのみを実行し全fieldを読んで投影する。原本未変更で18モデル生成/nativeが成功。全18モデルを覆う38の有限事例を固定nanoda2062宣言で検査し、noop両branch、composeのnoop全4組、負/零size、noop時に危険な積を評価しないこと、更新時のoverflowを両投影が拒否することを確認した。原本CPPのnoop bypass/UBSan overflow拒否も別途一致した。

証拠は `.cache/wip/monoid_lazy_original_review_20261106/copy_return_samples_receipt.json`、`copy_return_set_sum_receipt.json`、`set_sum_guarded_native_receipt.json`、`copy_return_candidate_inputs.json` と `CopyReturnSampleChecks.lean`。検査は有限事例であり、一般caller・任意T・完全object lifetime・単一object費用対応や正本統合は未完了。custom copy/move/dtor等の拒否境界回帰も残る。元のAPIや対応入力は削っていない。

追加回帰では既存RangeAddRangeSumの13モデルのIR/Leanがbyte不変でnativeも成功した（実65386終了0）。独自copy・独自move・独自destructor・ローカルobjectの4境界は意図した理由で拒否した（実87108終了0、同 `copy_return_guards_receipt.json`）。初回move fixtureはcopyが暗黙削除されwitnessが成立しなかったため、default copyを明示して独自moveの拒否を直接検査した。一般caller証明と正本統合は引き続き残る。

### 2026-11-07: mixed/copy返却の正本統合

`verifier/mixed_scalar_functions.py` と `strict_scalar_return.py` を正本companion経路へ統合し、
複数fieldでは全primitive構成子引数と全fieldを宣言順で評価し、同recordのtrivial copy/move返却も扱う。
既存のpublic/非companionプログラムは維持しており、その旧投影経路の全field評価への移行は残る。
`tests/test_nested_templates.py` に原本Add/Sumの13一般callerモデル、Set/Sumの18モデル/38有限事例、
独自copy/move/destructor・ローカルobjectの4拒否境界を登録した。実80528は8tests/243.987秒で終了0、
固定nanoda3673・2062・3600・3652・3606宣言が成功。追加の全field初期化検査も実62213終了0、
16roots/固定nanoda2008宣言で他fieldの7/value失敗、宣言順、初期化前field参照の拒否を確認した。
Clangのforward-read警告は期待した拒否例であり、未定義動作のある例を実行してはいない。

証拠は `tests/lean/original_mixed_add_sum.lean`、`original_mixed_set_sum_samples.lean` と
`.cache/wip/mixed_records_integrated_20261107/focused_receipt.json`。Setの一般caller証明、任意T、
単一objectの総費用/完全lifetime、公開APIの原本への復元、全137件の検証は残る。
この登録済みの局所成功を全件gate/公開完了とは扱わない。原本CPPに変更はない。

### 2026-11-07: 複合型をrecord自身と誤判定する変換器境界

型名の部分一致により `Probe *`、`std::vector<Probe>`、`Probe (&)[2]` のunused引数が
record自身と判定され、scalar2fieldの引数へ誤変換されることを有効なCPP/native/UBSanで
再現した（実12997終了0、`.cache/wip/mixed_records_integrated_20261107/record_type_frontend_before.json`）。
CPPライブラリの不具合ではなく、C++からモデルへのABI対応の誤りである。
`scalar_record_type` を全型一致/トップレベルconst・参照へ限定し、SplitClass/Eraserの判定、
複合引数/返却型/値消去の局所宣言を拒否するよう修正した。単一fieldの返却型はmethod署名の
書換え前にも検査する。原本CPPを変更したり未対応型をscalarへ読み替えたりしない。

単一/複数field×pointer/vector/array/function pointer引数およびpointer/vector返却の12回帰は
実66787終了0、native/UBSan成功と意図した複合型拒否を確認した。初回は結果fixtureのconstructorが
未具体化、次は単一fieldの返却型が先に書換えられていたため、witnessと検査位置を修正した。
証拠は `.cache/wip/record_type_boundary_fix_20261107/boundary_receipt.json`。
旧全件gate44736は成功したが、この修正前の結果なので最終成功へ流用しない。

追加の局所pointer/vector/arrayも含む18回帰は実60213終了0（45.401秒）で成功した。
型境界修正後の関連4スイートも実81165終了0・計35testsで成功し、入力hashは不変だった。
その後、局所compoundの明示拒否と追加fixtureを入れたため、最終全件検査は引き続き必要である。
証拠は同cacheの `focused_receipt_before_local_extension.json` と `boundary_local_receipt.json`。

Set版のRangeSum8モデルは、現変換器でAdd版/Set版を再生成し全NProgram一致を証明することで、
既存の一般caller定理を共有できた。汎用の2fieldコピー評価/scope復元補題を使って、RangeSetの
既定構築/idの4モデルも一般callerで結果・停止・元メモリ保持・work/space上界を示した。
私的検査実74872終了0・固定nanoda3649宣言、入力hash不変。証拠は同cacheの
`set_sum_transferred_receipt.json` / `set_sum_transferred_inputs.json`。これらを
`tests/lean/scalar_record_copy_fields.lean` と `original_mixed_set_sum_callers.lean` へ移し、
既存の18モデル/38事例と合わせて登録検査している。残るSetの値構築/compose/apply6モデル、
任意T、単一object lifetime/総費用、原本全137件の検証は引き続き未完了である。

正本登録後のSet/Sum検査も実45891終了0（79.770秒）、固定nanoda3731宣言で成功した。全18モデルの38事例と12モデルの一般caller定理、および2fieldコピー/scope復元の依存閉包を同時に検査した。記録は同cacheの `registered_set_sum_receipt.json`。値構築・compose・applyの残る6モデルを証明済みとはしない。

### 2026-11-07: Set/Sumの全18 fieldモデルの一般caller証明

値構築2モデル、値渡しcompose2モデル、非const receiverのapply2モデルの一般caller証明を追加した。
composeは条件を一度評価し、選ばれたrecordの全fieldをコピーする。applyは書込み可能なreceiver参照2個と値引数2個を維持し、元callerのメモリを変えずに値引数のxだけを更新する。乗算の型範囲はnoopがfalseのときだけ要求し、負のint sizeを許す。サイズ投影でも元の更新と全fieldコピーを評価する。

`tests/lean/original_mixed_set_sum_{value_ctor,compose,apply}.lean` を既存の登録テストへ統合した。実2047は終了0（79.720秒）、固定nanoda3797宣言で全18モデルの一般caller証明と38事例の依存閉包を検査し、C++/UBSan、noop時の危険な積の非評価、更新時overflowの拒否も成功した。証拠は `.cache/wip/monoid_lazy_set_apply_20261107/registered_receipt.json`。compose単独の一般caller検査は実14377終了0/3581宣言、apply単独は実81314終了0/3604宣言。これらは原本CPPから再生成したモデルと対応付けている。

原本CPPおよび公開headerは変更していない。任意T、各field投影を組み合わせた単一object全体の寿命・総費用、残る原本family、公開API復元と原本全137ファイルの検証は未完了。`monoid_lazy.hpp`全体の移植完了ではないためpushしない。

### 2026-11-07: Set/MaxMinの条件付き構築呼出しは未対応

元の `RangeSetRangeMaxMin<long long>` のRangeSet/RangeMax/RangeMinを同一witnessで具体化した。既定構築・id・compose両分岐・max/minのe/op・apply両分岐と値引数の元値保持はC++/UBSan実行で成功した。原本からのモデル生成は `calls in conditionally evaluated operands cannot be inlined` で拒否された。元の `apply<M>` の `return noop ? x : v;` は、選択した分岐でrecordを構築する形である。現在のinlinerは条件付きoperandの既知呼出しを無条件に前置せず拒否するため、この原本APIをまだ検証できない。

修正前の再現は `.cache/wip/monoid_lazy_set_extrema_20261107/probe.py`、witnessは同folderの `witness.cpp`、修正前の入力hash・結果は `before_conditional/inputs.json` / `before_conditional/receipt.json`（後の成功結果と区別して保存）。実44214は終了0で、native成功とlowering拒否の両結果を記録した。原本の変更や入力制限は追加していない。次は条件の一度だけの評価と選択した分岐だけの構築を保つ変換を検討・検証する。モデル生成、Lean証明、任意Tと完全object lifetimeは未完了である。

### 2026-11-07: 条件付き構築の変換とSet/MaxMinの証明登録

`inline_ast.Inliner.conditional` を追加した。既知呼出しのある整数prvalueの条件式を結果localとIfStmtへ変換し、条件を一度評価し、選択したbranch内でだけoperandの呼出しを展開・代入する。参照/objectの条件式、short-circuit右辺、loop headerの拒否境界は維持する。入れ子の条件の実行回数、未選択側のゼロ除算を評価しないこと、選択側のゼロ除算がfaultになることを9事例とC++/UBSanで確認した。

原本Set/MaxMinの18モデルを生成し、16モデルは既存MonoidInstance/SetSumとの全NProgram/callFuel一致、apply2モデルは元の書込み可能なreceiver参照2個と値引数1個を保つ一般caller定理で登録した。noopの分岐とbranch一時変数のscope終了後を含め、結果・停止・元メモリ保持・IRのwork/space上界を示した。原本の型・API・ソースは変更していない。

実55798は終了0（379.581秒）でinline4＋nested10の14testsに成功し、全検査入力hashが不変。固定nanodaは2539/2008/3600/3673/3867/3652/3606宣言。Set/Sumの全18モデルの一般callerと38事例も合わせて再検査した。その後、宣言対応の点検でAdd/MaxMinのcompose一般callerが未登録と確認したため、`RecordComposeAudit.compose_correct` を追加した。値渡し引数と和の型範囲を保ち、任意callerで結果・停止・元メモリ保持・IR資源上界を示す。追加後の実3137は終了0（54.420秒）、freshなC++モデル再生成と固定nanoda3635宣言が成功した。

証拠は `.cache/wip/monoid_lazy_set_extrema_20261107/final_focused_receipt.json` と同folderの `registered/` / `registered_record_compose/`。14tests後の入力変更はcomposeのfixtureと登録テストの2ファイルだけで、後の局所検査が両変更を覆い、他の入力は不変だった。任意T・任意M、完全object lifetime/単一objectの総費用、公開API復元、原本全137の検証は未完了。原本1ファイル全体の移植完了ではないためpushしていない。

### 2026-11-07: RangeSetの非投影object構築/copyを接続

原本RangeSetRangeSum<long long>::RangeSetの2構築と暗黙copyを、structured TemplateInstanceを通して既存class_copy_layoutのconstructor member export / MemberCopy評価器へ接続した。long long/boolの両fieldを1つのObjectRefで扱い、同一TUのfield/copy宣言IDと原本/witness hashを監査する。原本CPPと公開headerは変更していない。

const元からmutableなコピーを作り、コピー先の両fieldを更新しても元は7/falseのままであること、const先への代入拒否、scope終了直後にコピー先slotへアクセスできず元の2field状態を保持することを9 Lean事例とC++/UBSanで確認した。生成されたcopyの一般layout/observer/value/position/work/space定理も固定nanodaで検査した。AST収集後のwitness改変とraw型要求を拒否する回帰を追加し、support.tomlに新testを登録した（共有241checks）。

初回44145は終了1（unused permission binder警告とLean予約語scoped）であり成功扱いしない。生成時にzero-vectorの未使用引数名を修正し、fixtureを改名した後の実63216は終了0（106.356秒）、新4＋既存layout4の8tests、固定nanoda3329宣言、検査入力hash不変で成功した。証拠は `.cache/wip/monoid_lazy_object_layout_20261107/registered/{receipt,inputs}.json` と tests.log。

RangeSumの既定構築はe()のclass返却とmove/委譲構築を持つため、同stage generatorが意図した理由で拒否する。原本ASTの形は同cacheのRangeSum_record.jsonとprobe.pyに保存した。委譲のcopy/move・一時objectの寿命を省いたfield投影で代用せず、次にこの実行経路を接続する。任意T/M、完全object lifetimeと単一object総費用、公開API復元、原本全137の検証は未完了。現在のfinite instanceのメタデータも両完了flagをfalseに保つ。

### 2026-11-07: RangeSumのscalar委譲構築とfactory/body順序を保持

原本RangeSumの委譲ASTを調べ、e()の返却objectをimplicit move構成子で受ける形と確認した。constructor_delegation.pyを追加し、same-recordのconstructor signature、factory宣言ID/source位置、trivial copy/move/destruction、builtin scalar fieldsを監査する。factoryの値引数と全fieldを1回構築し、factory側の構成子bodyを実行してから全fieldをtargetへ移し、外側bodyを実行する。直接委譲chainも値束縛と本体順序を保持する。独立した2つのfield投影へ置き換えていない。

helper収集で旧constructor処理を重複させないようclass_method_functionsへinclude_constructorsを追加した（既定True、class_copy_layoutのstage helper収集はFalse）。構成子内の途中returnとfactory一時receiverのmember呼出しは別のcall境界が必要なので拒否し、追加処理のあるfactory、nontrivial特殊メンバー、ref引数、runtime effectのある引数、非scalar fieldも未対応のままにした。元の型/API/原本CPPは変更していない。

原本の初回61111はfixtureのscalarFields修飾名、別class初回79687は冗長な旧constructor helper検査で失敗した。これらを成功扱いしない。修正後、実61955は終了0（138.812秒）、template layout7＋既存layout4＋constructor stage methods5の16tests、固定nanoda2815/2648/3300/3329宣言が成功し、manifest対象入力hashは不変だった。原本の全stage形とfield位置のrfl、default/負size/const/copy/一時回収、別classのfactory/body/chain5事例とcaller prefix保持、他fieldゼロ除算の4事例とUBSanの拒否、7つの未対応CPP境界を確認した。

証拠は `.cache/wip/scalar_object_delegation_20261107/registered/{receipt,inputs}.json` とtests.log、tests/lean/original_delegating_object_layout.lean、scalar_delegation_bodies.lean、scalar_delegation_failure.lean。scalar一時領域はstage内で保持しfinishで非export分を回収する。C++の正確な特殊メンバーの時点/identity/総費用や任意T/Mの証明は完了しておらず、full flagsはfalseを維持する。公開API復元と原本全137の検証も未完了で、原本1ファイルの移植完了前なのでpushしていない。

### 2026-11-07: RangeSum既定構築を任意callerからexportまで証明

元CPPのdefault stageの全bodyを対応付け、任意Pのpure pexec本体（work14/need P.length+15）、prepareから通常runFuelへの接続、2fieldだけのfinish/exportを一般証明した。対象はlong long/intの具体化で、callerのmemory内容・長さ・binding数・scopeは任意。frameのwell-formed/rootWritable長/所有scopeとscalar baseの通常の条件を前提にし、未使用cell全件の型範囲は要求しない。

const/mutableの両targetで旧scalar memory/binding/slotと既存scalar読取を保持し、0のlong long/intを各1cell追加して新fieldの型・権限で読める。有効frame、旧frame binding、storage object数・live/work、caller.scopeを保持し、prepare/body/export込みscalar work増分18以下とscalar/storage/outer peak上界を示した。これは抽象counter/cellの境界であり、C++実測値やバイト数の証明ではない。

私的な本体/lift検査ではsimpの自己再展開で最大再帰へ達したため、上限を変えず状態等式をcongrArgで明示合成した。最終私的実54647は固定nanoda3695宣言で終了0。正本fixture original_delegating_constructor_general.leanへ移して既存testに統合し、実99895は終了0（45.767秒）、CPPモデルfresh再生成・Lean・固定nanoda4076宣言・C++/UBSan・manifest対象input hash不変が成功した。

証拠は `.cache/wip/rangesum_constructor_general_20261107/registered/{receipt,inputs}.json` とtests.log。前turnの関連16tests成功後の変更はこのfixtureと該当testの統合であり、今回は対象1testを再検査した。任意T/M、値構築等の一般object caller、全frame観測、C++厳密lifetime/identity/総費用、公開API復元、全137は未完了。原本CPP/公開header未変更、完了flagsを拡大せずpushしない。


2026-11-08: `tree/tree.hpp` のLCAループ上限は利用者が実表の最終行へ修正し、旧範囲外を負例で検査する（fixes.md参照）。元の `build_ancestor()` は頂点数1で `doubling(parent,0)` を呼び、同関数の `assert(kmax>0)` を満たさない。singletonでも同一頂点LCAの早期return自体は表に触れない。この既存の構築境界は今回の上限変更とは分けて未解消とする。
