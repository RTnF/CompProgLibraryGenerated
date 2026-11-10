# experiments/ の検証状況（手書きの台帳）

`experiments/library/cpp`（48 ヘッダー）と `experiments/library3/cpp`（20 ヘッダー、旧版）の各ヘッダーが、`library/` のどの公開部品に対応するか、何が残っているかを記録する。`docs/verification_inventory.json` は原本の hash・依存・宣言と、確認できた範囲の status/evidence を記録する。未確認の宣言を pending のまま残し、部分的な本体証明をクラス全体の完了に引き上げない。この表は公開側との対応と残作業を補足する。公開部品は `python3 tools/check_public.py` で全件検証される（C++ テスト、テンプレートを先に include したテスト、生成モデルの照合、Lean の証明）。

凡例: 済 = 公開部品あり（元の機能を、書き換えた形で証明）。一部 = 公開部品はあるが元の機能の一部。未 = 公開部品なし（理由を書く）。

## experiments/library/cpp

| 元ヘッダー | 状況 | 公開部品／残りの理由 |
| --- | --- | --- |
| algebraic_structure/group.hpp | 済（整数型の具体化セット `long long`・`int`。2026-11-09、浮動小数の `T` は基盤整備後に別項目） | `group`。2026-11-05にhidden friend・元の委譲構築/returnを復元し、LL構成子のfieldモデルと一般定理を追加。統合後の全件検証中。任意Tや完全なobject/lifetime ASTの証明は未完了 |
| algebraic_structure/monoid.hpp | 済（整数型の具体化セット `long long`・`int`。2026-11-09、浮動小数の `T` はC++回帰のみでLeanは基盤整備後） | `monoid`。公開版のhidden friend暗黙変換とcopy-only Tの制約違反は2026-11-06に再現し、正本C++で復元。原本Mul/Max/MinのLL各4モデルを生成し、既存モデル一致および一般callerのop・既定構築と資源上界を独立kernelで確認。公開版の新モデルの全件gateは成功。2026-11-08に原本/公開版のMax/Min浮動小数単位元を修正し、非浮動小数の旧APIを保持。両版のnative回帰とLL生成/証明、公開ASan/UBSan/template-first・fresh bridge・固定nanoda3639/3668宣言が成功（handoff参照）。任意T/完全object/lifetimeと原本全体の検証は未完了（docs/original_template_classes.md、docs/experiments_findings.md） |
| algebraic_structure/monoid_lazy.hpp | 一部 | `monoid_lazy`のflat APIのみ。2026-11-06に原本のstatic idが公開側にないことと、RangeSet composeの値渡しをconst参照へ変えたためコピー効果が異なることをnative比較で確認。原本Add/SumのLL13モデルとSet/SumのLL18モデルは一般callerの結果・停止・元メモリ保持・IR資源上界を登録検査済み。Set/MaxMinのLL18モデルも16モデルの全program/callFuel一致とapply2の一般callerを登録し、Add/MaxMinのcomposeの値渡し一般callerの登録漏れも補った。Set/SumのRangeSetは非投影の2field object構築/copy/権限/scopeを既存評価器へ接続して検査済み。RangeSumのLL委譲構築もfactory返却の全field生成とtrivial move/copyを保持するstageで検査済み。LL/intの既定・値構築とe()は任意callerでの全field exportと旧scalar/vector観測保持を証明。Add/Sum・Set/Sum両方のfriend opもtypedな2object参照からprepare/run/exportまで任意callerへ接続し、両和の型有効性の下で全field結果・入力保持・IR work増分25以下とpeakを証明（固定nanoda4086宣言）。Add/Set×RangeMax/RangeMinの4原本モデルも全field生成と任意入力本体（選択結果・prefix保持・work/need上界）を証明。原本4箇所の浮動小数単位元の不具合を修正し、負値・両無限大と非浮動小数APIのnative回帰を追加（関連検査の最新結果はhandoff参照）。Max/Minの全object呼出しも任意callerのprepare/run/exportへ接続し、旧scalar/vector観測保持とIR work増分47以下・peakを証明（固定nanoda4117宣言ずつ）。trivial record値引数の全fieldコピーを追加し、元Add両系統のcompose/id全object返却を有限ケースで検査（2823宣言ずつ）。変更後の関連15testsも入力不変で成功（handoff参照）。Addの値引数も任意callerへ接続し、両値と和の型有効性だけで旧scalar/vector観測保持・work E+12以下（ObjectRef snapshotでは14以下）とpeakを証明（固定nanoda4072宣言ずつ）。Set composeの条件付き全fieldコピーも元両系統から生成し、bool両組合せ・非ゼロnoop値・極値・alias/const/id・不正入力を固定nanoda2828宣言ずつとnative/UBSanで有限検査。新3testsと既存一般caller/構築/コピーの関連12testsも入力不変で成功。Setも任意入力本体のwork20/need P.length+21と全PS一致、任意callerの旧scalar/vector観測保持・work増分32以下/peakを証明し、両原本freshモデルの固定nanoda4102宣言ずつとAdd/RangeSum回帰が成功。途中更新/異なるrecordのapply、C++厳密identity/lifetime/総費用は未完了。nested型/e/id/applyの公開API復元、任意T、完全object lifetime/総費用、member templateの任意Mの検証は未完了。2026-11-10: 一般化した証明（符号付き範囲外はfault、符号なしは2^widthで折返し）をタイプ4種（32/64bitの符号付き/なし。`long`/`long long`は同じTy）で生成物とrflで全数照合（検査を16本×2組に分割して登録）。`short`/`char`は変換器が未対応（整数拡張の扱いが要る）で、元の任意Tを狭める違反として残る。2026-11-10: `library/algebraic_structure/monoid_lazy.hpp` に元の入れ子API（4 family、`std::` 修飾と `ll` の綴りだけが違う）を追加公開（`tests/monoid_lazy.cpp`、`tests/test_monoid_lazy_original_api.py` で原本とのトークン一致と全driver実行を確認）。平らなAPIは簡便APIとして残す（docs/original_template_classes.md、docs/experiments_findings.md） |
| array/cumulative_sum.hpp | 一部 | `cumulative_sum`（クラス `CumulativeSum<T>` と `CumulativeSum2D<T>`） |
| array/doubling.hpp | 済 | `doubling`, `bit_width_u64`。2026-11-10に「元のソースからの変更」を文書化し、元の関数の逐語コピーとの差分テストを追加 |
| array/element_count.hpp | 一部 | `run_length`（出力は呼び出し側が用意した 2 本の vector） |
| array/search_util.hpp | 一部 | `search_util`（`count`、`lower_bound_index`）、`run_length`（`counts` のソート済み入力の場合） |
| array/sort_util.hpp | 一部 | `sort_util`（`inv_perm`, `compress`, `sort_vector`, `dedup_vector`）。`arg_sort`/`inv_arg_sort` は未（`stable_sort` とラムダ比較） |
| fps/convolution.hpp | 一部 | `inv_gcd`（拡張ユークリッド。結果は呼び出し側の `out` に書く）、`countr_zero`（`countr_zero_constexpr`。末尾の 0 ビット数）。`pow_mod_constexpr(x, n, m)` は公開済みの `safe_mod`（`x` の符号を `[0, m)` に直す）と `pow_mod`（二乗法。`1 <= m <= 2^32`）の組み合わせと同じ関数なので、重複としてまとめた（`m = 1` は `pow_mod` も 0、`n = 0` は 1 を返す。`n` は元の `long long` の非負値を `unsigned long long` に読み替える。2 つの関数の合成が元と一致することは Lean では示していない）。NTT 本体（C++20 の `countr_zero`、多項式の `vector` を返す関数）と `safe_mod`/`pow_mod_constexpr`/`primitive_root_constexpr` の `constexpr` 版は未 |
| geometry/line.hpp, polygon.hpp, vector.hpp | 未 | `double`（浮動小数の誤差の扱いが必要。`docs/trust_policy.md`） |
| graph/bellman_ford.hpp | 一部 | `bellman_ford`（辺の平行配列、親配列と負閉路の印 `-inf` を含む。元の `NEGATIVE_CYCLE` の値でなく `-inf`） |
| graph/dijkstra.hpp | 一部 | `dijkstra`（CSR 配列、`priority_queue` の代わりに線形探索の O(n²+m)。親の配列 `parent` を含む。2026-10-29） |
| graph/edge.hpp, edge_flow.hpp | 対象外（方針） | 利用者の決定（2026-10-12）: 標準入出力（`operator<<`）と ID 管理（静的カウンタ `next_id`）は本質から外れるので Lean の証明は要らない。辺は端点・費用（・容量）の配列で表すグラフアルゴリズムの正しさと計算量を優先する |
| graph/find_cycle.hpp | 一部 | `library/graph/find_cycle.hpp`（CSR・反復 DFS。閉路の有無と、閉路の頂点列を返す仕様、`O(n+m)` の仕事量まで証明。辺の構造体の配列で返す元の形は未。違反一覧: 再帰ラムダを明示的スタックに、返り値の形を頂点列に変更） |
| graph/graph_flow.hpp, graph_list.hpp, graph_matrix.hpp | 一部 | `library/graph/csr_build.hpp`（`graph_list` の辺リストから CSR 配列を作る計数ソート。辺の属性と `vector<vector<>>` の形は未。違反一覧: `ListGraph` クラスを辺リスト→CSR の関数に変更）。`graph_flow`/`graph_matrix` は未（`vector<vector<>>`、`map`、構造体の vector） |
| graph/topological_sort.hpp | 一部 | `topological_sort`（CSR 配列、カーンの方法のキュー版。辞書順最小版は未） |
| graph/lowlink.hpp | 一部 | `library/graph/lowlink.hpp`（CSR 配列・反復 DFS。橋と関節点の同値、ord/par/low/sep の仕様と `O(n+m)` の仕事量まで証明。元の「ソート済みの配列を返す」形、`ListGraph` の形は未。違反一覧: 再帰ラムダを明示的スタックに、返り値の配列を呼び出し側の配列に変更） |
| graph/prim.hpp | 一部 | `library/graph/prim.hpp`（配列版 CSR、`O(n²+m)`、最小全域森の最適性まで証明。`priority_queue` 版と `ListGraph` の形は未。違反一覧: 元の `O((n+m) log n)`・`ListGraph` を CSR 配列・線形探索に変更） |
| graph/warshall_floyd.hpp | 一部 | `floyd_warshall`（非負の辺、親の行列は含めない。平らな形と `vector<vector<T>>` の形） |
| interval/interval.hpp | 済 | `interval`。2026-11-09に元の既定 `operator<=>` と同じ順序の `==`/`!=`/`<`/`>`/`<=`/`>=` を追加（C++17、単一return式）。生成モデル13関数と一般定理 `interval_{eq,ne,lt,gt,le,ge}_correct`、全件gate（実7336秒、独立kernel49269宣言）成功。入出力演算子は方針（2026-10-12）により対象外 |
| interval/interval_union.hpp | 一部 | `interval_union`（組を 2 本の vector に分け、結果は呼び出し側の 2 本の vector に書く。挿入ソート `O(n²)`） |
| modint/dynamic_modint.hpp | 一部 | `dynamic_modint`（演算は関数、法は各値のフィールド） |
| modint/modint.hpp | 一部 | `modint`, `mod61`, `pow_mod` |
| number/ratio.hpp | 一部 | `ratio`（符号と大きさの形、`normalize` のみ） |
| number/square_matrix.hpp | 一部 | `square_matrix`（`mat_mul`・`mat_add_assign`・`mat_sub_assign`・`mat_zero`・`mat_negate`・`mat_identity`・`mat_equal`（`==`、`!=` 相当）・`mat_pow`（冪。作業用 vector を引数に取る）。値を返す演算子は未）。原本の比較・不要な最終二乗は2026-11-02に修正してC++回帰済み。原本クラス全体の変換・Lean証明は未完了 |
| number_theory/enumerate_quotients.hpp | 済 | `enumerate_quotients`。2026-11-10に「元のソースからの変更」を文書化し、元の関数の逐語コピーとの差分テスト（n≤3000全件・n<2^44の乱択）を追加 |
| number_theory/is_prime.hpp | 済 | `library/number_theory/is_prime.hpp`（`mul_mod_u64`・`pow_mod_u64`・`mr_base`・`mr_witness`・`is_prime`）。`__uint128_t` は 2 倍法で置き換えた。素数は常に `true`（無条件）、`true` なら素数は仮説 `MRWitnessSet`（公表済みの計算。未証明）の下で証明 |
| number_theory/factorize.hpp | 未 | 再帰・ラムダ・`sort`（ポラードのロー法）。`is_prime` は上の部品を使える |
| number_theory/floor_sum.hpp | 済 | `floor_sum`, `floor_sum_unsigned`, `safe_mod`。2026-11-10に「元のソースからの変更」を文書化（元ヘッダーと同一の生成モデルを毎回照合） |
| random/xorshift.hpp | 済 | `xorshift` |
| segment_tree/binary_indexed_tree.hpp | 済 | `fenwick_tree`（クラス。構築子 3 種、`sum(r)`、`sum(l, r)`、`add`。`T` はテンプレートのまま、検証した具体化は `long long`） |
| segment_tree/segment_tree.hpp | 一部 | `segtree_sum`（和のみ）、`segment_tree`（クラス `SegmentTree<方針>`。モノイドは `value_type`・静的 `e()`・静的 `apply` を持つ方針として与え、`long long` の最大値 `SegMax<long long>` と最小値 `SegMin<long long>` を検証した。構成子・`set`・`get`・`product`・`product_all`。値ではなくモノイドのオブジェクトを持つ元の形、`search_prod_right`/`left`、他のモノイドの具体化は未） |
| segment_tree/lazy_segment_tree.hpp | 一部 | `lazy_segment_tree`（クラス `LazySegmentTree<方針>`。値と作用を `value_type`/`action_type`・静的 `e`/`id`/`op`/`mapping`/`composition` を持つ方針として与え、`long long` の最大値に chmin を作用させる `LazyChminMax<long long>` を検証した。構成子・`set`・`get`・`product`・`product_all`・`update(idx, f)`・`update(l, r, f)`。値と作用のオブジェクトを持つ元の形、`search_prod_right`/`left`、他の作用の具体化は未） |
| segment_tree/segment_tree_beats*.hpp | 未（途中） | 容量分離した構築/全6操作の本体・Call、実確保からの表現構成、slot/binding置換の実行意味保存、root callerからの構築/export/receiver、更新後BVecs/Scalarsまで型検査済み。複数vectorクラスbundleの生成構成子・全14メソッドは既存モデルとrfl一致し、生成構築→chmin→calc_maxの一般意味も検査済み。const構築viewと一般権限証明を生成し、共通部3037宣言は独立検査成功。構築Call単独の独立検査も成功したが全件独立監査は継続中。child header入力、既存objectのconst参照view/caller接続、copy/move/destructionとexport込み総資源、任意caller AST、Safe導出/任意長操作列/償却、元入力範囲を保つ公開版切替・全件gateは未完了。`_sum`版は別途未検証 |
| set/set.hpp, multiset.hpp | 未 | `std::set`/`map`/`multiset`（STL の契約が未登録） |
| string/char_count.hpp | 一部 | `run_length`（文字列ではなく `long long` の vector） |
| string/rolling_hash.hpp | 一部 | `rolling_hash`（`RollingHash<int>`。構成子と `hash(l, r)`/`hash(a)`。文字列版、`match` 系、`starts_with`/`ends_with` は `std::string`/`npos` が未対応で未） |
| tree/tree.hpp | 一部 | `library/tree/tree_arcs.hpp`（辺リスト版コンストラクタの辺（両方向）の並べ方。辺の費用の写しは `library/tree/tree_arc_costs.hpp`、`Cost = long long`）と `library/tree/tree_find_root.hpp`（根なし親配列版コンストラクタの根の決定）と `library/tree/tree_edges.hpp`（`Tree(root, parent)` の隣接リスト構築のうち、親配列から辺（両方向）を並べる部分。`csr_build` と合成して CSR にする）と `library/tree/tree_height.hpp`（`Tree::height` の最後のループ `h[i] = max(cd0[i], cd1[i])`。直径の両端を求める部分は未）と `library/tree/tree_distance.hpp`（`Tree::distance`。`lca` を引数に取る）と `library/tree/tree_lca_same_depth.hpp`（`Tree::lowest_common_ancestor` の深さを揃えたあとの部分。深さを揃える前半は `tree_ancestor` で別関数に分けている）と `library/tree/tree_ancestor.hpp`（`Tree::ancestor`。ダブリング表を引数に取り、ビット判定を `(i / j) % 2 == 1` に変えている。`i` 個先の祖先を返すことまで証明）と `library/tree/tree_path.hpp`（`Tree::path`。`tree_root` の親配列を `to` から `from` までたどって `out` に書き、長さを返す。元の経路と同じ頂点列）と `library/tree/tree_root.hpp`（`Tree::build_depth` の `parent_`/`depth_`/`cost_depth_` を CSR 配列と手動スタックで求める。`Cost` はテンプレートのまま、検証した具体化は `long long`。到達性・辺と深さと費用の関係・`O(n+m)` の仕事量まで証明。違反一覧: `diameter`・`height` を 1 関数としての形（直径の両端を求める合成）・`height`・`path` の 1 関数としての形（深さ優先探索で復元する元の形。到達不能な `to` に空の経路を返す部分）・`build_ancestor`/`lowest_common_ancestor`/`distance` の 1 関数としての形・`full_tree_dp` の一般の関数オブジェクト `P`（反復版 `library/tree/tree_full_dp.hpp` は `DpHeight<long long>` で追加済み。`ord` は `library/tree/tree_order.hpp` が幅優先の並びとして作る）・辺リスト/親配列のコンストラクタ・`ListGraph`/`Edge` の形・根ごとの `vector<vector<int>>` は未） |
| union_find/disjoint_set_union.hpp, union_find.hpp | 一部 | `union_find`（クラス。構成子 2 種、`unite`、`same`、`root`、`size`、`num_groups`。木の数は `ps` の最後の要素に持つ。`unite`/`same`/`size` は経路圧縮をしない） |

## experiments/library3/cpp（旧版）

`library3` は `library` の旧版で、同じ名前の機能を持つ。`library` 側の公開部品と重複する場合は、命名規則を含めて `library/` を優先する（AGENTS.md 方針）。`Group`, `Monoid`, `CumulativeSum`, `SortUtil`, `BellmanFord`, `Dijkstra`, `GraphL`, `GraphM`, `Lowlink`, `Prim`, `TopologicalSort`, `UnionFind`, `WarshallFloyd`, `ModInt`, `Factorize`, `IsPrime`, `SegmentTree` は上の表の同名ヘッダーと同じ状況。`Mapping`（アフィン写像など）は `library/algebraic_structure/group.hpp` と一部対応するが、下表のAPI/型の差が未解消。`Geometry/Point` は整数の点で象限を `int8_t` に持つ（`int8_t` は生成器の型表に無く、象限による `operator<` の比較も未対応）ため未。

### library3 の対応表（2026-10-12 時点で全ファイルを確認）

| library3 のファイル | 対応 | 状況 |
| --- | --- | --- |
| AlgebraicStructure/Group.hpp | `library/algebraic_structure/group.hpp` | 一部。旧版のpublic field `x/a/b` は公開版へ未復元。原本を変更せずLLの15モデルを生成する共通入口と独立kernel回帰を追加した（[有限具体化](original_template_classes.md)）。任意Tと完全object/lifetimeは未完了。`GroupSum<double>::inv` は旧版の `e().x-x` と公開版の単項minusで正の0の符号が異なる |
| AlgebraicStructure/Mapping.hpp（`Affine<T>`） | `library/algebraic_structure/group.hpp` の `GroupAffine` | 一部。原本のpublic field・ide/compose・値渡しapplyを保持し、LLの12モデルとapplyのLL/intに一般callerの証明・独立kernel回帰を追加した（[有限具体化](original_template_classes.md)）。元APIの公開版への統合、任意T/U、完全object/lifetimeは未完了。`Affine<long long>(2,1).apply(0.5)` は旧版2・公開版1で、doubleはC++回帰のみ |
| AlgebraicStructure/Monoid.hpp | `library/algebraic_structure/monoid.hpp` | 一部。原本MonoidMulのLL具体化4モデルを生成し、既定構築の一般callerと他3モデルの一致を独立kernelで確認。原本hidden friendの暗黙変換は公開C++で復元。公開版の全件gateは成功。任意T・完全object/lifetimeは未完了 |
| Array/CumulativeSum.hpp | `library/array/cumulative_sum.hpp` | 統合済み（`CumulativeSum2D` を含む） |
| Array/SortUtil.hpp | `library/array/sort_util.hpp`, `search_util.hpp` | 統合済み。`arg_sort` 系は未（ラムダ比較の `stable_sort`） |
| Geometry/Point.hpp | なし | 未（`double`、`atan2` 系の偏角ソート） |
| Graph/BellmanFord.hpp | `library/graph/bellman_ford.hpp` | 一部（辺の平行配列。親配列と負閉路の印は `-inf`） |
| Graph/Dijkstra.hpp | `library/graph/dijkstra.hpp` | 一部（CSR、O(n²+m)、親あり） |
| Graph/TopologicalSort.hpp | `library/graph/topological_sort.hpp` | 一部（辞書順最小版なし） |
| Graph/WarshallFloyd.hpp | `library/graph/floyd_warshall.hpp` | 一部（非負の辺、親なし。平らな形と `vector<vector<T>>` の形） |
| Graph/UnionFind.hpp | `library/union_find/union_find.hpp` | 一部（対応先を共有。元`DisjointSet::getNum()`の選択生成・元field条件からの実call/復元・仕事量/3peakと原本C++ UBSanを確認。元constructor/残りAPIと任意caller ASTは未検証。経路圧縮・別カウンタ・元の入力範囲の公開版復元も未完了） |
| Graph/GraphL.hpp, GraphM.hpp, Lowlink.hpp, Prim.hpp | なし | 未（追記 47 の機能待ち） |
| ModInt/ModInt.hpp | `library/modint/modint.hpp` | 一部（`+ - * /`、入出力なし） |
| NumberTheory/Factorize.hpp, IsPrime.hpp | なし | 未（`__uint128_t`、ミラー–ラビン） |
| SegmentTree/SegmentTree.hpp | `library/segment_tree/segtree_sum.hpp` | 一部（和のみ。任意のモノイドは構造体の要素が要る） |
| Template/*（MMTemplate.cpp, Template.cpp, SmallTemplate.hpp） | 対象外 | テンプレート（マクロ・`using`）で、ライブラリではない。`tests/` はこの中の `small_template.hpp` を先に include する |
| Verify/*.test.cpp, VerifyIgnored/, VerifyManually/ | 対象外 | 外部のジャッジの問題を使う確認用で、テストはコンテストサイトと通信しない規則（AGENTS.md）により公開側のテストには使わない。対応する手元のテストは `tests/*.cpp` |

## 共通の変換器について

公開部品はすべて共通の変換器 `verifier/nested_ir.py`（`lower_source`/`emit_lean`）で C++ から Lean のモデルを生成する。部品ごとの TOML の `bridge = "verifier/nested_bridge.py"` は、その共通変換器へ入る入口の名前であり、特定の部品に特化していない（`merge_sort` と `associative_array` の専用ブリッジは削除した）。


## 規則違反の一覧（AGENTS.md の「クラスとしてまとめる」「元の汎用性を保つ」）

次の部品は現在、規則に違反している。解消するまでこの表を残し、直したら行を消す。解消済み: `monoid_lazy`（型パラメータ）、`fenwick_tree`（旧 `fenwick*`）、`union_find`（旧 `uf_*` のファイル分割を解消。機能・入力範囲の違反は下記に残る）、`cumulative_sum`（旧 `prefix_sums` を統合し `CumulativeSum2D` を持つ）、`group`（旧 `affine` を統合し `GroupAffine` を持つ）、`monoid`、`interval`、`vector_sum`/`vector_min`/`vector_max`/`vector_fill`/`mat_mul`/`floyd_warshall`/`compress`/`segtree_sum`（型パラメータ）、`extrema`（型パラメータを元のまま残し、`long long` の具体化を検証する）。

### 1. 同じクラスなのにファイルを分けている、またはクラスにしていない



| 元のクラス | 現在の公開部品 | 目標 |
| --- | --- | --- |
| `ModInt` / `DynamicModInt` 周辺 | `modint`, `mod61`, `pow_mod`, `dynamic_modint` | 元のヘッダーごとに 1 つ（`mod61`・`mul61` は `string/rolling_hash.hpp` の `rh_in`、`pow_mod` の元を確認する） |
| `RollingHash` | `rolling_hash`（`SimpleRollingHash` 相当。文字列版・`match` 系は未） | `string`、`npos`、`vector<ull> hash_sum_[16]` の対応後に元の形へ広げる |
| `SortUtil` 周辺 | `sort_util`（`inv_perm`・`compress`・`sort_vector`・`dedup_vector` を統合済み）、`search_util`（`count`・`lower_bound_index` を統合済み） | 元のヘッダー（`array/sort_util.hpp`、`search_util.hpp`、`element_count.hpp`）ごとに 1 つ |

### 2. 元の汎用性を狭めている変更

- 旧`library3`の`Group`/`Mapping`のAPI・意味を縮小している: public field `x/a/b`、`ide/compose`、`template<class U> U apply(U)` の値渡しを現行公開版は保持していない。逆元の演算の定義も異なり、doubleの0の符号が変わる。上の旧版対応表と `docs/experiments_findings.md` に実比較を記録した。元APIを持つクラスとして全機能を検証するまで未解消。

- 型 `T` を `long long` に固定: なし（`run_length`・`bellman_ford`・`dijkstra` も 2026-10-12 にテンプレート化済み。`monoid_lazy` もテンプレート化済み。入れ子の構造体の平らな形は下の「構造を変えている」に残る）。
- 機能を落としている、または構造を変えている: `tree_root`/`tree_ancestor`（`Tree` の高さ・直径・全方位木 DP とコンストラクタ類を含めず、隣接リストを CSR、`stack<tuple>` を呼び出し側の `stk` に変えている。解消は残りの `Tree` の機能を同じ枠組みで足す）、`interval_union`（`pair` の vector を 2 本の vector に分け、結果を呼び出し側の vector に書く。並べ替えは `std::sort` でなく挿入ソート）、`union_find`（`unite`/`same`/`size` が経路圧縮をしない。木の数を `ps` の末尾に持つ。入力assertは復元済み）、`interval`（`<=>` と入出力演算子なし）、`bellman_ford`（負閉路の印は元の `NEGATIVE_CYCLE` 値でなく `-inf`。負閉路から届く頂点が必ず `-inf` になることは未証明でテストのみ）、`dijkstra`（`priority_queue` でなく O(n²)）、`topological_sort`（辞書順最小版なし）、`floyd_warshall`（負の辺と親なし）、`dynamic_modint`（静的な法を各値のフィールドに変更）、`ratio`（符号付き `T n, d` でなく符号を分けた形、演算子なし）、`modint`（二項演算子は `+ - * /`。入出力、変換コンストラクタなし）、`mat_mul`（積のみ）、`segtree_sum`（和のみ）、`monoid_lazy`（平らなAPIは簡便APIとして残す。元の入れ子APIは公開済みで、`T` は変換器の整数4種のみ検証、`short`/`char`/浮動小数は未）。
- 機能を落としている（`lazy_segment_tree`）: 元の `LazySegmentTree<M, F>` は任意のモノイド `M` と作用 `F` のオブジェクトの木だが、公開版は値と作用の vector（`vector<value_type>`、`vector<action_type>`）の木で、方針 `P` の静的関数 `e`/`id`/`op`/`mapping`/`composition` で与える（1 つの整数だけの値と作用に限る）。既定構成子と `int` を取る構成子、`search_prod_right`/`search_prod_left`（述語を取る二分探索）、`assert` は含めない。検証した具体化は `long long` の最大値と chmin のみ。区間操作は `h_node <= 29`（`n <= 2^29`）に限る。解消は、構造体のオブジェクトのベクトルを扱う変換器の拡張、述語の扱い、区間加算などの具体化を足すこと。
- 機能を落としている（`segment_tree`）: 元の `SegmentTree<M>` は任意のモノイド `M` のオブジェクトの木だが、公開版は値（`vector<value_type>`）の木で、モノイドは `value_type`・静的 `e()`・静的 `apply` を持つ方針として与える（1 つの値だけのモノイドに限る）。`search_prod_right`/`search_prod_left`（述語を取る二分探索）と `assert` は含めない。検証した具体化は `long long` の最大値と最小値のみ。解消は、構造体のオブジェクトのベクトルを扱う変換器の拡張、述語 `F` の扱い、`MonoidMin/Mul` などの具体化を足すこと。
- 機能を落としている（`square_matrix`）: 元の `SquareMatrix<T, N>`（非型テンプレート引数 `N`、`operator*`/`+`/`-`/`==`、`pow`）を、`vector` と `int n` を取る関数 8 個（`mat_mul`・`mat_add_assign`・`mat_sub_assign`・`mat_zero`・`mat_negate`・`mat_identity`・`mat_equal`・`mat_pow`）にしている。値を返す演算子（`+`/`-`/`*`）、クラスとしての形は未（`!=` は `!mat_equal`、`pow` は `mat_pow` が相当し、`pow` の指数は非負の `unsigned long long` に限る）。解消はC配列・非型テンプレート・行参照・初期化状態の変換器対応を足し、公開mat配列と元の全クラスAPI・型traitを維持してクラス全体を検証すること。
- 入力範囲を狭めている: `union_find` の番兵表現は `n < 2^31 - 1` に制限している。元の別カウンタを復元して解消する。入力assertは復元済みで、正常終了定理に加え、共通の純粋拒否補題と生成モデル/C++の失敗経路テストを持つ。構成子の確保前の検査とは主張しない（元と同じ本体assert）。

- 入力範囲を狭めている（`segment_tree_beats`）: 元の `4*n` から公開版の `8*n+8` へ配列を増やした一方、長さと子添字の計算を32-bit intのままにした。例えばn=2^28では元の4*n/2*n0と全木添字がintに収まるが、新しい8*n+8は収まらない。公開の8*n+8<2^31という前提だけで解決済みとはしない。未使用節点・葉の子への無条件アクセスを含む反復化が理由であり、サイズ/子添字計算の型と安全性証明または制御フローを改善して元の範囲を復元する。巨大入力の実確保はしていない。

### 3. 変換器の拡張（実装済み）と残り

実装済み（`verifier/ast_stream.py`、`class_lowering.py`、`class_split.py`、`vector_stl.py`、`clang_ast.py`）:

- `vector` をフィールドに持つクラス: フィールドを引数にしたメソッド。書き換えないスカラーのフィールドは値渡し。構成子は、スカラーのフィールドをメンバー初期化子の値を持つ局所変数にし、`vector` のフィールドは標準の構築子の契約に任せ、本体の文を関数にする。同名メソッドは引数の個数で区別する。
- クラステンプレート: 明示的な具体化（`template class X<long long>;`）を検証する。関数テンプレートも明示的な具体化を普通の関数として検証し、`op`のような元のhidden friendも、型だけのwitnessで本文を具体化して検証できる。namespaceテンプレートと併存する場合はモデル名の衝突を区別する。
- 静的メンバー関数、`std::numeric_limits<整数型>::min()/max()/lowest()`、`const` へ修飾変換された `this` でのメソッド呼び出し。

残り:

1. 可変scalar fieldは共通NProgram/Context経路で参照として生成・実行でき、UF候補の全5method、正常状態・資源・両constructorへの接続を持つ。公開UFは旧経路のままであり、別カウンタ/全methodの経路圧縮/元入力範囲への切替が残る。これは現行共通変換器が参照fieldを扱えないという意味ではない。
2. 元の入れ子class・メンバー関数template（`monoid_lazy` の元の形）、入れ子vectorを使う全旧APIへの適用、`std::string`、`std::set`/`map`、再帰、`double` の扱い。入れ子vectorの一部操作は共通Nested経路で対応済みだが、元API全体の検証とは区別する。


## 2026-10-15: GroupAffine::applyの参照APIを復元

公開group.hppのapplyは元のconst T&から値渡しへ変わっていた。コピーが観測できるTで挙動が変わるため、元の署名へ戻した。共通生成モデルとaffine_apply_correctは3つの読み取り専用参照へ更新し、別名を含む状態保存/結果/定数費用を扱う。C++では署名とコピー回数も確認する。公開部品数は増えておらず、他の未完了API/汎用性違反/各アルゴリズムの残作業は引き続き対象である。


UnionFindの元API/別カウンタ/全メソッド経路圧縮を保つ候補を `experiments/verification/data_structure/union_find.hpp` に追加した。詳細は [union_find_experiment.md](union_find_experiment.md)。元実装との全配列・カウンタ一致と共通生成NProgramの有限照合、経路圧縮の一般仕様/再帰との一致を確認する。候補root/same/size/unite/num_groupsは混合fieldのprepareからcallFuel/finishまで一般証明し、sizeの実成分要素数、uniteの2圧縮/union-by-size結合/同根保存/別counter1cell更新と最終Valid、num_groupsの根数と各要素の一意な成分代表へ接続した。構成子の確保・field初期化の処理は一般callerのprepareから全入力の実行と初期Validまで接続した。callerへのfield移行と一時領域解放を含む構成子専用constructFuelも一般証明した。prepareから構成子stageまでの正確なframe（旧buffer/capacity/limit/epoch、新bufferと権限の追加）は一般証明した。旧objectのscope条件下でfinish後までの全既存buffer/tag/epochと新buffer metadataの保存も一般証明した。任意の正常な取得済み参照の読取り保存と、旧ownerのgrant/read結果同値も一般証明した。構成子からVOKWF/初期Validと保存_nを読むnum_groupsへの接続も一般証明した。残るroot/same/size/uniteと連続呼出しを含む全クラスの前提接続、資源上界、対数高さ/償却解析、元API全体の監査は未完了であり、公開版の違反はまだ解消済みとしない。

UnionFindのroot後もVOKWF/型付きbuffer/全scalarCellを保持し、圧縮後stateへ2回目のrootを渡す一般証明を追加した。size/same/unite後の同様の再構成と全クラスの任意長連続呼出し・計算量等は未完了。

UnionFindのsame/size/unite/num_groups終了後もVOKWF/型付きbufferを返す一般証明を追加した。same/size/getterは全scalarCell保存、uniteはcounterと同cell別名の更新・別cell保持を扱う。全クラスの任意長呼出し列と計算量・元API等の残る義務は未完了。

UnionFindの両構成子から全5メソッドのクラス不変条件を成立・保存し、任意の有限な有効メソッド列が実生成プログラムで終了して配列長と不変条件を保つ一般証明を追加した。元callerのscalar/vector別名や資源・copy/move等の残る義務があり、公開版の違反と全experiments目標は未解消。

UnionFindの到達状態について、初期/圧縮/union-by-sizeで2^rank≤成分サイズと根rank0を保存し、任意有限メソッド列でrank≤log2(n)を導く証明を追加した。root単体のwork増分上界も導いた。償却解析と全メソッド列・構成子を含む時間/追加領域、copy/move等は未完了。

UnionFindの全5methodについてwork増分≤182log2(n)+405を導き、任意の有限な有効列m操作で開始work+m*(182log2(n)+405)以下を一般証明した。構成子終了後を基準とする実行モデル上界であり、構成子・追加領域・償却解析・copy/move等は未完了。

UnionFindの実構成子を含むwork上界を追加した。サイズ指定はn+引数nodes+30、その後m操作を含めn+引数nodes+30+m*(182log2(n)+405)、defaultは12+m*405の増分上界。追加領域・償却解析・copy/move等と全experiments目標は未完了。


- 構成子の追加領域に向け、`CppConstructorPeak`でscalar/fill/空確保の実step peakと、k scalar fieldsの復元live量+2k・finishの正確なpeak式を追加。過去peak、caller baseline、vector capacityを保持する。全stage/全method列のspace上界は未完了であり、work証明からspaceや償却を推定しない。


- `CppScalarComponents`と`UfConstructionPeak`で実生成構成子bodyのscalar単独/全体peakを合成。sizedはscalar定数7/全体10、defaultは5/6、memory/bindings各+2、base保存、正確なframeを証明。配列capacityを各scalar stepへ重複加算しない。prepare前callerからfinishまで、全method列のspace上界とcopy/move等は未完了。


- `UfConstructorSpace`で両構成子の引数評価→stage→移行/退役→field復元の領域を合成。実construct成功・Strong・workに加え、scalar live増分4、nested live増分n+1/default1、caller過去peakと予約束縛/式nodes/新capacityを含むpeak上界を証明。method列全体のspace、償却α、copy/move等と他分野の検証は未完了。


- 全NExpr/Container評価のstate/root権限保存と、実Frame.write/NStmt.writeで全bufferのowner/capacity/limit/epoch/長さ保存を追加。入れ子vectorと既存readonly参照の更新値・stale参照拒否を検査。UF全bodyの制御/scope/finishへの接続、操作列space・copy/move等は未完了。


- 全式評価のscope保存、scalar/write primitiveのheader/root権限/scope/返却種別保存、旧ownerが対象scopeにない場合の実retire/leave保存を追加。UF全5methodの生成bodyが対象fragmentであることを確認。制御構造runFuelへの合成と全method/列の効果・space等は未完了。


- `CppNoResizeRun`で制御全体、`CppCallFrame`で実prepare/body/finish/callのmetadata保存を接続。UF全5methodと任意の終了実列へ適用し、Strong/workが構成する任意有限有効列にも接続。構成子前からの総workと最終常駐領域増分（scalar4/nested n+1または1）、全buffer Signature、bindings/slots/scope/baseline/memory長とgrant検証結果保存を証明。一様peak・任意read/headerOwner/resolve・他owner値・償却α・copy/move等と残り全分野は未完了。


- `CppReferenceHeaders`でCallEffects下の既存read成功保存、両側wellFormed下で任意Referenceの成功/失敗同値を証明。UF全5method/実有限列へ接続し、Strong/workが構成する任意有限有効列へも接続。値の同一性、構成子で新登録されるgrantへの失敗同値、headerOwner/resolve、他owner値、一様peak/償却α/copy/move等は別義務。


- `CppHeaderAliases`と`UfReceiverAliases`で両側wellFormed下のnested buffer全lookup、headerOwner完全一致、resolveの成功/拒否とbinding/Signature保存を証明し、UF全5method・任意有限有効列のStrong/workへ接続。整数値の同一性、他owner値、一様peak、償却α、copy/move等と残り全分野は未完了。


- `CppExprPrefix`で全成功式のslots/binding prefixとrelease後frame完全復元、`CppFixedWrite`でlocal 0固定rootの実writeが他ownerの全buffer lookupを保存することを証明。scalar primitiveもTarget/frameを保存。binding index≠owner、一時nested child binding、readonly拒否を回帰検査。制御/call/UF有限履歴への値保存、一様peak、償却α、copy/moveと残り全分野は未完了。


- `CppFixedScope/CppFixedRun`でfresh scope終了の全lookup保存、固定local0書込みの制御全体（sequence/branch/while/scope/break）のTarget/binding/slots/他owner値保存を証明。UF全5生成bodyの分類とnested readを含む実loop/早期return/break/zero loopを回帰検査。成功runFuelの効果であり、終了の構成とcall/UF有限履歴への接続は別義務。一様peak、償却α、copy/moveと残り全分野も未完了。


- `CppPrepareTarget/CppFixedCall/UfReceiverValues`で先頭vector引数の実prepareからcallee local0 ownerを導き、実scalar finishと固定root制御効果を全UF method・任意有限履歴へ接続。他owner全buffer lookupを保存し、両側wellFormed下の他owner Reference.readの値/拒否Option全体も保存。Strong/workが構成する終了結果へ接続済み。nested read値引数、binding4≠owner2、UF混在12操作を検査。一様peak/償却α/copy/moveと残り全分野は未完了。


- `CppCallUnique`でfuel非依存の実call結果一意性、`VecWriteScalarPeak`で過去outerピークを混ぜない一般vector callのscalarピーク境界を証明。`UfRootScalarPeak`で実root bodyの終了構成と任意fuel成功へ接続。outer履歴1億の回帰検査でscalar値の不変と境界を確認。他4method、prepare上界と有限列の一様ピーク合成、tight storage/outer peak、償却α/copy/moveと残り全分野は未完了。


- `UfSame/Size/Unite/CounterScalarPeak`で残り4methodのscalar専用境界を実prepare/bodyへ適用し、任意fuel成功へ接続。`UfReceiverScalarPeak`で全5OperationをRepresents/有効入力とStrong/workが構成する終了結果へ統合。outer履歴1億の全5操作でscalar境界とmemory/storage結果を検査。init.scalarPeakのmethod prepare上界、有限列の一様scalar/outer/storage peak、償却α/copy/moveと残り全分野は未完了。


- `UfMethodPreparePeak`で1/2/3値式の実method prepareのscalar component上界を証明。`UfUniformScalarPeak`で全5methodと任意有限有効列の終了/Strong/workへ接続し、scalar peak≤max 開始scalarPeak (開始liveS+開始vector binding数+112)を証明。操作回数に依存せず、任意の成功fuel列にも結果一意性で適用。36操作と空列、outer履歴1億を回帰検査。tight storage/outer peak、償却α/copy/moveと残り全分野は未完了。


- `CppWritePeak/CppStoragePeak/CppCallStoragePeak/UfUniformStoragePeak`でwrite/fresh退役のstorageピーク等式を実制御/call/UF有限履歴へ接続。storage peak≤max 開始storagePeak (開始liveSpace+1-開始baseSpace)を操作回数非依存に証明。同じ終了/Strong/work/metadata結果で既存一様scalar境界も保持。nested control、base>liveでの飽和減算、混在24操作と空列を検査。outer履歴を含む総合、一様peakの構成子接続、償却α/copy/moveと残り全分野は未完了。


- `CppPeakComponents/CppEvalPeak/CppStmtPeak`でscalar/storageピーク単調性と履歴を分離したouter上界の関係Growsを、全成功Container/NExprとscalar/write primitiveへ証明。17種の成功式、nested一時binding解放、短絡、過去outerピーク1億・scalarピーク1億を検査。制御/scope/call/UF有限履歴へのouter接続、構成子からの総合、償却α/copy/moveと残り全分野は未完了。


- `CppPeakScope/CppPeakRun/CppPreparePeak/CppCallPeak/UfUniformPeak`でouter履歴を分離したGrowsを全NoResize制御、全対応引数型の実prepare/scalar call、UF全5method/有限履歴へ接続。Strong/workが構成する同じoutにscalar/storage境界と操作回数非依存のouter全体上界を証明。nested複数vector引数、scope/loop/return/break、履歴1億、混在24操作を検査。構成子前からの総合、償却α/copy/moveと残り全分野は未完了。


- `UfConstructorSpace`の構成子証明をcomponent版と既存statement wrapperへ統合し重複を解消。`UfConstructedPeak`で両構成子前から任意有限有効列までの終了/Strong/work/metadata・常駐領域とscalar/storage/outerの一様境界を接続。scalarはn/m非依存、storageは最終常駐領域+1、scalarは最終liveS+開始vector bindings+引数nodes+113で各開始peakとのmaxを取るモデル境界。n=0/1/17、default、alias/baseline/履歴、混在列と抽象INT_MAXを検査。償却α/copy/move/元汎用APIと残り全分野は未完了。


### UF特殊メンバー基礎（2026-10-18）

CppVectorCopyの新buffer/flatストアの一般コピー証明と、元・候補の全4暗黙特殊メンバー有限照合を追加。クラス全体のcopy/move生成・意味対応、償却α、公開版の既存違反は未解消。詳細はvector_copy_contract.md。全experiments検証は未完了。


### scalar vectorコピーのFrame基盤（2026-10-18）

root/childから新rootへのコピーとFrame延長・旧参照保存、新参照の取得と書込み分離、nested headerを重ねない領域境界を証明した。copy/move全クラス生成、UF Strongへの接続、償却αと公開版の違反は未完了。


### UFコピーの状態不変条件（2026-10-18）

新vector+scalar2セルの状態モデルで、コピー直後の元・先Strong、任意有効列のコピー先終了/Strongとwork境界を証明した。暗黙C++ AST生成・意味対応、操作列後の元receiver保持、copy全体のscalar/outer境界、代入/move/償却αと公開版違反は未完了。詳細はunion_find_copy.md。


### UFコピー先操作列後の元receiver/alias（2026-10-18）

copyReceiver状態モデルで、任意有効操作列の終了後の元・先Strong、全旧成功scalarCell/vector参照保存とworkを一般証明した。暗黙C++ copy ASTの生成・意味保存、copy全体のscalar/outer境界、代入/move/償却αと公開版違反は未完了。


### UFコピー前から操作列までの領域（2026-10-18）

copyReceiver状態モデルのコピー前から任意有効列までの全3peak/常駐領域を、両Strong・参照保存・workと同じoutへ接続した。暗黙C++ copy ASTの生成・意味対応、代入/move/償却αと公開版違反・他分野は未完了。


### 暗黙クラスcopy ASTの宣言監査（2026-10-18）

原UFと一般形のvector+scalar classを、元ヘッダー変更・アクセス制御無効化なしで実体化し、source/field/標準copy宣言identityと順序を監査する経路を追加。coverageはmember_identity_only。共通Lean生成・UF状態モデルとの意味保存、代入/move/償却αと公開版違反・他分野は未完了。


### 共通class copy評価器（2026-10-18）

CppClassCopyの宣言順profile評価器とUfClassCopyBridgeの任意state/Layout・失敗を含むwhole state同値を追加。const元とコピー先権限を分離し、n/countとvector長不一致も保持する。監査計画から直接評価器のprofile/copyを生成しUF bridgeへ接続。fieldとslotの対応/call siteは未完了で、暗黙copyのC++検証完了や公開昇格とは扱わない。代入/move/償却α、公開版違反と他分野も引き続き未完了。


旧UnionFindのquoted small_template.hpp→bits/stdc++.hのpristine include profileを固定Clangの同時JSON reportから再現。原sourceの暗黙copy監査とLean生成をUF bridgeへ接続した。これは当該copy profileの進捗で、copy call site/move/代入/クラス全検証の完了ではない。


### コピー元式と一時参照（2026-10-18）

CppFrameCopyの純定義を低層coreへ分離し、コピー元の式を評価してrow temporaryをreleaseした後にfresh owner/bindingを追加するCppCopyStatementモデルと一般補題を追加した。実終了/Extends/旧成功read・scalarCell保持と、source評価を含むnextからの正確なwork/storage資源を扱う。flat scalar vectorの通常NStmt新caseとAST生成を追加。クラスfield-slot・const instance viewとクラス全体のscope退去統合は未完了。クラスcopy全体や全experimentsの完了とはしない。

### 同一TUのclass field-slotと構成子export（2026-10-18）

暗黙copyの宣言監査と明示構成子stageを同じTUのFieldDecl ID/型/順序/permissionで結び付け、実slotからconstructFuelのexport引数を生成する経路を追加。UFの既存入口との全状態同値と、const/mutable/bool・shadowing local・初期化補助呼出しをLean/C++ UBSanで確認する。コピー先const profileはmutableを区別する。クラスcopy call site、一般の構築先const view、assignment/move、UF償却αと公開版違反・他分野は未完了。

### member copyの通常命令列（2026-10-19）

監査済みprofileからvector copyと宣言順scalar初期化の通常命令列を生成するバックエンドを追加。初期source検証からの正常終了、旧成功参照保持、結果配置、workと3peakの一般補題を型検査した。直接評価器との資源差を明示し、不正なfuture source slotを拒否する。class caller ASTと全method呼出し境界の統合、assignment/move、UF償却α、公開版違反と他分野は未完了。


### メソッド呼出し境界とcaller制御（2026-10-19）

既存NProgramのprepare/finishを通してscalar/bool結果をcallerのreadonly localへ保存するadapterと、列/scope/分岐/ループを組み合わせる制御層を追加。全5 UFメソッドの任意の許された有限列について、実終了、receiver不変条件、サイズ・回答数・追加slot数の保持を一般化した。実C++混在列とのUBSan照合とearly return/一時寿命を検査する。新caller AST frontend、一般const構築view、class return、copy/move代入/move、全caller資源、UF償却α、公開版違反と他分野は未完了。全件検査の確定結果はhandoff参照。


### 同一TUのclass reference caller（2026-10-19）

元record/標準roots/未展開free callerを同じdumpから収集し、FieldDecl/MethodDecl identity・型・const/mutableからCallerProgramと外部receiver呼出しを生成する経路を追加。入口scalar fieldsも参照として保持し、各methodの値引数は呼出し時に読む。UF全5methodは既存programとの定義上の一致、混在CPP callerはnative UBSanと照合する。const/mutableの別名receiver、同一arity overload、for incrementのtemporary scopeも検査する。class localの構築/copy、call condition/複合式、class return/assignment/move、一般const構築view、全caller資源と従来の未完了事項は残る。全experiments検証完了ではない。


### caller内のimplicit class copy（2026-10-19）

同じrecordの監査済みimplicit constructor signatureと元objectのDeclRef identityからlocal copyを生成し、vector+scalar fieldsを宣言順に追加する経路を追加。sourceの直前の変更、const/mutable、local同名shadow、block退去と旧参照保持を生成Lean/native UBSanで照合する。通常local構築を持つ未対応callerは黙って除外せず明示拒否する。class localの通常構築、move/assignment、class return、一般const構築view、全caller資源、UF償却α・公開版違反・他分野は残る。最新の確定all結果はhandoff参照。


### constructorのtyped export views（2026-10-20）

構築中の初期化権限とexport後のconst/mutableを分け、fresh field bindingsのviewだけを制限するモデルと一般補題を追加。scalar cell/slot/address、物理frame state/root flags、work/3peak、元callerの既存binding参照を通常exportとの関係で保つ。同じclass metadataからexportViewFuelを生成し、mutable int/bool、declared const vector/scalar、型/件数/権限拒否を生成Lean/native UBSanで検査する。通常local構築のcaller AST接続、move/assignment、class return、全caller資源と従来未完了事項は残る。全experiments検証の達成ではない。


### 通常class local構築とvoid methodのcaller接続（2026-10-20）

同じTUの元constructor ID/signature・FieldDecl・実slotを使い、default/sized/const localをconstructor-view helperへ接続。entry receiverなし/未使用の構築も黙って省かない。constructor内部のthis-methodは初期化済みfieldsへ対応し、void methodは独立call boundaryで更新を保って続行する。UF全5method、copy、scope/break、const/mutable int/bool、参照引数、overloadを生成Lean/native UBSanで照合する。implicit default、constructor内部calleeのearly return、bare void return、vector/class return、move/assignment、複合call、全caller資源と従来の未完了事項は残る。


### bare void returnとvoid caller（2026-10-20）

NStmt末尾のretUnitとunit/some unitのfinishを追加し、void/constructorのReturnStmt子なしを型に応じて生成する。void free callerはunit result kindで実行し、値なしreturnをscalarへ偽装しない。local退去と元vector/scalar aliasの更新、constructor fields exportを生成Lean/native UBSanで照合する。公開1778theorem statementsは維持、依存閉包19変更/retUnit1追加は旧scratchとの実比較と意味レビューを行う。constructor内callee early return、move/assignment、vector/class return、複合call、全caller資源など従来の未完了事項は残る。


### 構築子・外部methodの既定引数（2026-10-20）

同じTUの元parameter initializerを使い、構築子と外部receiver methodの省略引数を既存の純scalar/reference引数規則へ接続する。展開された既定式のnode identity/構造、整数変換方針、明示指定時の非評価を検査し、省略時の副作用は拒否する。内部this-callのinliner、任意の副作用/global object、implicit default/delegation、move/assignment、class/vector return、全caller資源、UF償却αと既存の公開版違反・他分野は未完了。全件検査の確定結果はhandoffを参照する。


### UnionFindの履歴rank（2026-10-20）

元のsize値から求める根のlog2 rankと、親方向への厳密増加を別のghost不変条件として保持する証明を追加。経路圧縮、サイズによるswap付き結合、生成済み全5method、両構築子からの任意の有効な有限操作列へ接続する。実state/数学的不変条件や実終了の既存条件を維持する。これは償却αの証明に向けた不変条件であり、rank分布・potential・実仕事量の償却対応は未証明。詳細はdocs/union_find_history.md、確定した検査結果はhandoffを参照する。公開版違反と他分野を含む全experiments目標は未達。


### UnionFindの成分内rank分布（2026-10-20）

実際のsize結合履歴から、成分size s・閾値t=2^k・rank≥kの個数cについて、s<tならc=0、t≤sならc*t+t≤2*sを保つ証明を追加。圧縮・サイズswap付き結合・生成全5method・両構築子からの任意の有効な有限列へ接続する。点ごとのHistoryのみでは不足する反例も検査する。全成分の集約、level/index potential、実走査/書込み/仕事量の償却対応は未完了。詳細はdocs/union_find_population.md、確定検査結果はhandoff参照。全旧ライブラリの検証完了ではない。


### UnionFindの全体のrank分布（2026-10-20）

Valid forestの全成分がrange nの重複なしの分割になること、成分サイズ/filtered countの和を証明し、rank≥kの全node数cに対するc*2^k≤2*nを導く。生成全5method・両構築子からの任意の有効な有限列へ接続し、既存Represents/HistoryWithPopulationを維持する。全体上界をconstructorの入力前提に置かない。level/index potential・実走査/書込み/仕事量・償却αは未完了。詳細はdocs/union_find_global_population.md、確定検査結果はhandoff参照。他分野と公開版違反を含む全experiments目標は未達。


### UnionFindのnode potential基礎（2026-10-20）

実size結合でのrank増加高々1、標準2引数Ackermann再帰と固定引数/対角逆関数の比較、非根nodeのlevel/indexとpotentialを追加。各圧縮node（rank0含む）の非増加を実Compressed関係へ接続し、実生成root callの終了とRepresentsを保持する。全forest potential・結合時の増加・探索例外node数・実2-pass仕事量・列全体の償却時間は未完了。詳細はdocs/union_find_potential.md、確定検査結果はhandoff参照。公開版違反、caller資源、他分野を含む全experiments目標は未達。


### UnionFindの全forest potential（2026-10-20）

根alpha*rank・非根nodePotentialの全node和を定義し、初期値0、圧縮の非増加、実size結合の増加高々alpha(n)を証明。全5method・任意の有効な有限列・両構築子に接続し、potential増加をunite呼出し数*alpha(n)で抑える。これは仕事量ではなくpotentialの上界。深さ3の8-node木のモデル/native UBSan、他root/参照保持、2-node結合のpotential増加例を検査する。例外node数・実2-pass仕事量・償却時間は未証明。詳細はdocs/union_find_forest_potential.md、確定結果はhandoff参照。公開版違反、caller資源、他分野の義務は未完了。

### UnionFind rootの実仕事量の償却上界（2026-10-20）

親リンク列の一意性/正確なdepthから生成rootの仕事量を91*経路長+142で抑え、level/indexの経路課金と全forestのpotentialへ結び付けた。root_amortizedは実終了・Represents・Historyを保ち、仕事量+91*更新後potential≤旧仕事量+91*旧potential+324*(alpha(n)+1)を示す。rank0/根/小さいnも含む。全5method・任意操作列の仕事量、caller資源、公開版違反、他分野は未完了。詳細はdocs/union_find_path_amortized.md、確定検査結果はhandoffを参照する。

### UnionFind全5methodと操作列の実仕事量の償却上界（2026-10-20）

生成済みsame/uniteの2回の探索に、それぞれ圧縮前後のValidから導いた正確なdepthを適用した。全5methodを統一し、任意の有効なm操作についてWout+91*Φout≤Win+91*Φin+769*m*(alpha(n)+1)、両構築子を含めたO(n+m*(alpha(n)+1))の仕事量上界を証明。サイズswap/同根/実count更新、実結果のRepresents、履歴rankを維持する。深さ3から長さ1になる2回探索、全5method、n=0/1をモデル/native UBSanで検査。候補C++/旧定理は変更しない。任意callerへの全資源接続、copy/move等、公開版違反、他分野は残るため全experiments目標は未達。詳細はdocs/union_find_method_amortized.md、確定検査結果はhandoffを参照する。

### vectorコピー代入の寿命基盤（2026-10-20）

UF等の暗黙コピー代入に向け、自己代入・容量再利用・再確保のflat storeモデルを追加。生き残る先頭参照を保ち、縮小で破棄した末尾参照が再拡張で復活しない要素寿命世代を証明した。元/他bufferの参照保存と資源式を接続し、固定GCCのint/long longをASan/UBSanで照合。既存Frame/NState、暗黙class operator=のAST生成/意味対応、scalar代入とmoveへの接続は残る。全experiments目標は未達。詳細はdocs/vector_copy_assignment.md。

### コピー代入のFrame接続（2026-10-20）

TrackedFrame/refで要素寿命を保持し、既存のresolve/grant/object/commitにコピー代入を接続。実終了/wellFormed・型/権限・元/他参照保存、成功した任意コピー代入列での無効参照の非復活、無効参照からの書込み拒否、nested liveSpace/baselineによる資源式を証明。親reserve後のimmutable grantと古いchild binding拒否、縮小再拡張をモデル/native ASan/UBSanで検査。NState/NProgramと暗黙class operator=の生成/意味対応、scalar宣言順代入、move/他分野/公開版違反は残る。詳細はdocs/frame_copy_assignment.md。

### クラスコピー代入評価器とNState/ghost対応（2026-10-20）

CppClassAssignでvector代入→宣言順scalar読書き→代入先ObjectRef返却を評価する。scalar部分は既存NStmt.assign/Command/runFuelに一致し、初期の型/権限条件から終了を導く。frameのデータ射影が世代に依存しないことと、任意の世代での実成功への持上げ、クラス代入列での旧無効参照の非復活を証明。slots/scalar memory長/binding保持、正確なモデル仕事量、定数scalar一時領域のpeak境界を確認し、GCC/ASan/UBSanで照合。暗黙operator=のAST監査・生成・実caller境界、混在寿命操作列、move/公開版違反/他分野は残る。詳細はdocs/class_assignment.md。

### 暗黙class copy operator=のAST監査/profile生成（2026-10-21）

class_assign.pyで使用済みの暗黙copy operator=を同一TUに実体化し、this/source/FieldDecl、標準vector copy assignment callee、宣言順scalar load/write、*this戻り値を監査してCppClassAssign profile/呼出しを生成。候補UF生成profileと既存profile、任意stateの評価器呼出しを照合し、変異/特殊化/別TU/source改変の拒否、mixed型とcopy ctor非依存、旧copy-onlyを検査。caller field slot/layoutと実代入式の生成・意味対応は残り、class assignment全体の完了とは扱わない。詳細はdocs/class_assignment_audit.md。


### scope破棄・返却moveと暗黙destructor監査（2026-10-22）

[scope破棄](move_destroy.md)、[所有vector返却](move_return.md)、[暗黙destructorの宣言監査](class_destroy.md)を登録した。逆構築順、元要素grantと返却先の寿命、正常入力からの終了、所有/型/範囲不変条件とwork/peakの上界をモデル上で確認する。destructor監査は元FieldDecl逆順と同一TUの標準vector destructorを確認するmember_identity_only段階で、元caller/body/returnの一般生成接続は残る。176登録checksの全件検査と独立kernel検査は成功した（詳細はhandoff）。公開UFの経路圧縮・別カウンタ・入力範囲の違反は解消しておらず、表のUF状況も「一部」に修正した。全experiments検証は未完了。


### class move代入評価器と監査Profile生成（2026-10-22）

[Class move代入](class_move_assignment.md)にContext上のvector move→逐次scalar代入→target参照返却を登録した。元入力からの終了、全Optionのscalar評価器一致、heap不変条件・非復活、metadataとwork/live/heapPeak/scalarPeak/合成peakを証明する。元implicit operator=の監査から型/順序のProfileと実呼出しを生成し、UFとmixed型境界値をLean/native ASan/UBSanで照合した。177登録checksの全件検査と独立kernelは成功した。元callerのFieldDecl→ObjectRef slot、実代入式、move構築/返却/destructorと通常method bodyの生成接続は残り、公開UFの既存違反と全experiments目標は未解消である。

### 非resize結果のpayload戻し込みと全Frame/Context射影（2026-10-22）

[非resize結果の戻し込み](move_restore.md)を登録した。実runFuel後のvector payload・scalar更新・counterを同じallocation/header/grant/世代へ戻し、正常な形状・型・所有条件からの成功、保持/非復活、再射影したFrame/Context全体と実afterの一致を一般証明する。178登録checksの全件検査と独立kernelは成功した。終状態のshape一致だけでは途中resize不存在を証明せず、Allowed等の実行列側の証拠を要求する。実callFuel/finishからの条件導出とscalar返却、元caller AST生成、割当/resize/nested/異種vectorと任意混在寿命列は未接続。公開UFの既存違反と他旧ライブラリの未検証は残る。

### scalar call結果のContext接続と旧UF move後method（2026-10-22）

[scalar call戻し込み](move_call_restore.md)は実call finishからの型・metadata・形状保持と全状態/返却値の対応を登録した。旧UF candidateのclass move後5method、sameの正常条件からの終了証明との接続、旧grant/世代と失効参照、元C++ candidateのnative ASan/UBSanを確認した。179登録checksの全件検査と独立kernelは成功した。source caller生成とghost履歴を除く物理call準備領域は未接続であり、公開UFの既存違反と全experiments検証は未完了。

### Context-native call準備と正常finish・資源式（2026-10-22）

[Contextで準備するcall](move_prepared_call.md)を登録した。参照履歴を予約量に含めず、実bodyからのwellFormed保持、正常な返却/memory条件からのfinish構成、全状態戻し込みとfinishのwork/peak式を証明する。旧UF move後sameに一般定理を適用し、grant履歴2/200件で準備memory14と結果/counter一致を有限確認した。180登録checksの全件検査と独立kernelは成功した。各methodのbody証明と全資源、元caller生成、公開UFの相違と他旧ライブラリは未完了。

### callee binding整理と旧UF rootのContext正常call（2026-10-22）

[callee binding整理](move_call_bindings.md)と[旧UF rootの正常call証明](union_find_compact_root.md)を登録した。元Forest/型/範囲・QS/FWから実bodyとcallの停止、返却rootと圧縮payload、workとbaselineを差し引くscalar/heap/合成peak上界を導く。body/finish/restore成功を入力仮定にしない。move後UFに一般定理を適用し、binding解決・alias・旧grant更新・失効保持も検査した。181登録checksの全件検査と独立kernelは成功した。元callerのAST/prepare/QS/FW生成、他methodと償却・任意混在列、公開UFの既存相違と他旧ライブラリは未完了。

### 元same/sizeのContext正常callとscalar memory保持（2026-10-22）

[query証明](union_find_compact_queries.md)にsame/sizeの実body・call停止、圧縮payload、Connected判定、workとbaselineを差し引くpeak上界を登録した。sizeは元クラスのValidからcomponent要素数との一致とValid保持も導く。一般finishのmemory対応を強め、root/same/sizeの_n/countを含むcaller scalar memory保持をpostへ明記した。182登録checksの全件検査と独立kernelは成功した。unite/count、償却/任意混在列、元caller AST/prepare/QS/FW生成、公開UFの既存相違と他旧ライブラリは残る。

### 元unite/num_groupsのContext正常call（2026-10-22）

[統合とカウンタの証明](union_find_compact_mutation_count.md)にunite/num_groupsの実body/call停止、更新payload/Valid、counterだけのupdatedMemory更新と保持、workとbaselineを差し引くpeak上界を登録した。getterはForest/Weights/Validやn=vector長を要求せず、moved-from/空vectorとi32全範囲を保つ。183登録checksの全件検査と独立kernelは成功した。候補5methodの個別callは揃ったが、元callerのAST/FieldDecl/ObjectRef/prepare/QS/FW生成、償却/任意混在列、公開UF相違と他旧ライブラリのverifyは未完了。

### FieldDeclからのContext method receiver生成（2026-10-22）

[receiver生成](context_method_receiver.md)を登録した。同一TUの宣言ID/順序/型/参照mode/権限を照合し、ObjectRefからContext callへ引数を生成する。元UF全5programのcanonical modelとの一致、一般転送、mixed型とfield/external mutable-ref aliasのLean/native照合、対象外profile/body・変異・source改変拒否を確認した。184登録checksの全件検査と独立kernelは成功した。元free caller ASTと評価順、正常状態からprepare/QS/FWの自動構成、旧backendのalias条件、償却/混在列、公開UF相違と他旧ライブラリは残る。

### receiver引数からのprepare/compact/QS構成（2026-10-22）

[receiver配置証明](move_receiver_layout.md)を登録した。元header/参照権限・counter cellと型妥当な値列から実prepareSavedの成功とmemory/bindings/slotsを構成し、実resolve結果からprepareArgumentsへ接続する。prepared view/slotsから実compact成功とQSも構成する。元UF全5methodへの適用、readonly/moved-from scalar保持、不正型/値域/権限拒否を検査した。185登録checksの全件検査と独立kernelは成功した。UF固有fields/FWの一般構成、元ObjectRef/引数評価からの正常call・償却接続、任意混在寿命列、公開UF相違と他旧ライブラリは未完了。

### 元UF receiverのfields/QS/FW構成（2026-10-23）

[元receiverのfields/QS/FW構成](union_find_receiver_layout.md)を登録した。実resolve結果と元header/readable/所有関係・allocation妥当性から実prepare/compact成功と正確なfields/QS/FWを構成する。全5methodへの一般定理適用、rootの正常終了/圧縮とmoved-from空vectorのgetter正常終了・元count返却、readonly権限を確認した。186登録checksの全件検査と独立kernelは成功した。元ObjectRef/式評価からの一般resolve構成と正常call/償却への接続、caller全体・任意混在寿命列、公開UF相違と他旧ライブラリは未完了。

### pure式と元fieldから実receiver引数評価を構成（2026-10-23）

[pure receiver引数評価](move_receiver_resolve.md)を登録した。任意長の同一Ty pure scalar式列の型/denote条件と元field cellから実resolve成功と型付きsaved列を構成する。全5methodのresolve、算術式を含むrootのresolve→prepare→compact→QS/FW→正常call/圧縮、moved-from field保持、unsigned wrapとsigned overflow拒否を確認した。187登録checksの全件検査と独立kernelは成功した。元ObjectRef/field slotからの一般条件構成、生成wrapper/任意caller/副作用・評価順、償却/任意混在寿命列、公開UF相違と他旧ライブラリは未完了。

### 元ObjectRef配置と生成receiver評価定理（2026-10-23）

[元ObjectRefのfield配置と生成評価定理](move_object_receiver.md)を登録した。slot/binding/memoryからscalarCellとcapture/resolveを構成し、同一TU schemaに基づく全methodのarguments_of_fieldsと、対応する構造のresolve_of_receiverへ接続する。元UF全5method、moved-from元field保持、別名classとmode/型/権限変異を検査し、既存mixed/alias/native検査も維持した。188登録checksの全件検査と独立kernelは成功した。元callerからObjectRef/正常配置を導く一般接続、生成wrapperの正常call/償却/任意混在寿命列、構築/返却/破棄、公開UF相違と他旧ライブラリは未完了。

### 元ObjectRefからのroot/getter正常call合成（2026-10-23）

[元ObjectRefからの正常call](union_find_object_call.md)を登録した。元Receiver/heap・式の条件から共通prepareと正確なQS/FWを構成し、rootの停止/圧縮/Forestとgetterの元count返却、既存work/peak/memory/payload postを一般に導く。再生成したsource wrapperへ転送し、moved-from getterも確認した。189登録checksの全件検査と独立kernelは成功した。same/size/uniteのこの経路への合成、元callerからObjectRef/正常配置を導く一般接続、償却/任意混在寿命列、構築/返却/破棄、公開UF相違と他旧ライブラリは未完了。

### 元ObjectRef経路で全5methodの正常callを合成（2026-10-23）

[same/size/uniteのObjectRef正常call](union_find_object_methods.md)を登録した。共通prepareから各正常callを構成し、Connected/Weights/component cardinality/Valid・countAfter/updatedMemoryと既存work/peak/memory/payload postを維持する。生成source wrapperへの転送と、初期Validから作った別成分状態のcounter2→1・他scalar不変を一般postから確認した。190登録checksの全件検査と独立kernelは成功した。元callerからObjectRef/正常配置を構成・保持する経路、償却/任意混在寿命列、構築/返却/破棄、公開UF相違と他旧ライブラリは未完了。

### 成功callの配置/heap条件と次getterへの接続（2026-10-23）

[呼び出し後の配置・heap条件保持](move_call_layout.md)を登録した。実成功したcompact Context callのrestoreから元slot/binding/header/view/長さ/baseline等を保持し、型妥当性・所有/readable/scope条件を結果へ引き継ぐ。更新memoryから同じObjectRefのReceiverを構成し、別成分unite→getterの両正常終了・返却1・memory保持を一般定理で確認した。191登録checksの全件検査と独立kernelは成功した。結果payload/UF Validの次状態対応、元caller/constructorからの正常配置、償却/任意混在寿命列、公開UF相違と他旧ライブラリは未完了。

### 実currentBuffer/payloadと次UF callの接続（2026-10-23）

[実currentBufferとpayloadの対応](move_call_payload.md)を登録した。元header/現在bufferと結果projectのlookup/itemsから実結果dataを構成し、uniteのpayload/UF Validを同じObjectRefへ引き継いで次rootまで正常終了を確認した。空headerのpayload/容量0と旧target grant失効保持も検査した。192登録checksの全件検査と独立kernelは成功した。全5methodを束ねた状態不変条件とその保持、元caller/constructorの正常配置、償却/任意混在寿命列、公開UF相違と他旧ライブラリは未完了。

### 通常UF状態と任意長メソッド列

[通常UF状態の全5method保持](union_find_object_state.md)と[任意長メソッド列](union_find_object_trace.md)を登録した。元ObjectRef・実currentBuffer/fields/UF Valid/heap条件を各call後に保持し、初期Stateと元の添字条件から任意有限列の正常終了、結果列、最終State、各stepの返却意味と実preparedからの仕事量上界を導く。193件と194件の登録checksの全件検査と独立kernelは成功した。元caller/constructorからの初期State、準備費用を含めた列全体の資源合成/償却、寿命操作との混在、評価順/副作用、公開UF相違解消と他旧ライブラリは未完了。

### 引数評価・準備を含むUF列全体の仕事量

[一般引数評価/準備費用](move_argument_work.md)と[元ObjectRef UF列の仕事量](union_find_object_trace_work.md)を登録した。実引数の純粋式node数・参照費用・callee準備費用を合成し、各callで7+2*arityをbodyWorkへ加え、中間Stateと実Stepを持つChargesで列全体の上界を導く。元の正常終了/返却意味/State保持を維持する。196登録checksの全件検査と独立kernelは成功した。各中間rankに依存する和であり、log/α償却・列全体のpeak、元caller/constructorからの初期State、寿命操作との混在、公開UF相違解消と他旧ライブラリは未完了。

### 実成功fuel列へのUF証明転送

[compact Context呼び出しの成功一意性](move_call_unique.md)と[実ObjectRef呼び出し列への証明転送](union_find_object_trace_actual.md)を登録した。fuel追加時の成功保持と異なるfuel成功結果の一意性から、供給された実callに対応するStep、実scriptの結果State/History/Charges/work上界を構成する。元の正常終了の存在構成は維持し、moved-from弱getterも一般一意性で扱う。197登録checksの全件検査と独立kernelは成功した。列全体のheap/全peak・償却、元caller/constructorからの初期State、寿命操作との混在、公開UF相違解消と他旧ライブラリは未完了。

### UF列の一定ヒープ上界

[元ObjectRef UF列のheap peak](union_find_object_heap_peak.md)を登録した。元header/allocationのHeadersLiveを明示し、実prepare/compact/FWと物理生存量を照合してmax(初期heap peak,初期liveSpace+1-baseSpace)の上界を得る。実restoreの生存量/基準量/Header対応保持から任意長列へ合成し、新測定基準での追加heap≤1と正常終了/意味/仕事量も同時構成する。198登録checksの全件検査と独立kernelは成功した。スタックを含む全peak・償却、元caller/constructorからの初期State/HeadersLive、寿命操作との混在、公開UF相違解消と他旧ライブラリは未完了。

### 全5methodのscalar/過去の全体peakの分離

[一般compact scalar実行とroot](compact_scalar_peak.md)、[全5methodの実scalar上界](union_find_object_scalar_peak.md)を登録した。PRWのlocals/needとsoundWの独立SPB、実prepare/compact/body/finish/restoreを合成し、過去の全体peakをscalar上界へ含めずに評価する。全5methodの返却型と意味を保持し、過去の全体peak1000000を保ったままroot scalar≤91、各methodの共通scalar≤111とEffectを確認した。200登録checksの全件検査と独立kernelは成功した。元caller量によるprepared評価、列全体の一定scalar/全peak、初期State/constructor、償却、寿命混在、公開UF相違と他旧ライブラリは未完了。

### 引数評価・準備を含む任意長UF列の一定scalar上界

[実引数評価/準備のscalar量](move_argument_peak.md)と[列全体の一定scalar上界](union_find_object_uniform_scalar_peak.md)を登録した。元memoryまでにbaseline条件を狭めずraw footprintを評価し、全5methodの実preparedを元caller量へ戻す。Layout保持から操作数に依存しないscalar予算を合成し、正常終了/全History/Charges/work/heapと同時構成する。基準量9が元memory長4を超えるStateでも任意列を検査した。202登録checksの全件検査と独立kernelは成功した。全体peakの一定上界、初期State/constructor、償却、寿命混在、公開UF相違と他旧ライブラリは残る。

### UF任意長列の意味・仕事量・全体peakの同時保証

[実callの全体peak合成](move_call_outer.md)と[UF列全体の全体peak](union_find_object_total_peak.md)を登録した。pure resolve/prepareのscalar単調性/heap保持、本体component単調性と実finish/restoreから、全体peak≤max(初期全体peak,一定scalar予算+一定heap予算)を導く。新測定ではmax(bindings数+5,slots数+101)+1の抽象追加領域上界となり、任意有限列の意味/workとscalar107/heap1/全体108を同時に検査した。204登録checksの全件検査と独立kernelは成功した。元caller/constructor初期State/HeadersLive、rank/償却、寿命混在、公開UF相違と他旧ライブラリは未完了。

### 公開 UnionFind の const API を保つ切替準備（2026-10-25）

公開切替用 fixture の通常 5 method は既存候補の生成 NProgram と同一であり、元の圧縮 API と公開済みの const query overload を併存させる。`Proofs/UfReadCursor.lean` は追加 scalar bindings を保つ読み取り専用の根探索の一般証明を提供する。実 const helper 本体・query 内ループとの AST 生成対応と native 境界は `tests/test_uf_read_cursor.py` で確認する。詳細は [追加フィールドを保つ読み取り専用の根探索](union_find_read_cursor.md)。公開ヘッダーの違反解消や const query 全体の Context 呼出し証明はまだ完了しておらず、棚卸しの完了フラグは変更しない。

### 公開切替候補の const query 本体（2026-10-25）

`Proofs/UfReadInline.lean` / `UfReadQueries.lean` は const helper の引数捕捉と展開、same/size/num_groups の guard から最終 return までを一般証明する。元 memory/bindings/配列を保持し、rank に関する仕事量と本体 need の上界を示す。正規 AST 生成モデルへの適用・境界は `tests/test_uf_read_queries.py`、条件と限界は [const query 本体](union_find_read_queries.md) を参照する。元 Context prepare/finish と caller の 3peak への接続・公開ヘッダー切替は未完了で、棚卸しの完了フラグは変更しない。

### const query の readonly 元receiverからの実呼出し（2026-10-25）

`Proofs/CppMoveReceiverPermissions.lean` / `UfReadPrograms.lean` / `UfReadBody.lean` / `UfReadCall.lean` は、readonly 元field/view/headerから実prepare・compact・本体・finish/restoreと返却/対象配列保持を構成し、prepared基準のworkとinitialを含む3peak上界を保証する。const3program全体/引数写像のAST対応、一般定理のreadonly具体例への適用、moved-fromの実getterは `tests/test_uf_read_call.py` で確認する。[条件・計数と残件](union_find_read_call.md)を参照。caller-only資源への合成、全payload/寿命、公開切替・他旧APIは未完了。棚卸し完了flagは変更しない。


### const 呼出しの caller-only 資源式と意味・owner の接続（2026-10-25）

`UfReadPrepareBudget.lean` は引数評価・prepare を含む全仕事量と、元callerだけの3peak上界を構成する。scalarBudgetから履歴totalPeakを外し、vector長/heap量をscalar上界へ混ぜず、scalarLive+式nodes+caller slot数+49の保守的上界を得る。sizeの成分要素数、sameのConnectedとの同値、保持ownerが元buffer.ownerと一致することも明示した。詳細は [readonly実呼出し](union_find_read_call.md)。全payload/寿命・公開切替・他旧API/全experimentsは未完了、棚卸し完了flagは変更しない。


### readonly UF の全 payload・参照保持（2026-10-25）

`Proofs/UfReadValues.lean` は元receiver条件からconst3callを構成し、全ownerのbuffer/全既存reference read/元memoryとLayout/receiver値を保持する。異なるlive scopeの別mutable UF、有効/古いepochの参照、readonly size後の別UF uniteも `tests/test_uf_read_call.py` で確認する。詳細は [全payload・参照の保持](union_find_read_values.md)。scope終了/copy export/長い操作列・公開切替・他旧API/全experimentsは未完了、棚卸し完了flagは変更しない。


### 公開UFの構成子とメソッドを同じソースから生成（2026-10-25）

`context_class_ir` は切替fixtureの両構成子/export/copy profileと全メソッド/receiver写像を一括生成し、既存の通常5/const3programと両構成子・copy profileへの一致を検査する。途中source差替えや未対応のresizeメソッドを拒否する。詳細は [クラス生成経路](context_class_converter.md)。公開backend/モデルの切替、元実装との差解消、任意寿命・他旧ライブラリの検証は未完了で、棚卸し完了flagは変更しない。


### 公開切替候補の実source wrapperと構成子export（2026-10-25）

`Proofs/Generated/UnionFindPublicCompat.lean` は厳密な宣言範囲を検査した同じfixtureから生成し、`UfPublicSource.lean` が通常5/const3methodの実wrapperと両constructor exportへ元の全成功・意味・保持・work/3peak証明を接続する。readonly queryは有効UF不変条件とhistorical rankから下降rankを構成し、実size/same callのworkを16 log2 n /32 log2 nに関するcaller基準式で抑える。[条件と残件](union_find_public_source.md)を参照する。公開header/TOML/一次proofの切替、implicit copy/move・scope・任意寿命混在と他の旧ライブラリは未完了で、棚卸し完了flagは変更しない。


### copy結果のContext exportと元/先receiver保持（2026-10-25）

`UfCopyContext` は元readonly receiverからmutable/const先の実copyClassとContext exportを構成し、_num_groups/_nを独立に保つ。`UfCopyContextPreserve` は元field/receiver/Stateを保持し、empty headerのghost owner変更もitems等の保持で扱う。`UfCopyNewState` は有効な元UFからコピー先の可変Stateを構成する。work n+4、scalar増分4、常駐heap n+1/一時peak n+2と3peakを示す。`UfCopyReadReady`/`UfCopyCounterCall` は任意の先権限についてcopy後const getterの正常終了・元counter返却・合計work≤元+配列長+14とgetterによる保持/資源条件を構成する。`UfCopyReadQueries` はcopy後const size/sameの正常終了・意味・合計workと保持/資源条件、および有効UF/Historyからの対数系を示す。[条件・検査・未完了事項](union_find_copy_context.md)を参照する。任意caller/assignment/move/scope/寿命混在・公開切替・他旧ライブラリは未完了で、棚卸し完了flagは変更しない。


### 順序生成から全方位木DPへの前提の接続（2026-10-31）

`TreeOrderToDp` は `tree_order_correct` の順序の性質を `TS` へつなぐ。辺の親子分類と逆辺を別途要求し、TOだけでは不十分であることを三角形の反例で検査する。実C++でも生成した順序を全方位DPへ渡して比較する。一般の方針型Pや元Treeクラス全体の検証完了には引き上げない。


## 2026-10-31: Beats の容量条件と復帰検査の結果

Beatsの登録済み条件付き定理は、実スタック256に対しLensがnode容量Lを要求するため、n≥32の実構築状態へ適用できない。[詳細と未解決事項](segment_tree_beats.md)のとおり、節点/スタック容量を分離して解消する。構築とchmin本体の一般化草案は直接Lean検査を通したが、正本への登録・公開Callと残る操作への接続は未完了。

全59部品の復帰ゲートBは、227登録checks、C++/生成モデル照合、Lean build、49923宣言監査、183変更moduleのLean kernel replayを通過した後、独立nanodaがSIGABRTで終了した（実handle30374、終了1）。全件成功とは扱わない。独立検証の失敗時にもstdout/stderrを保存し、終了状態と厳密な成功メッセージを検査する修正を加え、失敗/不正メッセージ/正常終了の回帰検査を通した。全experiments目標は未達。


## 2026-11-01: Beats容量分離の構築とchmin本体

[容量分離補助証明](segment_tree_beats.md)としてBeatsCapCtor/BeatsCapChminを登録した。一般のnについて中点分割木の高さとS=256の予算を示し、S≥34の構築と、chminの実生成メソッド・表現保存へ接続する。旧Lensでは扱えないn=32/L=264/S=256の実長さから構築後の表現を導く回帰例が成功した。公開Call・他操作・独立カーネル監査への接続は未完了であり、元クラス全体と全experimentsの完了には数えない。


## 2026-11-01: Beats全6操作と公開Callの容量分離

BeatsCapCtor/Chmin/Update1/Update2/Update3/Calcの6補助moduleを登録し、構築と全6操作の生成本体・意味保存・公開CallへL/Sを分離した条件を接続した。公開側はProofs.BeatsSeparate名前空間へ追加し、旧定理を保持する。全体build1742対象、n=32/L=264/S=256の構築と公開BFreshSの回帰検査が成功した。公開仕様は2419→2461roots、6090→6141閉包で既存変更0/削除0。共有829modules/228checks/103docs、公開59部品。C++source変更なし。独立監査と全件検査、実allocationからcallerの初期表現を構成する証明は未完了。


## 2026-11-01: 確保を含むBeats構築段階とヘルパー展開

[構築段階でのメソッド呼出し](constructor_stage_methods.md)を追加した。共通AST変換器が構築済みフィールド局所変数をthis呼出しへ渡し、同一宣言IDのメソッドを展開する。可変scalar参照がフィールドを別名参照する際に古い値を捕捉する不具合も修正し、モデル/Cpp/UBSanの回帰例で確認した。

実Beatsの15本のvector確保を含むProofs/Generated/BeatsConstructionStage.leanを登録し、実ソースからの全文生成一致・型検査、確保順/型/スタック256、本体のvectorスロット置換による既存モデルとの構文一致を検査した。新規5検査、UF構築3検査、constructor layout1検査、Context methods6検査が成功した。確保から初期表現を構成する一般証明、評価器の置換の意味保存、クラスexport/寿命と確保費用は未完了。公開仕様2461/6141は変更なし。共有830Lean modules/229checks/104docs、公開59部品。


## 2026-11-01: Beats構築のスロット置換補題

[スロット置換](beats_slot_cycle.md)を登録し、先頭16スロットの循環置換と逆置換、vector/scalarの読取り、型付きscalarCell/envOfの対応、既存の格納内容/権限/仕事量/peak/slot数の保存を示した。CppSlotRenameは任意添字写像の式変換とscalar補助評価・nodes/scalarOnly保存を扱う。状態付き評価器では課金とlocal/literal/variableまでであり、配列size/read、複合式、命令列/ループ、実確保からの前提構成は未完了。元の4*nから8*n+8へのintサイズ変更による入力範囲縮小も違反一覧へ追加した。巨大入力を実確保した検査ではない。


## 2026-11-01: 元のサイズ範囲へ戻すBeats構築候補

[構築候補](beats_wide_candidate.md)をexperimentsへ追加した。12本の確保長と構成子内の子添字2個を64-bit化し、操作側は変更しない。元の4*n<2^31の範囲で実木の全子添字がINT_MAX未満であること、走査/確保の境界、表現の下界をmin L INT_MAXへ縮めることをBeatsIndexHeightで証明した。通常/ASan/UBSan・巨大確保なしの算術境界・候補のstage/body型検査の3検査が成功し、構成子以外の全生成関数は公開版と完全一致した。公開ヘッダー/構築実行証明への切替は未完了で、入力範囲の違反を解消済みとはしない。共有833Lean modules/230checks/106docs、公開59部品、公開仕様2461/6141は不変。

BeatsWideExecを追加し、実候補の64-bit子添字式の補助評価・wrapしないこと・確保長内の境界を元のサイズ範囲で証明した。実ソースからの2式とのrfl一致とINT_MAX超の境界例を含む候補3testsが成功した。ループ全体の構築証明と公開版切替は残る。共有834Lean modules/230checks/106docs。

同moduleで、実入力vectorの長さから12本の確保長式を評価するvden_wide_countも証明した。元の最大サイズで長さ2^32を得る境界例と12式の生成一致を含む候補3testsが成功した。vector確保自体の成功・費用と構築後の表現保存は未完了。

続いて16補助modulesを追加し、最初の走査whileをpexecM上で停止まで接続した。49命令を13補題に分け、CtInv・ValidOK・node/stack別の容量を保ち、残りd回に対する仕事量d*20620+20、storage work d*12を示す。配列長L<2^31の仮定を4*n<2^31へ置き換えた。新modulesは証明器の資源上限を変更せずbuild成功し、実候補のwhile全体とのrfl一致を含む3testsも成功した。後半の集約処理・実確保・caller/export/寿命・公開版切替は残る。共有850Lean modules/230checks/106docs、公開仕様2461/6141は不変。

BeatsWideCtorExecで前後のループと本体初期化を合成し、候補の構築本体の正常終了・意味・容量・BRepSと仕事量/need/storage workの上界を示した。内部節点の子添字<4*nをrngOf_indexから導き、後半へmin L INT_MAXを渡すため、L<2^31は不要になった。実候補の構築本体全文とのrfl一致、初期配列を記号的に作る任意の元サイズ範囲の構築例とn=2^28の例を含む3testsが成功した。巨大確保の実測ではない。実確保・Frame/caller/runFuel/export/寿命・公開版切替と独立監査は残る。共有851Lean modules/230checks/106docs。

BeatsSlotEvalでContainer/NExprの全構文の状態付き評価をスロット置換へ接続した。成功・失敗の両方と、Frame/参照binding/仕事量/peakを含む状態全体を扱う。異なるvectorからの複合size/read、短絡、範囲外失敗、row binding追加の実評価を含む新1testが成功した。命令run/制御フローrunFuel、実確保、class export/寿命は残る。共有852Lean modules/231checks/106docs。

BeatsSlotStmtで末尾への宣言追加、代入、配列書込みのrunを接続した。writable/型変換失敗、右辺先行順、実配列更新、一時binding解放も含める。scopeのleaveについては、任意の戻り値と失敗も含む状態置換の対応を示した。宣言/代入/実配列更新/row参照解放/正常・異常なscope終了を含む2testsが成功した。命令列/制御フローrunFuel、vector確保とFrame/初期表現、class export/寿命は残る。共有853Lean modules/231checks/106docs。

BeatsSlotRunでCoreStmt/CoreCommand範囲のrunFuelへ接続した。任意のfuelで状態全体・return/break・fault/exhaustedが対応し、後続処理の16slots条件を保つ。実wide構築本体がこの範囲に入ることと、15確保後の実stage全文が命令置換と一致することも確認した。vector確保・変更の他命令とinvokeScalarはこの意味保存の対象外。slot回帰3tests、候補3testsが成功した。実確保からのFrame/初期表現・全体資源、class export/寿命、公開版切替と独立監査は残る。共有854Lean modules/231checks/106docs。

BeatsAllocationで実15確保を合成し、正しいcaller表現からrunFuel 16の正常終了、owner/binding/slotの15増加、各fieldのFlat実Frame表現とwritable binding、入力vector保持を証明した。実sourceの確保部分全文とrfl一致し、空入力/長さ3の15配列を実評価する新1testと候補3testsが成功した。本体の旧FWMとのbinding順の差、BFreshS/CVecsへの合成、確保を含む全体資源、class export/寿命、公開版切替と独立監査は残る。共有855Lean modules/232checks/106docs。

BeatsAllocationLayoutで15確保後のcapacity/limit/epochを含む正確なbuffer配置と旧bufferの全metadata保持、保存処理の仕事量12*(8*n+8)+783を示した。15fieldのVOKGとbuffer条件は実配置から導き、新しいlimitを仮定していない。scope/baseのcaller条件の引継ぎ、入力を含むCVecsと本体合成、全体work/peakは残る。確保回帰2testsが成功した。共有856Lean modules/232checks/106docs。

追跡していた旧公開new0単独の独立nanoda検査は、12450.545秒後にSIGABRT（-6）/stack overflowで失敗した。実20457の終了1を回収しstdout/stderrを保存した。全件gate成功ではなく、失敗する依存宣言・式の分割と改善が必要である。スタック上限は増やしていない。

BeatsAllocationLayoutのprefix_conditionsで、scopeのstrict条件とscalar領域のbase条件を確保前から実15確保後へ引き継いだ。prefix_argumentsは初期callerの条件だけから正常終了・正確なbuffer配置/保存処理の仕事量・15fieldと入力vectorのVOKGを導く。入力の権限を保ち、確保後の条件や成功を仮定しない。正本buildと確保回帰2testsが成功した。CVecs全体の合成、binding順、本体・全体work/peak・class寿命・公開版切替・独立検証は未完了。共有856Lean modules/232checks/106docs。

BeatsAllocationArgsで、実prefixの結果をCVecsの全条件へまとめた。slot/binding/owner/scopeのoffsetを分け、初期配列とVVAの一致、node容量8*n+8/stack256のBFreshSも証明した。入力は構築用のreadonly参照でmaximum権限を保ち、元bufferの標準sizeLimit契約だけを初期条件に要求する。8*n+8<2^31は不要。正本buildと確保回帰3tests（offsetの差、全配列の内容、巨大確保なしのn=2^28境界を含む）が成功した。readonly prepare・binding表・本体合成・全体資源・class寿命・公開版切替・独立監査は未完了。共有857Lean modules/232checks/106docs、固定仕様2461roots/6141閉包は不変。

BeatsWideCallで、WideCtorCmdを16vector引数のNProgramとして明示的にprepare/callFuelへ接続した。実prepareのfield→入力のbinding表とFWM、元storage/権限の保持を示し、元の4*n<2^31で正常終了・BRepS・caller復元・scalar/storage仕事量を導く。allocated_callは実15確保とこの正規化呼出しを合成する。候補のインラインstageへ追加のprepare/finishがあるとは扱わず、scope/scalar prefix/binding表/資源を含む対応は残件とする。正本buildと確保回帰4testsが成功した。全体資源・class寿命・公開版切替・独立検証も未完了。共有858Lean modules/232checks/106docs、固定仕様は不変。

BeatsBindingCycleでbinding表と保存済み参照の番号を同時に置換し、Frameのresolve/elementRef/grant/read/write/commit/addBindingを正常・失敗の両方で対応させた。NStateのscalar読取り/vector resolve/仕事量と逆変換も証明した。MultiVecOwnedSoundは同じscopeで確保したrootを扱うmv.sc≤sc+1で既存と同じRunsTo/QpostMを導く。元のsoundM/FWM/固定仕様は保持する。正本2modulesのbuildとslot/binding/scope回帰5testsが成功した。式・命令列・scope/release全体のview対応とインラインstage合成、全体資源、class寿命、公開版切替・独立監査は未完了。共有860Lean modules/232checks/106docs。

BeatsBindingExprでbinding viewの対応をContainer/NExpr全構文へ合成した。rowのbinding追加、型変換・targetCast、算術・除算/剰余・短絡、size/readを扱い、Option全体と結果NState全体を対応させる。初期16bindingsの条件はbindings長の単調性で後続へ引き継ぐ。正本buildとslot/binding/scope回帰6testsが成功した。命令run/runFuel、scope/release全体とインラインstage、全体資源・class寿命・公開版切替・独立監査は未完了。共有861Lean modules/232checks/106docs、固定仕様は不変。

BeatsBindingStmtでbinding viewとrelease/declared/enter、scalar宣言・代入・配列書込みのrun、任意の戻り値のleaveを接続した。rowの右辺・target双方の一時binding、実書込みと元の長さへの解放、vector返却時の所有権移譲、scope復元失敗を扱う。正本buildとslot/binding/scope回帰7testsが成功した。check/return等の残るprimitiveと制御全体runFuel、初期Frame/FWM/QS、インライン構築全体、全体資源・class寿命・公開版切替・独立監査は未完了。共有862Lean modules/232checks/106docs、固定仕様は不変。

BeatsBindingRunでCoreStmt/CoreCommand範囲の全primitiveと制御runFuelをbinding viewへ接続した。実成功後の16bindings条件を保ち、任意fuelのOutcome全体（正常終了・fault・exhausted・return/break）を対応させる。BeatsWideCall.inline_body_viewはslot位置とbindingの両置換を実wide構築本体へ合成し、余分なprepare/finishを挿入しない。初期Frame/FWM/QS、数学的本体証明と実stage全体、全体資源・class寿命・公開版切替・独立監査は未完了。共有863Lean modules/232checks/106docs、固定仕様は不変。

BeatsInlineFrame/Execで、準備済み1vector入力から実15確保・view後のFWM/QS・数学的本体を合成し、候補のstage全文の正常終了・BRepS・全16bufferの最終内容まで接続した。stage全文は実候補の生成ASTとrfl一致する。元の4*n<2^31、n≥1、従来のInRangeを使い、8*n+8<2^31は要求しない。本体scalar仕事量、確保込みstorage仕事量、確保後の状態を基準としたpeak上界も示した。正本2modulesと確保5tests/候補3tests（通常/ASan/UBSan・元サイズ境界・全文生成一致）が成功した。元callerからのreadonly prepare、確保中scalar仕事量/peakを含む閉じた全体資源、class寿命、公開版切替・独立監査は未完了。共有865Lean modules/232checks/106docs、固定仕様は不変。

BeatsInputPrepareでroot入力の実prepareを元callerへ接続した。任意のcaller slot/binding/owner番号と可変/readonly両参照を許し、calleeのreadonly参照・元最大権限・storage・memory prefixを保持してRealizes/Input/Entryとstrict/base条件を導く。実prepareからstage正常終了・BRepS・field/input内容を合成し、prepareのscalar work増分3も証明した。正本buildと確保/構築回帰6testsが成功した。nested rowのchild header入力は現Flat/FWMのroot tag条件のため未検証で、利用形態を削って完了扱いにしない。全体資源・class寿命・公開版切替・独立監査も残る。共有866Lean modules/232checks/106docs、固定仕様は不変。

BeatsAllocationResourcesで実15確保のscalar仕事量増分≤319、常駐領域/storage仕事量増分=12*(8*n+8)+783、scalar/storage/全体peakを初期状態から導いた。stage全体の仕事量は初期work+181824*n+1308、root入力のprepare込みでは元caller.work+181824*n+1311以下。peakも実確保後の未知状態に依存しない線形上界へ合成した。抽象仕事量/cell領域であり実測や検証器資源の増加ではない。row入力、class export/finish/copy/move/寿命、公開版切替・独立監査は未完了。共有867Lean modules/232checks/106docs、固定仕様は不変。

Beatsの構築終了処理はCppConstructorRoots/MultiFinishとBeatsConstructorFieldsで、実field slotsから15vector/2scalarを捕捉してcallerへ移譲するところまで接続した。BeatsConstructCall.constructは元callerのroot grantから実prepare→wide構築stage→exportの成功、BRepS、全15fieldと元入力のModelsを導く。初期prefix長さ/型/scopeは実prepareから自動導出し、可変/readonly入力を保持する。総資源はexportを含む形には未合成で、全caller領域保持・receiver操作・child header入力・converterの複数vector bundle・copy/move/destruction・公開版切替と独立監査/全137旧ライブラリは未完了。詳細は[候補doc](beats_wide_candidate.md)と[引き継ぎ](agent/handoff.md)。

BeatsConstructCall.construct_full/ExportLayoutで、構築後のmemory・bindings・slots・scope・scalar baseline・field権限とlookupを結果に含めた。BeatsConstructReceiverは全15fieldの実resolveとpayload、元callerで有効だった任意scalar参照（別名・readonlyを含む）の保持を導く。6操作へのbuffer契約/strict等の全条件、全無関係vector保持、export込み資源、child header入力、converter/寿命/公開切替/独立監査は残る。

CppConstructorRetirementでroot移譲後のbuffer全体保持とscope破棄後のcontextを一般証明し、Beatsの最終FWMのValid/limit/owner/smallとscopeをexport後まで引き継いだ。BeatsConstructReceiver.construct_readyは元callerから構築成功、BRepS、既存6操作のBVecsを導く。scalar引数・各Safe条件・実method call/更新後receiverの接続、総資源、child header入力・converter・全寿命・公開切替・独立監査は継続中。

BeatsReceiverCallsで返却inf/nを実scalar slotから読み、6操作の生成NProgramへ渡す定理を追加。物理容量L<2^31を要求せず、元4*n範囲から操作用下界だけmin L INT_MAXへ縮め、従来Safe等の前提下で成功・query/更新意味・BRepS・ScalarPostMBを引き継ぐ。構築後の同一状態へ6操作を続けるtraceはC++/UBSanと照合する。一般の更新後receiver/任意長操作列、Safe導出、class converter/寿命/総資源/公開切替/独立監査は未完了。

2026-11-02: CppCallUnitFrameとBeatsReceiverRestoreで、unit/scalar戻りの操作後metadata、INF/nの実読取りと新BVecsを復元した。6拡張定理は従来の意味/BRepS/ScalarPostMBを残して次receiver条件を返す。一般receiverからchmin出力をcalc_maxの入力へ渡す例を型検査する。各Safeの導出、任意長操作列/総資源、全無関係vector内容保持、child header入力・converter/寿命/公開切替/独立監査は継続中。


2026-11-08: 元Set/Sum・Add/Sumのrecord返却applyを、同一TUの異なるreceiver/result recordとして共通class-copy経路へ接続した。receiverは元fieldへの参照、RangeSum引数は全field値snapshotとし、前置更新後に全x/sizeを返す。const/noexceptを保持し、member pointer型のcompiler照合で別familyの同名record取り違えを拒否する。元ソースを変更せず、負size・noop時の未選択乗算・overflow・alias・const/readonly・不正slotと引数不変を有限LLのLean roots/native/UBSanで確認する。登録回帰と実行結果は[引き継ぎ](agent/handoff.md)を参照。applyの任意入力/任意caller一般定理、任意T/M・厳密object identity/lifetime、公開API復元、原本全体/全137は未完了。


2026-11-08: Set/Sum・Add/Sumの元applyの本体について、任意prefixとreceiver位置、型付きv/x/sizeの一般定理を登録回帰へ追加。元の負sizeを許し、Setのnoopは未選択乗算の表現可能性を要求しない。コピー内の更新を含め全PSとprefix保持、結果・停止・IR work/needを示す。任意callerのmixed prepare→body→全field export、任意T/M・厳密identity/lifetime・公開API復元と原本全体/全137は未完了。最新結果は[引き継ぎ](agent/handoff.md)を参照。


2026-11-08: 利用者による `tree/tree.hpp` のLCA降順開始段を `ancestor_.size()-1` とする修正を確認し、旧4頂点の範囲外を登録負例にした。TreeLcaMathの全行降下・添字範囲・同一頂点を含む最初の合流点3 rootsと既存公開LCA caller定理の固定kernel5277宣言、元classの全小木/境界形状/任意root・全頂点対のC++20/UBSan/境界検査が成功。元class全体の生成/寿命・公開API復元・singleton build_ancestorの境界等は未完了のままとする。結果は[引き継ぎ](agent/handoff.md)を参照。


2026-11-08: 元monoid_lazyのSet/Sum・Add/Sum applyを任意callerのmixed準備→本体→全field object返却へ接続し、旧scalar/vectorの値と参照・readonly/alias入力・const結果・scope/storage work保持とIR総仕事量Add≤24/Set≤25・peakを示す。元の負sizeを許し、Setのnoop時に不要な乗算条件を課さない。登録回帰の結果は[引き継ぎ](agent/handoff.md)を参照。任意T/M・member template apply・厳密identity/lifetime・公開API復元・原本全体/全137は未完了。


2026-11-08: 元MaxMin両系統の `apply<M>` も、明示具体化した元pattern/同一TUのrecord宣言IDとmember pointer型を照合し、全field object返却へ接続。Setの `noop ? x : v` は選ばれたimplicit copy/値構築だけを実行し、コピーを値構築子で作り直さない。新3testsで元Add/Set×Max/Minと2fieldのcopy対constructor・未選択overflow・const結果、native/UBSanと不正要求の拒否が成功。任意入力/caller一般定理、任意T/M・厳密identity/lifetime・公開API全体の復元と原本全体/全137は未完了。既存回帰と最新検査は[引き継ぎ](agent/handoff.md)参照。
