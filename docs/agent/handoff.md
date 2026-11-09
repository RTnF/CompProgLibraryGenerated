# 作業引き継ぎ

更新: 2026-11-09。時系列ログを圧縮して上書きした。目的は **experiments の全137ファイルを検証し、元API・機能・汎用性を保って移植すること**。一部のモデルやCI成功だけで完了としない。

## 現在の作業

1. `library/`の59部品を原本に似た12分野へ移動し、隣接するTOML・source/include・テスト・文書・再帰登録/cache・配布ZIPを更新済み。本handoffも原本ごとの表へ圧縮済み。
2. 配置変更で見つかった旧ModIntモデルのずれとnested oracleの旧パス参照を解消。最新の全件gateは実75688が終了0（853.562秒）。inventory137・Lean1793build・59CPP/59bridge・共有242checks・52416宣言の命題/定義/公理依存・両kernel（nanoda49238宣言）・ZIP59header単独/一括includeが成功。証拠は `.cache/wip/library_layout_20261109/final_gate/{checks_state.json,all.log,package.log,archive.log}`。この成功は原本137ファイル全体の移植完了を意味しない。
3. `monoid_lazy`の元nested API候補（experiments/verification/algebraic_structure/monoid_lazy.hpp、原本とnamespace/includeだけ異なる）を検証中。1field値構築とRangeAdd::idの任意caller証明を追加し、原本/候補の6型ずつを検査した実46323は2tests/380.630秒終了0。kernel3857×8/3885×4・C++/UBSan・入力hash不変。値構築総IR work≤引数式nodes+6（literalは7）、idは変換/scope込み≤9、raw need=P.length+7。scalar/vector・権限・const結果・scope/peakを保持。RangeSetのvalue/default/id（2field）を27rootsで共通化し、3入口のprepare→body→field export・const/scalar/vector保持・work/peakがLean compile成功。総IR workは値構築≤式nodes+9、既定≤9、id≤10。実5160で原本/候補両familyの再生成/kernel/UBSan検査中（`.cache/wip/set_record_ctor_20261109/registered/active_job.json`）。対象を固定し同じhandleをpollする。Sum構築/e/op/apply・MaxMin op/e/apply・Add/Set composeは既存一般証明へ接続済み。任意T/M・strict identity/lifetime・公開切替・原本全体は未完了。全件gateは後続変更前のsnapshot。原本1ファイル全体の移植完了前にはpushしない。

## 判定と作業制約

- **公開59部品**と**原本137ファイル（header66/template6/driver65）**は別の単位。公開部品の検証があっても元class/API・任意T・全lifetimeの完了を意味しない。表の「部分」は原本全体未完了。
- 既存の大量の変更を保持する。`MEMORY.md`、cache、ツール実体、ローカル測定値は公開候補に含めない。新commit/pushなし。HEADは `5bf952dff99f102e9aea74aa0d096ac953c5cdec`、最後に確認したorigin/mainは `096d2902959f2607b39baee5c46e786feb31db70`。
- push粒度は原本1ファイル全体の移植完了。機密情報検査→commit→手動承認push→対象SHAのActions/配布物終了確認。[Git手順](git_workflow.md)を守る。
- リクエスト量を抑え、agentを増やさない。重いjobは1本、低優先度・offline。Lean1thread、nanoda固定2threads/既定16MiB。資源不足は上限増加で回避しない。観測timeoutだけでjobを再起動しない。
- コンテストサイトへテスト/CIから通信せず、この環境から提出しない。機密値をログへ出さない。

## 重点項目・再開地点

| 項目 | 確認済み | 残件・次の手 |
| --- | --- | --- |
| monoid_lazy / Sum | RangeSum構築、friend op、Add/Set compose、Add/Set applyの全fieldを任意callerへ接続。readonly/alias・const結果・scalar/vector保持とwork/peak | 任意T/M・厳密object identity/lifetime・元のnested class公開API全体を復元 |
| monoid_lazy / MaxMin | Add/Set×Max/Minのop/e一般callerとmember templateの全field返却。RecordArgumentで同一TUの宣言ID/patternを照合しmember pointer型もcompilerで確認 | Add/Set apply<M>は任意caller exportまで一般証明済み（work≤14/21）。元nested API候補はexperimentalへ配置済み。候補のSum/MaxMinとcomposeは一般証明接続済み。1field値構築/RangeAdd idも一般caller済み。RangeSet value/default/id、任意T/M・strict identity/lifetime・公開切替は未完了。copy/値構築のconditionalは選択枝だけ実行。副作用条件・入れ子record conditional等は未対応として拒否 |
| Group/Monoid | hidden friend・既定構築・汎用型制約を復元。LLモデルと一般caller、float単位元C++回帰 | 任意T・浮動小数Lean契約/誤差・strict lifetime。原本2系統の差を保って監査 |
| ModInt | 原本/移動後ヘッダはバイト同一、移動前配置と移動後からの生成モデルも同一 | 生成モデル11定義を再生成済み。Powのloop一般定理を追加セルのscope除去込みで更新し従来の数値上界を維持。Div/全Opsの一般定理もbuild成功。独立kernel36roots/6172宣言も成功。全件gateも成功。評価を消して照合だけ合わせない |
| Beats | 元構築の15vector/2scalar、初期callerからの資源上界、export・buffer保持・6操作の呼出し/receiver復元 | Safe条件導出、任意更新列・償却、全無関係vector保持、child入力、class converter/寿命・公開切替・独立監査 |
| Tree | 利用者のLCA上限を実表size()-1へ修正した変更を保持。全小木/境界/任意root・全対C++、全行降下の一般数学定理 | 元class全体のC++由来生成、build_ancestorのsingleton assert、cost_depthの型、直径/全API・lifetimeは未 |
| Fenwick/UnionFind | 公開クラスで元APIの保持を改善。Fenwick構築の範囲外と+=のみの型を修正。UnionFindの元class/コピー/receiverを監査 | 原本ファイル全体の完了監査、任意型/厳密lifetime。部分関数の成功を全API完了にしない |
| SegmentTree/Lazy | 現公開policy版は部分的に検証済み | 元のobject型・全操作/search左右・汎用性を狭めた違反を解消。クラスを関数ごとのファイルへ分割しない |
| SquareMatrix | 比較/powの不具合とpow(ll)/traitを修正、C++/UBSan比較済み | 候補全範囲の一般証明・原本APIそのままの公開判定 |

## 検査証拠

- `.cache/wip/scalar_record_ctor_20261109/registered/`: 実46323は2tests/380.630秒終了0。原本/候補6型ずつ、kernel3857×8/3885×4、C++/UBSan・入力hash不変。新12rootsの値構築は純粋scalar式を取り総work≤nodes+6、6rootsのRangeAdd idは総work≤9。全field exportと元scalar/vector・const権限・scope/peak。任意T/M/lifetime/全体は未完。

- `.cache/wip/monoid_lazy_candidate_sum_20261109/registered/`: 実70126は7tests/507.224秒終了0。kernel4316×3（原本1/候補Sum構築2）、4086×2（Sum op）、4117×4（MaxMin op/e）、4072×2（Add compose）、4102×2（Set compose）、4126/4104（Sum apply）。C++/UBSan・入力hash不変。原本/候補で同一の証明fixturesを使用。任意T/M・strict lifetime・全体未完はreceiptに明記。

- `.cache/wip/monoid_lazy_api_20261109/registered/`: 実97763は5tests/418.354秒終了0。新idの原本/候補API/copy回帰・旧id2件のcompile負例、旧frontend3673、Add compose/id4072×2、原本/候補MaxMin apply各4080/4080/4100/4100。C++/UBSan・入力hash不変、receiptは任意T/M/lifetime/全体未完を明記。共有検査は新API check追加で243件（全件gateは未再実行）。

- `.cache/wip/extrema_set_general_20261109/registered/`: 実76341はfresh原本4具体化のkernel4080/4080/4100/4100・C++/UBSan・入力hash不変で166.179秒終了0。Add/Set applyの任意caller・全scalar/vector保持・const結果・scope/peak・総work増分≤14/21。Set rawはnoop9/代入12、need≤P.length+13、prepare2参照+1値は7work。privateのraw/prepare単体は2759×2、caller草案もcompile成功。全体未完了と任意T/M/lifetime未検証はreceiptに明記。



- `.cache/wip/contract_review_20261109/`: 旧モデル/Pow/Call/Opsと現Componentを別olean領域へbuildし、旧契約2481宣言を不一致0で再現。既存named theorem133件の型変更は9件。公開ModInt34件では本体等式1件以外同一。tail/加減乗/汎用callerの正確な状態にcaptureセルを含め、除算callerのhbodyはcapture2回へ更新、入力/結果/数値上界は保持。review.jsonにソース/契約hashと判断、旧契約はstatements.before.json。契約のroot2481件は不変、14変更5追加のみ同期。

- `.cache/wip/library_layout_20261109/`: 旧doublingパスと変異scratch配置を修正。full_gateの実54494は共有242件成功後に最終closure照合で終了1。secrets/check.pyは変更対象全ファイルの変更前後・差分・未push履歴を検査（件数とhashはreceipt/inputs.json）。全ファイル版の生検出2件は変更前後のProofs.MultiVecN.rowKeyの公開宣言digestで、HEAD/現契約/検査済Lean環境からの再計算一致を確認。認証情報0件、疑似tokenの対照1件。生検出と根拠はnoncredential_findings.jsonに保持。inputs.jsonのhash時点の検査根拠であり、その後の編集には適用しない。

- `.cache/wip/modint_discard_20261108/`: 元モデル/Pow/Call/Opsのsnapshotとbuild harness。37305はPow build終了0。penv_pushed/returnedCopies/pushedCopies/returnedCopies_execを共通化し、div_exec_copiesで戻り値コピー数≤2を扱う。実16423のCallと23883のOpsがbuild成功。pushed/returnedCopiesでret captureを全PS・費用・領域に含め、従来の数値上界は維持。実41493のregistered_check.pyはbuild/bridge/CPP/36roots6172宣言のkernelと入力hash不変で終了0。registered/{inputs,receipt}.json参照。旧full_gate/run_checks.pyの実58423は終了1。配置変更の残存パス修正後、20261109の別dirで再検査する。次段の未検証draftは.cache/wip/extrema_template_general_20261108/{add_raw,prepare_ref_value}.draft.lean。検査対象へは未反映、全件gate後にfresh生成モデルでcompile/kernel検査してから登録する。C++原本/公開headerは今回変更なし。
- `.cache/wip/library_layout_20261108/`: moves.jsonで118ファイルの移動とヘッダ58同一/1include変更を確認。登録59・登録基盤19tests成功。実38333はinventory0/all1（全件gate未完）。all.logは59CPP成功とModInt橋渡し失敗を記録。modint_relocation.jsonで同じ旧配置でも生成差分が存在することを確認。実70116は58bridge/ZIP収録59件・単独/一括include検査をすべて終了0で回収済み。relocation_state.json参照。この旧配置検査のjobは終了済み。機密検査は同dir secrets/check.py、inputs.json/receipt.jsonで最終hashと結果を確認。
- `.cache/wip/member_template_result_20261108/new/`: 新3tests/161.944秒終了0。元Add/Set×Max/Minはnanoda2825宣言×4、custom2field copy/constructは2817。native/UBSan、未具体化型・不正要求・副作用条件の拒否、入力hash不変が成功。
- 同 `related/`: 実29467は18tests/350.508秒終了0。nanoda 2815/2811/4126/4104/4102/4102/4072/4072/4086/4316/2834/2648/2820。Sum caller・const/prefix・constructor/factory・class-copy/union_find・同名record拒否が成功。私的harnessの旧base置換漏れで古いrelatedのinputs/logを上書きしたため、今回の正本をこの新relatedへ複写済み。旧16testsのreceiptだけはlegacy_related_receipt_84162.json、旧hash根拠には使わない。
- `.cache/wip/member_apply_call_20261108/registered/`: Sum applyとcomposeの3tests/209.825秒終了0。Set apply4126/Add apply4104、compose4072×2/4102×2。Add総IR work増分≤24/Set≤25。新共有prepare補題の最終proof-security/root照合と全件gateも20261109に成功。
- `.cache/wip/tree_lca_rows_20261108/registered/`: 新3rootsと既存LCA callerのnanoda5277、2tests/11.602秒終了0。旧上限だけ戻した4頂点負例は境界assertで失敗、修正後成功。TreeLcaCallのbuildも成功（既存依存の非推奨警告あり）。
- 配置変更前の共有240 checksの旧結果は、現在の成功根拠には使わない。現在の全件成功は20261109/final_gate。機密検査の現時点の根拠は20261109/secretsのinputs.jsonであり、後続変更は最終hashで再検査する。

## 原本ごとの進捗と懸念

L=`experiments/library/cpp/`、L3=`experiments/library3/cpp/`。公開部分ありでも元class全体の検証は未完了。詳細・証拠は [原本台帳](../verification_inventory.json)、[移植違反一覧](../experiments_status.md)、[問題点](../experiments_findings.md)、[修正記録](fixes.md)。

| 原本 | 進捗 | 懸念・残件 |
| --- | --- | --- |
| `L/algebraic_structure/group.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/algebraic_structure/monoid.hpp` | 部分 | 公開APIを復元しLLモデル/一般caller・浮動小数単位元のC++回帰済み。任意T/浮動小数のLean・lifetimeは未 |
| `L/algebraic_structure/monoid_lazy.hpp` | 進行中 | Sum applyの任意caller接続済み。MaxMin apply<M>はLL全入力（Addは加算範囲内）・任意caller接続まで。元API候補はexperimentalにあり、任意T/M・lifetime・公開切替は未 |
| `L/array/cumulative_sum.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/array/doubling.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/array/element_count.hpp` | 部分 | 候補あり。原本API全体の生成/証明/公開判定は未 |
| `L/array/search_util.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/array/sort_util.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/fps/convolution.hpp` | 未 | NTT/FPSの元API・modint依存と計算量の生成/証明は未 |
| `L/geometry/line.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/geometry/polygon.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/geometry/vector.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/bellman_ford.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/dijkstra.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/edge.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/edge_flow.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/find_cycle.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/graph_flow.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/graph_list.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/graph_matrix.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/graph/lowlink.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/prim.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/topological_sort.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/graph/warshall_floyd.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/interval/interval.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/interval/interval_union.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/modint/dynamic_modint.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/modint/modint.hpp` | 部分 | 公開ModIntの11モデル/一般証明を更新、bridge/kernel成功。全件gate成功。原本class全API/汎用型の移植は未完 |
| `L/number/ratio.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/number/square_matrix.hpp` | 部分 | 比較・powの不具合とAPI型/traitを修正。候補の全class一般証明/公開切替は未 |
| `L/number_theory/enumerate_quotients.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/number_theory/factorize.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L/number_theory/floor_sum.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/number_theory/is_prime.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/random/xorshift.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/segment_tree/binary_indexed_tree.hpp` | 部分 | 公開Fenwickクラスに構築3種/add/sum2種、+=のみの型を保持。任意T・厳密lifetimeは未 |
| `L/segment_tree/lazy_segment_tree.hpp` | 部分 | 公開chmin/maxの部分検証。元のobject/全作用/search左右・汎用性は未 |
| `L/segment_tree/segment_tree.hpp` | 部分 | 公開版は値/静的policyへ変更。元のモノイドobject・search左右・全汎用性の復元は未 |
| `L/segment_tree/segment_tree_beats.hpp` | 進行中 | 構築→15vector/2scalar export・6操作→receiver復元まで。Safe導出・任意操作列・償却/総資源・全lifetime/公開切替は未 |
| `L/segment_tree/segment_tree_beats_sum.hpp` | 未 | 別原本の全API/償却・重複統合を未確認 |
| `L/set/multiset.hpp` | 未 | std::multiset契約・元APIの変換/証明が必要 |
| `L/set/set.hpp` | 未 | std::set契約・元APIの変換/証明が必要 |
| `L/string/char_count.hpp` | 部分 | 局所監査のみ。標準string操作と汎用性の生成/証明は未 |
| `L/string/rolling_hash.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/tree/tree.hpp` | 部分 | LCA上限修正と全行降下定理/全対C++成功。元class全体・singleton構築・cost型/直径等は未 |
| `L/union_find/disjoint_set_union.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L/union_find/union_find.hpp` | 部分 | 公開クラスの経路圧縮/統合・5scalar/3vector連携を検証。全原本/汎用型/lifetime監査は継続 |
| `L3/AlgebraicStructure/Group.hpp` | 部分 | 有限LL・Affine<int>の生成/一般caller済み。任意T・全object/lifetimeは未 |
| `L3/AlgebraicStructure/Mapping.hpp` | 部分 | Affineの値渡し/型変換を維持して有限具体化。任意T/全objectは未 |
| `L3/AlgebraicStructure/Monoid.hpp` | 部分 | library3の有限LL具体化を監査。任意T・全object/lifetimeは未 |
| `L3/Array/CumulativeSum.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Array/SortUtil.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Geometry/Point.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L3/Graph/BellmanFord.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/Dijkstra.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/GraphL.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L3/Graph/GraphM.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L3/Graph/Lowlink.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/Prim.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/TopologicalSort.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/Graph/UnionFind.hpp` | 部分 | 有限クラス変換と公開版との差を確認。元版の全API/検証完了監査は未 |
| `L3/Graph/WarshallFloyd.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/ModInt/ModInt.hpp` | 部分 | 公開ModIntのモデルずれは単体検査成功。元版の全API/汎用型への適用は未完 |
| `L3/NumberTheory/Factorize.hpp` | 未 | 原本API/依存型の変換・Lean証明・C++/include検査が必要 |
| `L3/NumberTheory/IsPrime.hpp` | 部分 | 公開部品あり。元class/全API・汎用型との一致と全体検証が未完 |
| `L3/SegmentTree/SegmentTree.hpp` | 部分 | 元版の全API/型の保持と公開版との差の解消が必要 |

テンプレート6件（L/L3各3件）とdriver65件は原本台帳で別管理。テンプレート自体の全検証と型/マクロ/乱択契約は未完。driverのコンパイル成功は依存ライブラリの証明には数えない。

## 詳細資料

- [元template class](../original_template_classes.md)、[class copy/constructor監査](../class_copy_audit.md)、[Beats候補](../beats_wide_candidate.md)、[信頼境界](../trust_policy.md)
- [CI/リリース記録](ci_release_handoff_20261103.md)は過去の経過資料。現行のpush粒度と再開地点はこの文書を優先する。
- 古い履歴は [11月1日以前](handoff_history_20261101.md)。今回の上書き前snapshotは `.cache/wip/library_layout_20261108/handoff_before.md`（ローカルのみ）。
