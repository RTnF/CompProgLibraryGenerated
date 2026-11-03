# C++ テスト

各部品のテストは独立した基準（総当たり、`__builtin_clzll` など）と照合し、ライブラリ内の `small_template.hpp` を最初に include します。CI は依存順の include と、全部品を同時に include した結果もコンパイルします。

ケースの内容は生成スクリプトまたは専用テキストファイルに置き、TOML と YAML にはファイルの参照先だけを記録します。テストと CI はコンテストサイトと通信しません。 入力は `in/*.txt`、期待出力は `out/*.txt` に統一する。

## 検査の高速化（結果のキャッシュと並列実行）

`python3 tools/check_public.py` は、成功した検査の結果を `.cache/check-results.json`（Git の管理外）に残し、前回成功したときに読んだファイルが変わっていなければ再実行しない。

- Python の検査（生成器との一致、`tests/test_*.py`、`tools/check_*.py`）の依存は自動で記録する（`tools/trace/sitecustomize.py` が読み込んだファイル、一覧したディレクトリ、サブプロセスの引数のファイル、読み込んだモジュールを記録し、`tools/check_cache.py` がそれらが include する C++ ヘッダーも辿る。`lake`/`lean` を呼ぶ検査は、引数のモジュール名や渡した `.lean` ファイルの `import` から、実際に使う `Proofs` のモジュールとその推移的な import だけに依存する。引数なしの `lake build` と `Proofs` ルートはプロジェクト全体に依存する）。
- C++ のテストは、テストと対象ヘッダーが（引用符つきの `#include` を辿って）依存するファイルで判定する。コンパイラのフラグとバージョンも鍵に入れる。
- 証明の安全性検査（`check_proof_security.py`）は `Proofs/`、`verification/`、`lakefile.toml`、`lake-manifest.json`、`lean-toolchain`、検査ツール、公開部品の `.toml` が変わらなければ再実行しない。`lake build` は常に実行する（Lake が増分で処理する）。
- 独立した検査は並列に走る（`--jobs`、既定は 3）。プロセスの優先度は `nice 19` と `ionice -c3` に下げる。
- 失敗した検査の結果は保存しない。`--no-cache` で全件を再実行する。CI は新しいチェックアウトなので常に全件を実行する。
- 2026-10-09 の実測: 全件キャッシュ済みで約 2〜5 秒（キャッシュなしでは約 20 分、並列 2 の低優先度の実行。以前の逐次実行は約 1 時間）。

キャッシュは「前回成功時に観測した入力が同じ」という判定であり、観測できない入力（サブプロセスが内部で読むファイル、時刻や乱数）には依存しない前提である。疑わしいときは `--no-cache` を使う。

## 開発中の検査（短く、負荷を抑える）

全件検査（`python3 tools/check_public.py`、`--mode all`）は、証明の再構築・独立カーネル検査を含むため、冷えた状態で 20 分以上かかり、ディスクとCPUの負荷が大きい。**開発の繰り返しでは回さない**。次の順で絞る。

1. 部品の C++ テストと bridge の一致だけ（数秒）: `python3 tools/check_public.py --mode cpp --component NAME` と `--mode bridge --component NAME`（`--component` は繰り返せる）。
2. Lean の証明: `lake build Proofs.NAMECall`（変更のあるモジュールだけが再構築される）。
3. 文の登録: 公開定理を変えたら `python3 tools/regenerate_statements.py`。
4. 全件検査（ゲート）は、コミット前・まとまった作業の最後に 1 回だけ。`--jobs` の既定は 1（並列を増やすとディスク I/O が増える。WSL の VHDX は C ドライブにあり、過去に負荷で破損している）。

### 検査を 5 分以内に収める仕組み（2026-10-11）

- 証明セキュリティ検査（`tools/check_proof_security.py`）は差分方式にした。作業ディレクトリ `.cache/proof-security-scratch/`（`.gitignore` 済み）を使い回し、Lake の増分ビルドで変わった証明モジュールだけ再ビルドする。カーネルの再生（`leanchecker`）は、ソースまたは import した証明モジュールのハッシュが変わったモジュールだけ行う（記録は `.cache/proof-security-modules.json`）。Mathlib を含む全体の再生（`leanchecker --fresh Proofs`）は、ツールチェイン・Mathlib のピン・監査済みモジュール表のどれかが変わったときだけ行う。実測: 何も変えない場合 1 分 13 秒（初回の全構築は 11 分）。差分判定は git を使わず、ファイル内容のハッシュで行う。
- `verification/InspectEnvironment.lean` の作業リストへの追加が毎回リスト全体のコピーだった（2 次の計算量）。深さ優先に直して 211 秒から 29 秒になった。出力される宣言の集合は同じ（16916 件）。
- 1 つで 5 分を超える検査は分割して別々にキャッシュする（`tests/test_nested_ir_*.py`。元は `tests/test_nested_ir.py` の 4 テスト。オラクルとの照合は 3 つに分割し、3 つで全事例）。
- `check_public.py` の制限時間は 5 分（既定 240 秒）のまま。成功した検査はキャッシュされるので、生成器など広く依存される部品を変えた直後に限り、数回に分けて実行すれば前回の続きから進む。部品を足すだけなら 1 回で終わる。制限時間を延ばして通すことはしない。
- キャッシュ判定の精密化（2026-10-11）: (1) Python の import が作るディレクトリ一覧は、実際に import されたモジュール名と一致する項目だけを依存にする（`tools/trace/sitecustomize.py` の `i`/`n` 行、`tools/check_cache.py` の `import_dirs`/`names`）。`tests/` や `verifier/` に無関係なファイルを足しても、他の検査は無効にならない。同名のモジュールを置いて差し替える場合は検出される。 (2) bridge の検査は部品のメタデータだけを検証する（`tools/public.py` の `component(name)`）。レジストリ全体の検証は `check_public.py` の起動時に 1 回だけ行う。部品を足したときに全部品の bridge 検査がやり直しになるのを避けるため。


`test_union_find_bounds.py` は公開UnionFindの元の入力assertを検査する。複数のプロセス起動と異常終了を扱うため、support検査として登録し、ケースを `imports/union_find_bounds/in/cases.txt` と `out/cases.txt` に置く。生成LeanモデルのfaultとC++のSIGABRT、および正常な境界入力をASan/UBSanで照合する。


`test_union_find_original_api.py` は、元API/別カウンタ/全メソッドの経路圧縮を保つ実験候補と元の再帰実装を全状態で比較する。ケースはPythonの生成関数に置く。private配列・カウンタの比較用C++ハーネスだけを `-fno-access-control` でビルドし、ヘッダーは改変しない。共通生成Leanモデル、Pythonの再帰モデル、ASan/UBSan付きの元C++と候補C++を照合する。一般call証明完成とは区別する。


`test_union_find_fields_call.py` は実験候補から生成した登録済みLeanモデルの完全一致と、別カウンタ参照を持つrootの一般呼出し証明を検査する。counter/vectorの別名、複合式引数、callerの未使用セル・参照一覧、INT_MAXの要素数に対する一般境界条件、flat vector添字式の変数位置と無効slot0を確認する。


`test_union_find_same_call.py` は元API候補のsameの一般呼出し証明と、式内へ展開されたrootの終端return捕捉・継続を検査する。同じ成分/別成分、counterの別名、全scalar/vector状態、途中return/型変換/fuelの条件を確認する。rootテストと共通のFIXTUREを用いる。

`test_union_find_size_call.py` は元API候補のsize一般呼出し、根の負値と返却値/経路圧縮/カウンタ保存、vector読取りの単項plus/neg/notと実evalの境界値/work一致を検査する。Weights条件を明示し、INT_MINのnegは拒否する。

Doublingの変更検出では、値を変える変更はoracleの失敗を要求する。reserve(n)をreserve(0)へ変えた場合はgrowにより値が保たれるため、IR差分・値oracleの成功・元と変更後の実storage work/peakの差分を検査する。

`test_union_find_class_invariant.py` は根の負値と成分要素数/カウンタと根数の不変条件、数学的初期状態、圧縮保存、sizeの実成分要素数を返す全呼出しを検査する。n=INT_MAXは一般定理への適用で確認し、元C++構成子の実確保を検証済みとは扱わない。

`test_union_find_merge_invariant.py` は2成分のサイズ和/カウンタ減算の安全性、結合後の成分/根数/Valid保存、union-by-sizeの同根/swap、3回の連続結合を検査する。元候補の生成uniteの有限全状態照合と、数学的な一般不変条件の証明を区別する。

`test_union_find_unite_tail.py` は候補uniteの生成本体に一致する後半のsame/swap/2 vector書込み/別counter参照更新/returnを一般証明へ適用し、全状態・readonly alias・scope解放・資源上界・参照権限を検査する。root前半/prepare/finishを含む全callとは区別する。

`test_union_find_unite_call.py` は候補uniteのprepare/全本体/callFuel/finishを一般証明へ適用し、同根/swap/通常結合、root圧縮、counterのreadonly引数別名と元参照一覧、const vector alias、全状態/権限/fuelを検査する。INT_MAX端点は抽象vectorで扱う。

`test_union_find_num_groups_call.py` はgetterのprepare/callFuel/finish、空/独立/非自明な成分と一意な根の代表、元配列/参照/未使用cell/資源の保存、readonly引数別名、typed INT_MIN、権限/fuelを検査する。型付きraw値とValidによる成分数解釈を区別する。

`test_union_find_construction.py` はdefault/int構成子の初期化子から生成した処理をrunFuelで実行し、vector/counter/_n、宣言順、変更検出と未対応構文の拒否、C++ UBSanとの有限照合を検査する。fieldの永続化と全入力の構成子証明は未完了。

`test_union_find_construction_proof.py` は確保付き構成子処理の一般証明を実prepareのdefault/4要素stateへ適用し、全vector・権限・初期Valid、任意prefix/heap/参照位置/scopeと抽象INT_MAX端点を確認する。一般callerからのprepareと永続export/資源上界は未完了。

`test_union_find_construction_prepare.py` は一般callerのprepareから構成子初期化の実runFuel/初期Validへ接続し、既存vector/cellとreadonlyなn引数別名、fresh owner/参照/scope、型不一致と抽象INT_MAX端点を検査する。永続exportは未完了。

`test_union_find_construction_export.py` はconstructor専用の終了処理でcallerに保持したfieldからgetter/uniteを実行し、元caller別名と配列の保存を確認する。別C++ fixtureのi32/bool/u64 fieldとtemporary vector解放、UBSan、readonly属性、型/fuel拒否と抽象INT_MAXを検査する。全クラスの割当てmetadata/参照/資源の一般保存は未完了。

`test_union_find_construction_footprint.py` は一般callerのprepare→構成子stageの正確なframe証明を適用し、旧bufferの容量29/limit64/epoch7、新bufferのcapacity/limit/epoch、権限とtag、取得済み要素参照を検査する。default/0/1/2/17要素と抽象INT_MAXを扱う。finish後の全参照保存は別義務。

`test_union_find_construction_preserve.py` はdefault/int構成子の終了後までの全旧buffer/tag保存の一般証明を適用する。容量29/limit64/epoch7、root/child allocation、取得済みreadonly要素参照を終了後frameで直接読めることと権限一覧を確認する。任意Referenceの読取り一般同値は別義務。

`test_union_find_construction_references.py` は構成子終了後の任意の正常な取得済み参照の一般保存、旧ownerのgrant/read同値を検査する。nested readonly参照、stale epochと権限違反の拒否、任意caller/defaultと抽象INT_MAXを含む。

`test_union_find_constructed_receiver.py` はdefault/int構成子からVOKWF/初期Validへの一般接続と、保存した_nを実評価してnum_groupsが0/nを返す呼出しを検査する。元callerのcell/binding/権限/vector、任意callerと抽象INT_MAXを含む。

`test_union_find_root_ready.py` はroot後のVOKWF/buffer契約と全scalarCell保存、圧縮後stateを受ける2連続rootの一般証明を検査する。非自明な森・readonly counter alias・markerと実buffer metadata、任意caller/forest/式への適用を含む。

`test_union_find_method_ready.py` はsame/size/unite/getterの終了後VOKWF・buffer契約へ既存の全fixtureを適用する。uniteのcounter/同cell別名更新・別cell保持と、結合後getter/size/sameの実呼出しを検査する。

`test_union_find_receiver_trace.py` は両構成子からクラス不変条件へ接続し、任意の有限な有効メソッド列の終了・不変条件・配列長保存を一般証明へ適用する。混在12操作の生成モデル/C++ UBSan照合、全配列/count/n、旧caller vector/cell/取得済みref、default getter列とfuel/index拒否、任意列と抽象INT_MAXを検査する。

`test_union_find_rank_doubling.py` は初期/圧縮/union-by-sizeのrank倍増不変条件を実構成子と任意有限メソッド列へ接続し、rank≤log2(n)とrootのwork増分≤91*log2(n)+142を検査する。任意状態/列、default、抽象INT_MAXでrank≤30、非Balanced例を含む。償却解析・全資源上界は別義務。

`test_union_find_trace_work.py` は全5methodの共通work上界と有限列全体への合計を検査する。混在12操作/default、任意列、抽象INT_MAXでm*5865を確認する。構成子自身と追加領域の上界は含めない。

`test_union_find_construction_work.py` はprepare/確保/field初期化/移行・scope解放を含む構成子と全メソッド列のwork合計を検査する。default/0/1/2/17、readonly変数/式引数、混在列、任意caller/列と抽象INT_MAXを含む。


- `test_cpp_constructor_peak.py`: 既存caller buffer（capacity29/epoch7）・scalar aliasを持つ実構成子のfill/scalar宣言/空確保/field exportに領域補題を適用する。復元field数0/2、旧peak900/scalar peak700、baseMemory=memory長、任意caller/callee/field列の一般適用を確認する。実bytes測定や構成子全体の追加領域上界とは区別する。


- `test_union_find_construction_peak.py`: scalar component補題と、生成sized/default bodyの領域上界を実stageへ適用。n=0/1/3/17、旧capacity29/epoch7、memory/bindings増分、過去peak900/scalar700、baseMemory999によるNat差分切捨て、任意entryと抽象INT_MAXでの適用を検査する。全構成子/列のspace証明とは区別。


- `test_union_find_constructor_space.py`: 両構成子の一般定理、n0/1/2/17、readonly counter aliasを読む引数、2+2の式nodes、旧vector readonly alias追加、scalar/storage baseline、旧peak900/scalar700、旧capacity29/epoch7を検査。work/peakと終了後scalar live+4/nested live+n+1または1を確認。任意callerと抽象INT_MAXの定理適用を含み巨大確保は行わない。


- `test_cpp_buffer_headers.py`: 全式constructorと両短絡経路、入れ子containerのstate/root権限保存、実Frame.updated/write/要素代入のbuffer情報とliveSpace保存を検査。既存readonly child参照からの更新値、別buffer保存、連続write、epoch変更によるSameHeaders不成立/stale拒否、readonly経路へのwrite拒否、任意式/container/writeへの一般定理適用を含む。


- `test_cpp_no_resize.py`: nested readを含むdeclare/assign/ret/check/write、実scope leaveのbuffer/root権限/scope保存、memory/一時binding復元、none/scalar返却を検査。UF全5methodの生成ASTのfragment分類と、reserve/sort/dedup/確保/vector返却の除外を確認。任意primitive/leaveへの一般定理適用を含み、制御構造全体の効果証明とは区別する。


- `test_cpp_call_metadata.py`: loop内write/assign・scope・branch両側・早期return・break・zero loopを実runFuelで検査。入れ子vector/read値引数の汎用call、UF混在12操作の全buffer Signature/bindings/slots/scope/scalar liveと既存grant保存・更新値読取り、両構成子から列までのwork/常駐領域、任意列と抽象INT_MAXへの適用を確認。peakや任意参照読取りの一般保存とは区別。


- `test_cpp_reference_headers.py`: readonly child参照を入口に保持し、別のmutable親aliasから実callで-3→42を書換えて読めることを確認。stale/owner/境界/型/権限/grant不一致の拒否保存、旧他buffer、UF混在12操作での既存参照-1→0と失敗保存、一般call/列の定理適用を検査。Signatureだけ同じで旧payloadが不正なheapの負例も含み、両側wellFormed条件を検査する。


- `test_cpp_header_aliases.py`: nested readonly child/root aliases、正常・誤scope・欠損owner・stale parent epoch・範囲外・wrong parent/typeを検査。実callで整数値更新後のheaderOwner、resolveのbinding/Signature保存と全buffer値非同一、invalid heapの負例、UF混在12操作・任意method/列への適用を確認する。


- `test_cpp_fixed_write.py`: binding index 5とowner 4が異なるnested child対象に、RHS/添字のnested readが一時bindingを追加する実writeを検査。対象値-3→74、他owner全buffer lookup、旧readonly参照、binding/slot復元、scalar宣言、readonly書込み拒否、短絡式を確認。一般prefix/固定root/scalar定理の適用を含む。


- `test_cpp_fixed_run.py`: binding index5≠owner4のfixtureで、nested readの条件・一時scalar宣言・scope内反復書込み・代入・両branch・早期return・break・zero loopを実runFuelで検査。対象値102/88、他buffer全lookup、元binding/slotsの復元と末尾追加を確認。UF全5生成bodyの固定root分類とlocal1/child-row書込み・reserve除外、一般定理適用を検査する。


- `test_cpp_fixed_call.py`: nested readonly child参照を保持したcallerでbinding4≠owner2のflat rootを先頭引数へ渡し、nested read値引数の一時binding解放、scope内write、return、prepare/finish復元、他owner全buffer/read値保存を検査。UF混在12操作の他owner全lookup、一般method/列、Strong/workが構成する終了結果とread保存の定理適用を検査する。


- `test_union_find_scalar_peak.py`: rootの実prepare/body/callに独立scalar peak境界を適用。caller outerピークだけ1億へ増やし、実root callのscalar peak<1000、元実行と同scalar peak/memory/storage、outer履歴保持を確認。fuel64/128での同じ成功結果と一般call一意性への適用を検査する。


- `test_union_find_method_scalar_peak.py`: 構成済receiverのouterピークのみ1億へ増やし、全5操作の実成功、prepare結果とscalar上界≤1000を一般定理へ接続。元caller実行と同scalar peak/memory/storage、期待返却値、outer履歴保持を確認。一般OperationとStrong/workが構成するstepへの適用を検査する。


- `test_union_find_uniform_scalar_peak.py`: 全5Operationの実prepare境界、混在12操作を3回反復する36操作の実runCallsへ一様scalar peak定理を適用。12/36操作で同scalarピーク、outer履歴1億保持、resident live/memory長とbudget不変、空列、一般有効列の終了/Strong/workとfuel列非依存性を確認する。


- `test_union_find_storage_peak.py`: nested write/loop/branch/scope/early return/breakと汎用scalar callにstorageピーク定理を適用。fresh退役の正確なpeak更新、baseSpace>liveSpaceでの自然数減算飽和を検査。UF混在12×2=24操作で上界と12操作時と同storage peak、resident/baseline保存、空列と同一outのscalar/storage/Strong/workへの一般適用を確認する。


- `test_cpp_peak_components.py`: nested read/size、casts/unary/binary/div/rem、短絡4枝を含む17成功式へGrowsを適用。component単調性とouter関係、一時binding解放、scalar/write文を検査。outer履歴のみ1億の状態（component合計より大きい）とscalar履歴1億からの評価、一般expr/container/primitiveへの適用を確認する。


- `test_union_find_outer_peak.py`: loop/branch/scope/早期return/break、nested read値引数と2 vector+scalar ref/value引数の実prepare/callをGrowsへ接続。caller復元とouter履歴1億の保持を検査。UF混在24操作に一様whole peakを適用し、12操作時との同ピーク、空列、任意列の終了/Strong/work/metadataと各境界を確認する。


- `test_union_find_constructed_peak.py`: 構成子component境界をn=0/1/17、readonly alias、非零baseline、過去ピーク、抽象INT_MAXへ適用。sized/defaultと任意有効列、n=0 getter列、空列・複合引数式を検査。実構成子と混在12操作の出力を結果一意性で同一化し、全peak境界と最終常駐領域からの増分を確認する。


- `test_cpp_vector_copy.py`: 固定scalar vectorの新ownerコピー、破棄済みスロットを含むストア拡張・旧参照保存・コピー先書換えとwork/spaceを検査。旧/候補UFの全4暗黙特殊メンバー、自己代入、参照・容量再利用・move後復元をUBSanで照合し、固定Clangで生成された特殊メンバーASTを確認する。クラス全体の意味保存証明とは区別する。


- `test_cpp_nested_copy.py`: 過剰容量・readonly child/別root・tombstoneを含むforestから独立rootへコピーし、Extends・新binding/要素参照・書込み分離・scope寿命・work/spaceを一般定理へ接続。空vector、過去peak、非零baseline、型/slot/flags拒否、native親reserve/clear後の参照とコピーの寿命を確認する。


- `test_union_find_copy_receiver.py`: 実構成子で作ったUFのコピーを新vector・独立scalar2セルと両Strongへ接続し、任意有効列の一般定理、全5method混在12操作、元receiverの有限保持、readonly元とmutable先、再コピー/defaultとwork/spaceを検査。同じ操作を元C++・候補C++のconst元からのコピーへ実行しUBSanで照合する。暗黙copy ASTの意味保存とは区別する。


- `test_union_find_copy_preserve.py`: コピー先の任意有効列後の元Strong/全旧成功scalarCell・vector参照保存を一般定理へ接続し、混在12操作の実結果をfuel一意性で同一化。元receiverを再び操作できること、空列/再コピー/任意Strongと有効列/カウンタbindingの値・型に依存しない保存を確認する。


- `test_union_find_copy_peak.py`: コピー前から任意有効列までのscalar/storage/outer境界と常駐増分を一般定理へ接続。混在12操作の実結果、outer履歴1億、独立component履歴、非零baseline、12/24操作の同peak、空列/default0、常駐領域基準と任意Strong/有効列を検査する。


- `test_class_copy_audit.py`: const元から暗黙copyを実体化し、原UFと別名/型/件数/const/mutableのclassを監査。宣言ID・source・順序・body・cast・標準helperの変異、stale印、dump混在、ソース差替え、foreign include、型名と未対応形の拒否を検査。Lean実行生成の完了とは区別する。


`test_cpp_class_copy.py`は共通classコピー評価器とUFの全state同値、const元から独立したコピー先権限、scalar0/3件、slot/型/件数不正、n/countとvector長が異なる表現状態の値保持を検査する。監査AST→Lean profile/copy生成、別class/type/const/mutable/field順、決定性と不正namespace拒否も検査する。call site layoutは別義務。


`test_standard_include_profile.py`は同ASTコンパイルの標準include profileの順序/出所/schema/許可パス、macro/conditional/quoted wrapper/include_next shadow、macroで改変したprimaryと欠落・不整合・user replayの拒否、旧UnionFind原sourceから生成したLean copyのUF bridgeとの任意state同値を検査する。


`test_cpp_copy_statement.py`はコピー元式のrow temporary解放とfresh binding保持、readonly親+動的scalar添字、readonly/mutable先、旧ref/scalar保持と独立書込み、空/不正source、正確なwork/storageピーク/過去outerピーク、一般補題の適用を検査する。固定GCC UBSanのconst親/constコピー先とも有限照合する。flat vector copyは通常NStmt/ASTへ接続。クラスfield-slotは別義務。


`test_vector_copy_ir.py`は監査済みC++コピー関数のAST→NStmt→callFuel生成実行と同じnative関数を照合する。readonly source/parent、動的row/const先、明示block scopeで旧caller参照/状態を保持し、コピー先所有領域が終了時に退去すること、名前変更と未対応nested/bool/allocator overload/自己初期化拒否を検査する。

vector_copy_irの生成実行はroot/行header両入力を扱い、借用した行への書込みとcaller aliasへの反映、readonly→mutable要求、stale epoch、owner/header不一致の拒否も確認する。

`test_class_copy_layout.py`は同じTUのFieldDecl identityから構成子export slotを生成し、UFの既存入口/共通copy bridgeとの全状態同値を確認する。const/mutable/bool fields、fieldと同名local、初期化の補助呼出しによる一時slot、補助関数profileとの名前分離を扱う。別名Packetの構築→const method→const copy→コピー先書込みと元保持を生成Lean/native UBSanで照合する。クラス全call siteやassignment/moveの意味保存完了とは区別する。

`test_cpp_class_copy_commands.py`は通常のvector copy/scalar宣言列の終了・旧参照・配置・work/3peakの一般補題を利用し、scalar0/2件と不正なfuture source slotを検査する。生成profileのscalar3件ではconst copy後のconst method更新をnative UBSanへ照合する。直接copyClassとの資源差を消して同値とはしない。


`test_cpp_nested_invoke.py`は全5 UFメソッドの混在列をcallFuel経由でcallerへ接続し、native UBSanの回答と照合する。readonly結果localの保持、early return後の続行、caller return、scope/loopの解放、callee vectorの退去、fault/exhaustedと不正boolを検査する。UfCallerTraceの任意有限列についての終了・不変条件・回答数/slot数の一般定理も適用する。C++ caller AST変換や全caller資源証明の完了ではない。


`test_class_call_ir.py`は同じTUの元class/標準roots/未展開callerから外部receiver呼出しを生成し、UF全5methodの既存programとの定義同値、混在CPP caller/native UBSan、early return後続行、for/break、const/mutableの別名receiver、同一arity overload、field名のshadow、for incrementの結果temporaryを検査する。別dump/foreign MethodDeclとcall conditionを拒否する。class localの通常構築/代入/moveと全caller資源の検証は別義務。


`test_class_local_copy_ir.py`はUFのsource更新後copyとコピー先全5method、const source→mutable copy、const copyのmutable unsigned/bool、別blockで同名copy、copy root退去/旧source参照を生成評価器とnative UBSanで照合する。constructor signature差替え・自己初期化・static/TLS locals・未対応の通常local構築を明示拒否する。entry値snapshotへ置き換えず、method更新後のsourceを読む。


`test_constructor_view.py`は生成exportViewFuelからconst/mutable field viewsを構築し、const methodのmutable int/bool更新をnative UBSanへ照合する。通常fieldのreadonly化、declared const vector/scalarのupgrade拒否、型/件数不一致、元exportとのmemory/slot/work/3peak一致を検査する。元caller参照の一般補題は元binding/slotのboundsを要求し、不正なfuture slotを初期参照とみなさない。通常local構築のcaller ASTはまだ別義務。


`test_class_construct_ir.py`は同じTUのconstructor stage/field slotsから通常local構築を生成し、UF default/sized/const→全5method/copy/scope、loop/break、未使用の構築、const/mutable int/bool、constructor内部this更新/void call、scalar参照引数、同一arity overloadとPacket localをnative UBSanへ照合する。implicit defaultと内部callee early returnを拒否する。元の「通常localを黙って除外しない」回帰は、未対応implicit defaultの拒否と、以前のPacket例の新しい正例の両方で維持する。


`test_ret_unit_ir.py`はvoid/constructorのbare returnで後続処理が停止し、local vectorを退去すること、元vector/scalar aliasへの更新、void method/void free callerのreturn式を生成モデルとnative UBSanで照合する。unit関数がscalar returnを返す不正なモデルはfaultを要求する。新命令とunit finishの一般補題はCppUnitReturnで確認する。


`test_class_default_arguments.py`は構築子・外部receiver methodの元宣言に属する既定式を生成Lean/native UBSanで照合する。全省略/一部省略/明示指定、scalar/void/const、対象GCCの整数変換、local退去、node IDを保って式だけを変えた不正な展開の拒否、省略時の副作用拒否と明示指定時の非評価を扱う。内部inlinerや任意の副作用のサポートを意味しない。


`test_union_find_historical_rank.py`は元のsizeに対応する根のrankと親方向の厳密増加を、全5methodの生成program・両構築子・任意の有効な有限操作列の定理へ適用する。混在列のモデル/native UBSan、誤った一律rankと根size不一致の拒否も確認する。rank分布/potential/償却αを証明したテストではない。


`test_union_find_rank_population.py`は成分内のrank閾値ごとの個数上界を、生成全5methodと両構築子からの任意の有効な有限列へ適用し、混在列のモデル/native UBSanを照合する。4-node starの点ごとのrank条件だけではPopulationが従わない反例も形式化する。償却αそのもののテストではない。


`test_union_find_global_population.py`は成分分割からのglobal rank分布を、生成全5method、両構築子、一般の有効な操作列へ適用する。元のnode数を使う上界、モデル/native UBSan、8-node starの点ごとのHistoryだけではglobal上界が従わない反例を確認する。償却時間そのものの検証ではない。


`test_union_find_potential.py`はAckermann逆関数の境界/対角逆関数との上界、level/index/node potentialの一般補題、実root callからの圧縮node（rank0含む）更新とpotential非増加の定理を適用し、既存の混在全5methodモデル/native UBSanを照合する。全forest/償却仕事量の証明を意味しない。


`test_union_find_forest_potential.py`は初期値0・圧縮非増加・結合による増加上界を、全5method/両構築子/任意の有効な有限列へ適用する。7結合で作る8-node深さ3の経路圧縮をモデル/native UBSanで照合し、元の参照とメモリを保持する。2-node結合で実際にpotentialが1へ増える例も確認する。potentialの割当てを実CPU仕事量として扱わない。

`test_union_find_path_amortized.py` は生成済みrootの実仕事量とforest potentialの償却不等式を適用する。深さ3・圧縮後の再探索・根そのものの経路で仕事量を検査し、候補C++をUBSanで照合する。全5method/任意操作列の償却解析は未完了。

`test_union_find_method_amortized.py` は生成全5method・任意の有効な有限操作列・両構築子を含む実仕事量の償却上界を適用する。深さ3から圧縮後長さ1になる2回探索の仕事量、size/num_groups、全5method混在列、参照保持をモデルで確認し、native UBSanでサイズswap/n=1/既定構築子も照合する。詳細はdocs/union_find_method_amortized.md。

`test_cpp_vector_copy_assign.py` は自己代入・容量再利用・再確保と要素寿命世代を持つvectorコピー代入モデルを検査する。縮小で破棄した参照は再拡張後も読めず、新参照は読める。storeの元/別owner参照と資源式、一般の代入列での非復活定理を確認し、固定GCCのint/long longでASan/UBSan照合する。Frame/暗黙class operator=への接続は未完了。

`test_cpp_frame_copy_assign.py` は型付きnested Frameでコピー代入の寿命/権限/資源を検査する。縮小→再拡張後の古い参照の読書き拒否、新参照の読書き、先頭/元/他の参照保持、readonly/型/owner拒否、親reserveとimmutable grant、nested peakとbaselineを確認し、GCC/ASan/UBSanで照合する。NState/class operator=の生成接続は未完了。

`test_cpp_class_assign.py` はNState上のclassコピー代入評価器を検査する。宣言順scalar読書きは既存Command/runFuelと一致し、戻りObjectRefは代入先。ghost世代の射影/持上げ、任意代入列の無効参照非復活、自己代入、readonly元、仕事量/peakとメモリ保持、縮小再拡張を確認する。GCC Packetの暗黙代入をASan/UBSan照合するが、operator= AST生成/意味対応は未完了。

`test_class_assign_ir.py` は暗黙copy operator=を実体化し、同一TUのthis/source/FieldDecl/標準vector callee・宣言順・*this返却を監査する。変異AST/特殊化/別TU/source改変を拒否し、候補UFの生成profile/評価器一致、mutable混在型、copy ctor deletedでも代入可能な型、旧copy-only互換、元/候補native UBSanを確認する。実caller layout/代入式への接続は未完了。

`test_union_find_assignment.py` はコピー代入の実状態復元、自己代入、元と別 receiver の保持、読取り専用 source view の終了/値/権限保持、読取り専用 target 拒否、直後の size 呼出し、GCC/UBSan の移動後再代入を検査する。

UnionFind の代入検査は、代入の線形仕事量とコピー後の5種類の通常操作列について、初期 potential を含む一般的な償却上界への接続も確認する。

`test_class_move_audit.py` は暗黙 move 構築/代入の同一TU・フィールド・callee・rvalue・戻り値の監査と変異拒否、固定 GCC/UBSan の要素参照/自己 move を検査する。実行モデルへの一般対応は未完了。

`test_cpp_move_headers.py` は move 構築の header/allocation 分離、捕捉済み read/write と権限、所有者の一意性/存在、空と予約済み空、baseline/peak を Lean と固定 GCC/ASan/UBSan で確認する。全 caller の意味対応は未完了。

`test_cpp_move_assign.py` は move 代入の退役・参照転送・自己 move・非復活・header/所有不変条件と局所資源を Lean と固定 GCC/ASan/UBSan で検査する。Frame/NState/caller 接続と任意混在寿命列は未完了。

`test_cpp_move_frame.py` は object view、型付き Frame 投影、保存済み grant の read 対応、view 解決、整合性と liveSpace の一般定理を検査する。write の一般対応と caller prepare/finish は未完了。

`test_cpp_move_write.py` は固定要素書込みの Frame 戻し込みと元イベントの全Option一致、capture の grant 範囲生成、書込み後の所有/型/資源不変条件を検査する。

`test_cpp_move_context.py` は caller の状態投影、式評価、保存参照と引数準備、正常入力からの準備終了・資源式、借用 call の scalar 更新復元を検査する。一般 scope 破棄と全 caller 接続は未完了。

`test_cpp_move_argument_facts.py` は NExpr/引数評価のデータ・型保持、実評価から全 saved Ready と prepare 成功・資源への一般接続を検査する。class call 等の引数副作用と全 call 接続は未完了。

`test_cpp_move_destroy.py` は逆構築順の scope 破棄、正常入力からの終了、所有/型/参照範囲保持、work/peak 上界と caller 復元を検査する。固定 GCC/ASan/UBSan の標準 allocator 解放も照合する。元 destructor AST と全 body/返却接続は未完了。

`test_class_destroy_audit.py` は専用 witness の destructor identity、元フィールド逆順、同一 TU の標準 destructor、変異拒否と copy/move deleted 型を検査する。実 body の生成接続は未完了。

`test_cpp_move_return.py` は返却先構築→local 破棄→caller 復元の一般終了・target/不変条件保持・work/peak 上界と、固定 GCC/ASan/UBSan の返却後参照・元 UnionFind 候補を検査する。元 return AST と全 class caller の接続は未完了。

`test_class_move_ir.py` は Context の逐次 scalar/class move 代入、元入力からの正常終了、所有・型・非復活・work/peak、監査からの UF Profile/実呼出し生成、混在型境界値と固定 GCC/ASan/UBSan を検査する。元 caller の field-slot と実代入式の生成接続は未完了。

`test_cpp_move_restore.py` は実非resize書込み列のpayload/scalar戻し込み、正常条件からの成功、所有/型/世代/参照/領域保持、全Frame/Context射影一致と固定GCC/ASan/UBSanを検査する。実callFuel/finishと元caller生成の接続は未完了。

`test_cpp_move_call_restore.py` は非resize scalar callの参照更新/返却と旧UFのmove後5method、正常条件からのsame終了と戻し込み、旧grant/世代と失効参照、対象外program拒否、元候補classのnative ASan/UBSanを検査する。元caller生成と物理call準備領域は未接続。

`test_cpp_move_prepared_call.py` は旧UFのmove後sameをContext準備/body/finish/戻し込みで実行し、一般wellFormed保持/正常finish/全射影/work/peak式を適用する。grant履歴2/200件で準備memory長14と実結果/各counter一致を有限確認する。各methodの正常body証明と元caller生成の一般接続は残る。

`test_cpp_move_call_bindings.py` はcallee binding整理のscalar/vector解決・alias保持と不正slot拒否、元sameのfinish後全状態一致、元rootの正常条件からのcall終了/圧縮/work/peak定理適用とmove前grant更新を検査する。元caller生成・他methodへの一般接続は未完了。

`test_uf_compact_queries.py` は元same/sizeの正常条件からのContext call停止・圧縮・連結判定・成分要素数・work/peak定理を適用する。move後の連結/非連結、counter/旧grant保持、sizeのValid保持、INT_MIN重み拒否、正常binding表からのcompact成功を確認する。

`test_uf_compact_mutation_count.py` は元uniteの正常call/更新Valid/counter更新/圧縮/work/peak定理と、num_groupsの正常call/全scalar・payload保持/定数workを検査する。move後の連結/別成分統合、旧grantと失効参照、moved-from/空vector、i32両端値と根数の意味を確認する。

`test_context_method_ir.py` は同一TUのFieldDeclからのContext receiver生成、元UF全5modelとの一致、一般引数転送、mixed型/可変参照alias/const getterのLeanとASan/UBSan照合、型/権限/参照mode/宣言ID変異・対象外body・source改変の拒否を検査する。free caller ASTと正常状態からのprepare/QS/FW生成は残る。

`test_cpp_move_receiver_layout.py` は型付き値suffixのmemory address/binding slotの区別、元UF全5methodの実引数評価からのprepare配置、rootのcompact/QS構成、readonly/moved-from field保持と不正型/値域/参照権限の拒否を検査する。UF固有FWと元caller全体の一般接続は残る。

`test_uf_receiver_layout.py` は元UF全5methodのresolve結果と正常header/allocation条件から、実prepare/compact・元fields/QS・FWを一般構成する。rootとmoved-from getterの正常callへ接続し、readonly権限と元prefix/counter保持も確認する。任意callerの実引数評価の一般成功と償却/混在寿命列の接続は残る。

`test_cpp_move_receiver_resolve.py` は元UF全5methodのfield cellとpure scalar式の意味から実resolveを構成し、算術式を含むrootのprepare/compact/QS/FW/正常callへ接続する。unsigned wrap・signed overflow拒否とmoved-from field保持も確認する。ObjectRef/slotの一般選択と任意caller全体は未完了。

`test_cpp_move_object_receiver.py` は元ObjectRefのslot/binding/memoryからfield読取りとreceiver評価を構成し、元UF全5methodの生成定理へ接続する。別名classとprofile変異、moved-from元field保持も確認する。任意callerから元配置条件を導く接続は残る。

`test_uf_object_call.py` は元ObjectRefの正常配置から一般root/getter call定理を適用し、元sourceから再生成したwrapperの正常終了・root圧縮・moved-from count保持へ転送する。完成済み実resolve/prepare/QS/FW/body成功を入力にしない。

`test_uf_object_methods.py` はsame/size/uniteの元ObjectRef正常call定理を適用し、source生成wrapperへ転送する。元ValidとReachから別成分を証明し、uniteのcounter2→1・他scalar不変を一般postから導く。成功済み本体や固定fuel計算を入力にしない。

`test_cpp_move_call_layout.py` は成功callの配置/heap条件保持と同じObjectRefのReceiver再構成を検査する。別成分uniteのcounter更新から次getterまでを一般正常call定理で接続し、返却1とmemory保持を導く。

`test_cpp_move_call_payload.py` は結果の実currentBuffer/payloadとUF Validを対応させ、unite→rootの両正常終了へ接続する。move元の空headerについても空payload/容量0を保ち、旧target grantが復活しないことを確認する。

`test_uf_object_state.py` は通常UF Stateの全5method保持と完全な既存postを確認する。root→rootと別成分unite→size→same→getterを結果Stateでつなぎ、最終counter1/size4を導く。任意長列は`test_uf_object_trace.py`へ接続し、償却/元callerからの初期状態構成は残る。

`test_uf_object_trace.py` は全5methodを含む任意長列の正常終了・結果State・意味/仕事量の履歴を検査する。任意回数のroot、2成分からの混在列、groups/size履歴からの返却値、不正ObjectRef形と空列を確認する。列全体の資源/償却と元callerからの初期状態構成は残る。

`test_cpp_move_argument_work.py` は実引数評価/準備の仕事量を、field/算術/literal列、unsigned32 wrap、signed32 overflowと個数/mode不一致で検査する。`test_uf_object_trace_work.py` は準備費用を含む全5method混在列・任意回数rootと、getter/rootの具体的な仕事量上界を検査する。列全体のpeak・償却と元callerからの初期状態構成は残る。

`test_uf_object_trace_actual.py` は全5method混在列のfuel追加と実結果へのState/意味/仕事量転送、弱いmoved-from getterの任意成功fuelでの結果一致、実rootの供給fuelに対応するStepを検査する。正常終了の構成は従来のexecute_workから引き継ぐ。

`test_uf_object_heap_peak.py` は全5method混在列・2成分unite列・任意回数rootの一定heap上界/生存量保持、新測定基準での追加heap peak≤1、意味/仕事量との同時構成を検査する。スタックを含む全peakと償却は残る。

`test_uf_object_root_scalar_peak.py` と `test_uf_object_method_scalar_peak.py` は過去の全体peak=1,000,000とscalar上界を分離し、実rootのscalar peak≤91、全5methodのscalar peak≤111と全体peak履歴/Effect、2成分uniteを検査する。prepared scalar量の元caller量での評価と列全体への合成は残る。

`test_cpp_move_argument_peak.py` は実field/算術/literal列のprepare scalar peak≤22を検査する。`test_uf_object_uniform_scalar_peak.py` は任意有限列の一定scalar上界、memory長4より大きい基準量9、意味/仕事量/heapとの同時保持を検査する。全体peakへの合成は残る。

`test_cpp_move_call_outer.py` は実prepareとmoved-from弱getterで全体peak合成を検査する。`test_uf_object_total_peak.py` は任意有限列の意味/work/scalar/heap/全体peak同時保持、新基準での全体追加peak≤108、過去の全体peak1000000の一定予算を検査する。rank/償却と初期State構成・寿命混在は残る。

`test_uf_object_query_amortized.py` はroot/sizeの実経路長による仕事量を、停止用rankを1000増やした同じStateでも検査する。数学的unite履歴、αpotential、正常終了・返却意味と既存scalar/heap/全体領域上界を同時に確認する。全5method列の償却接続は残る。

`test_uf_object_binary_amortized.py` はsameの接続/非接続、uniteの成分数2→1と同一成分保持について、元Stepの意味・αpotential・既存領域上界を検査する。`test_uf_object_amortized.py` は全5methodの任意有限列/空列、実併合を含む混在列とfuel+17の実scriptへの転送を検査する。

`test_uf_object_initial_amortized.py` は4 singleton/0要素の正常Stateから初期potentialなしの仕事量と意味・全領域を検査する。`test_cpp_move_append_owned.py` は構築済みbufferを新規IDで表へ追加し、元move後の有効/無効grant・dead allocation・所有/生存/型条件、readonly/空bufferの境界を確認する。元constructor実exportとの接続は残る。

`test_cpp_constructor_layout.py` は参照引数を書き換える元C++ constructorを生成し、実memory=[9,7]/bindings/slots/Layoutをkernelで検査、元C++をUBSanで照合する。`test_uf_object_construction_export.py` は空/既存scalar callerの任意サイズ/default constructorの実new buffer・heap export・配置を検査する。正常Context Stateとcaller全体の対応は残る。

`test_uf_object_constructed_state.py` は元sized/default constructorから正常Context State・任意有限method列への接続、constructorを含むα仕事量・意味の履歴・全領域、move後の有効/無効grantの保持を検査する。

`test_uf_object_construction_preserve.py` は新UFのsized/default構築で旧UFの正常State・親配列/rank/counter/sizeを保つこと、空headerのowner2→3の更新を検査する。

`test_uf_object_getter_frame.py` は実構築後の2つのUFへの交互getter、返却1/n・両親配列と成分数保持・仕事量増分20以下、空headerの同一objectを両Stateに渡す場合を検査する。

`test_uf_object_values.py` は全5methodの任意有効operationについて異なるUFを両方向で保持し、実併合で対象成分数4→3、別UFの成分数1と親配列・size4保持を確認する。

`test_uf_object_pair_trace.py` は異なるUFへの実併合→経路圧縮、任意有限有効交互列、混在8操作、空header/空bufferの2UFへの空列と任意回getterを検査する。

`test_uf_object_constructed_pair.py` は両元constructor→旧/新UFのPair/Apart→任意有限有効交互列と、既存empty headerのowner更新/非aliasを検査する。

`test_uf_object_read_source.py` はreadonly borrow/readonly ownerからの実copy・新mutable UF・線形work・元read/readonly binding保持と、空vector/成分数1/_n4のmoved-from sourceをそのままコピーする境界を検査する。

`test_context_method_selection.py` は旧DisjointSet/getNumの元ソース生成との一致・一般本体証明・通常/空/moved-from Context・原本C++ UBSanを検査する。混合field順と依存method inline、選択外methodのalias/const解析、存在しない対象や到達する未対応bodyの拒否を検査する。旧クラス全体の検証とは区別する。

`test_disjoint_set_getter_call.py` は元DisjointSet/getNumのfield条件からprepare→実call→復元と仕事量/3peakを構成する一般定理を検査する。通常/moved-from、readonly size、counter参照権限の不足、fuel2の境界を扱い、旧class全体の完了とは区別する。

`test_uf_read_cursor.py` は追加 scalar binding を保つ読み取り専用の根探索を、公開切替用 fixture の実 AST 生成モデルへ接続する。通常 5 method の既存候補との一致、const helper の一般本体証明、const query 内ループの配置、readonly/fuel/範囲外境界と native ASan/UBSan を確認する。const query 全体の呼出し証明は残る。

`test_uf_read_queries.py` は const same/size/num_groups の AST 生成本体へ、guard→実 inline→return の一般証明を適用する。元 memory/bindings/配列の保持と仕事量/need の上界、readonly field、_n と実長の相違、空・範囲外・fuel 不足・INT_MIN を検査する。元 Context prepare/finish は次段に残る。

`test_uf_read_call.py` は const3program 全体と FieldDecl 引数写像の AST 生成一致、readonly 元receiverからの prepare/compact/実本体/finish/restore と資源定理の適用を確認する。元header権限任意Bool、全scalar bindings readonly、empty-header moved-from getter、mutable要求の拒否を扱う。実prepared/initialを含む資源式から、caller-onlyの式への最終合成も扱う。

const呼出しの同検査は `UfReadPrepareBudget` のcaller-only work/3peak、scalar上界のheap/履歴totalPeak非依存とscalarLive+式nodes+slot数+49の一般上界、sizeの成分要素数/同一成分判定/元ownerへの保持を追加確認する。

同検査の `test_readonly_world_and_multiple_owner_lifetimes` は `UfReadValues` の全buffer lookup/read/receiver更新と、scope 0/1 の2owner、有効epoch7/古いepoch6、別UFのmutable権限保持およびreadonly呼出し後の別UF uniteを確認する。scope終了やcopy export全体の完了とは区別する。


`test_context_class_ir.py` は同じ公開切替用UFソースから両構成子/export/copy profileと全メソッド/receiver写像を一括生成する。通常5・const3programと両構成子・copy profileの既存証明対象とのrfl一致、const引数写像、初期値/返却field変更の意味モデルへの反映、途中source差替えとresize追加の拒否を検査する。[対象と限界](../docs/context_class_converter.md)を参照する。公開登録の切替や任意のクラス寿命全体の完了は意味しない。

`test_context_class_ir.py` の公開bundle検査は、static method・template・本体なしmethod/constructor・static data・conversion・friend・nested type・type aliasを追加した実ソースを拒否する。部分method選択の既存経路は維持し、公開bundleの宣言検査と部分選択の併用を拒否する。


同検査は `Proofs/Generated/UnionFindPublicCompat.lean` と実fixtureからの生成全文も照合し、`Proofs/UfPublicSource.lean` を直接importする。通常5/const3methodの実receiver wrapper、両constructor export、元の全postcondition、readonlyの履歴rankからの対数work上界を型検査する。[証明対象と未完了事項](../docs/union_find_public_source.md)を参照する。公開headerの切替やimplicit lifetime全体の完了は意味しない。


`test_uf_copy_context.py` は source objectから実copyを構成してContextへ戻すUfCopyContext/UfCopyContextPreserve/UfCopyNewStateを検査する。readonly元から可変/const先、複数owner、余剰capacity/epochの異なる元、_n99の保持、元への非干渉とconst先書込み拒否、moved-fromの_n4/counter1/empty配列を実generated呼出しで確認する。固定GCCのASan/UBSan比較も行う。一般のcopy→const getter定理の正常終了・値・合計work上界・保持条件も、複数ownerとmoved-fromの両例に任意の先権限で適用する。UfCopyReadQueriesの一般size/sameも任意の元/先権限と変数引数へ適用し、同一成分・別成分・同じ要素、元/他owner/コピー先の保持、native const sameを比較する。[copy Contextの条件と残件](../docs/union_find_copy_context.md)を参照する。


`test_tree_order_dp.py` は `TreeOrderMath.TO.toTS` の一般証明をimportし、順序生成の結果から有効な木のDP前提を構成する例と、余分な非親子辺を持つ三角形の反例をLeanで確認する。`tree_full_dp.cpp` は実際の `tree_order` 出力を用いて全方位DPと素朴な高さ計算を比較する。[前提と接続範囲](../docs/tree_full_dp.md)を参照する。


- `test_beats_capacities.py`: Beatsの節点配列容量とDFSスタック容量の分離を確認する。n=32の実長さ(L=264、S=256)に旧Lensが適用できないことと、新しい容量条件から生成構築モデルの正常終了・表現を得ることをLeanで検査する。公開caller/allocation/全操作の検証完了を意味しない。


- `test_constructor_stage_methods.py`: 構築段階で実フィールドを渡してヘルパーを展開し、複数vectorの更新をLean/C++/UBSanで比較する。初期化・引数の変更、再帰の拒否、Beatsの確保prefixと既存本体へのスロット置換も検査する。


- `test_beats_wide_candidate.py`: 元のサイズ範囲を保つBeats構築候補を通常/ASan/UBSan、巨大配列なしの算術境界、実ASTからのLean型検査で確認する。構成子以外の全生成関数が公開版と同一であることも確認する。公開切替と候補全範囲の証明は未完了。
