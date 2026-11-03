# 作業の引き継ぎ

更新: 2026-11-03。過去の引き継ぎ全文は [履歴](handoff_history_20261101.md) にbyte同一で保存した。通常はこの文書から再開し、履歴は必要な節だけ検索して読む。

## 復帰時の最新確認（2026-11-03）

- リリースのステージ確認: index全1914ファイルが最終機密走査のSHA256と一致し、検出0。変更1737ファイル、325976追加/1146削除。MEMORY.mdと.cache/.tools/.lake/benchmarks/localは除外。git diff --cached --checkは引継ぎ済み追加ファイルの行末空白・末尾空行を報告した（ログはrelease_20261103/staged_whitespace.txt）。今回それらを整形せず検証済み内容を維持した。構文sh -nは成功。commit/push後の対象SHAとCI結果は引き続き確認する。

- **全件gate実72559は終了0を回収済み（4636.309秒）。再pollしない。** `.cache/wip/check_public_after_wide_call_fix{.txt,_state.json}` に実結果を保存。C++/bridge59、共有235checks、正本/scratchのLean build各1789targets、Mathlib778modules、52228宣言の公理依存・固定仕様監査、Lean kernel replay、未改変固定nanodaの **49088宣言** がすべて成功した。export917517490bytes、nanoda.stderr.logは0bytes。証明監査開始から773.7秒でreplay完了、832.7秒でexport完了、1044.2秒で独立検証完了（各値は開始からの累積時間）。2threads/標準16MiB stackを維持した。以下の72559「稼働中」は終了前の観測履歴。
- **公開59部品のgate成功は、旧137ファイル全体の検証完了ではない。** 元のAPI/汎用性/入力範囲、Beatsの公開切替・class copyのcaller AST/寿命・Safe導出/任意長操作列/償却、他の未対応ヘッダーやドライバの残件を維持する。gate成功後に下記「copy本体のlive領域と3種peak」まで証明追加・関連検査を進めた。全件gate72559はこの追加前の結果として区別する。
- 利用者から「キリが良くなったら、機密確認→git commit→git push」の指示を受けた。copy本体のpeak証明を一区切りとし、リリース前の監査・全件検査へ移る。git_workflow.mdに従いpush後は対象SHAのCI/ヘッダーリリース結果を確認する。旧137件の検証目標はこのリリースと区別して継続する。作業記録は `.cache/wip/release_20261103/`。初回機密走査はtracked/nonignored作業木1938候補と未push2コミットの追加/変更blobを対象に2154版・1955内容を確認し、検出0、binary/symlink0。秘密値を出力しない検出器を使用した。ステージ後も対象を再確認する。ローカルの古いMEMORY.mdは公開対象へ含めず保持する。
- リリース前の実17394は終了0を回収済み（987.181秒）。137件inventory、追加後の全件all（59部品/235checks/Lean build1789、変更のない正本のproof-securityは成功cache利用）、59ヘッダーZIPの作成、ヘッダー単独/全体includeのcompile・実行がすべて成功した。ログはrelease_20261103/{inventory,all,package,archive}.txtとchecks_state.json。APIで確認したremote mainはローカルorigin/mainと同じ013cf1ff7b67d9683c23ac398eadc257a5bf8a06で、既存未push2コミットとの分岐はない。機密確認とstaged差分確認を終えてcommit/pushし、当該SHAのCIとrelease-headersの終了結果まで確認する。実17394は再pollしない。
- **MatPowの未完了診断を再検証済み**。元の `Proofs.MatPowExec.pow_while` は固定nanodaで4809宣言成功、kernel単体23.450秒（標準16MiB/2threads/50秒窓内）。費用計算の小補題化候補も4810宣言成功したが、元の証明が成功するため**適用していない**。元ソースSHA256は `6fcfc7c5dfaef29ad6398e63acbde7a58b85878f879679e7512a7697952ef3d4` のまま。range診断で50秒窓の末尾に残ることをstack overflowの根拠としない。比較・判断は `.cache/wip/matpow_while_repair/{review,original_state,decision}.json`。
- `tests/test_mat_pow_kernel.py` を共有checkへ追加した。元のpow_whileとpow_finalの依存閉包4964宣言を固定nanodaで成功、1test28.947秒。許可公理は基礎3件のみ、標準stack/2threads、export/kernel各120秒、非0/不正な成功メッセージを拒否する。公開59/共有876/checks **235**/docs106、995Lean source audit、固定baseline byte一致、Python構文・diff確認も成功。原本SquareMatrixクラス全体の証明が完成したとは扱わない。
- 次の全件検査に備え、失敗28093の917519177bytesのexportを `.cache/wip/proof_security_failure_28093/` へrenameで保管した。archive.jsonにSHA256を記録。nanoda.original.jsonは元configのbyte同一コピー、nanoda.jsonは保管先exportを参照する診断用config。今後、昔の宣言indexを調べるときはこの保管先configを使い、次回監査が上書きするscratchのconfigを使わない。
- WideCall修正後の全件検査wrapper `.cache/wip/check_public_after_wide_call_fix.py` はall/jobs1/14400秒、nice19/ionice3/offlineで実行し、実72559の終了0を回収済み。ログ/状態は `.cache/wip/check_public_after_wide_call_fix{.txt,_state.json}`。この終了済みハンドルを再pollせず、次の作業は最新のcopy証明の節から再開する。
- 更新済みAGENTS.md・lessons・本書を確認して単独で復帰した。以下の「稼働中」「次は83949をpoll」は過去の観測であり、現在の再開指示として扱わない。復帰時のプロセス一覧にlean/lake/leanchecker/nanodaはなく、重い検査は起動していない。
- 有界宣言別診断は7ログ分まで終了済み。`.cache/wip/full_export_failure_probe/coverage.json` で49086宣言中49084の完了を記録し、未完了はindex38602 `Proofs.BeatsWideCall.call` とindex38780 `Proofs.MatPowExec.pow_while`。これは診断用の集計であり、全件独立成功でも、元のstack overflowの原因確定でもない。
- 前回のWideCall修正は実ソースにも反映済み。`Proofs/BeatsWideCall.lean` のSHA256は `24d3b4c99ea7697114a8be09e10ef17577f5e3f85ff87e9a2be4f3a407fd0315` で、独立検証済み候補と一致する。費用不等式を小補題へ分け、call/allocated_callの型とprogram本体は不変。`.cache/wip/wide_call_stack_repair/` のstate/review/final_auditを確認し、固定nanodaの6672宣言成功（16.669秒）、回帰2tests成功（19.105秒）、固定baseline不変を確認した。kernel_replay.txtは空で終了コードの記録が確認できないため、その検査の成功は追加主張しない。
- 次の独立検証の調査対象は `MatPowExec.pow_while`。資源上限を増やさず証明項を局所化する。全件監査28093は終了1のままで、全137ファイルの検証目標も未達。class copy先の一般表現・総資源・寿命、Beatsの公開切替と他の旧ライブラリの残件も維持する。

## 継続目標と作業制約

利用者の目標は `experiments/` の過去のライブラリすべての検証と、必要に応じた重複の統合。元の137ファイル全体が対象であり、公開59部品のgateや現在のBeatsだけを完了条件にしない。全目標は未達・active。

- `AGENTS.md` と [lessons](lessons.md)、[全件計画](../verification_plan.md)、[台帳](../verification_inventory.md)、[違反・残件](../experiments_status.md)を参照する。
- 元のAPI/型/機能/入力範囲を保つ。未完成の候補は `experiments/`。sorry/未説明公理を証明済みと扱わない。
- 利用者のcapacity指示により単独agentで進め、subagentは起動していない。重い検査は重複起動せず、nice19/ionice3/jobs1を使う。資源不足をメモリ/stack/heartbeat/深度の増加で回避しない。
- 大量の作業中・未追跡ファイルにClaude CodeとCodexの成果がある。reset/clean/一括削除をしない。コミット/pushはしていない。Git操作を伴うときはgit_workflowを読む。
- テスト/CIはネットワークを使わず、この環境からコンテストへ提出しない。

## 独立検証: 公開59部品の全件gate成功・旧137件全体は未完了

最新の全件成功は冒頭の72559を参照。以下は構築定理修正と、全件成功前の失敗・診断の履歴である。

**2026-11-02の最新結果**: `Proofs.BeatsRep.segment_tree_beats_new0` と容量分離版 `Proofs.BeatsSeparate.segment_tree_beats_new0` を合わせた依存閉包 **6824宣言** が、未改変の固定版nanodaで終了0、`Checked 6824 declarations with no errors`。export込み13.758秒。2threads/標準16MiB stackを維持し、前提・結論・費用上界を変更していない。全件gate Bの失敗と同じ式かは未確認であり、全件成功とは扱わない。以下の20457は修正前の失敗履歴。

**全件gate32702は終了1を回収済み（4628.227秒）。再poll/再起動しない。** C++/bridge59・登録234checks・正本とscratchのLean build1789targets・Mathlib監査範囲778modulesまでは通過したが、公開rootの一致検査で停止した。旧固定契約2461rootsに対して実環境2460rootsで、自動生成補題 `Proofs.BeatsSeparate.segment_tree_beats_new0._proof_1_4` が消えた差分だった。独立kernelには到達しておらず、全件成功ではない。ログ/状態は `.cache/wip/check_public_after_new0_fix{.txt,_state.json}`。以下の生存確認の箇条書きは終了前の観測履歴。

**全件証明監査28093は終了1を回収済み（16741.732秒）。再poll/同条件の再起動をしない。** wrapper `.cache/wip/check_proof_security_after_aux_review.py`、ログ `.cache/wip/proof_security_after_aux_review.txt`、状態 `.cache/wip/proof_security_after_aux_review_state.json`。scratch build1789targets、Mathlib778modules、root一致、52226宣言の公理依存・固定仕様監査を通過し、1371.2秒でLean kernel replay成功、1432.0秒でexport完了後、固定nanodaのthread_0がstack overflow/SIGABRT(-6)で失敗した。export917519177bytes、nanoda.stdout.logは0bytes、stderrはstack overflow。資源上限を上げず、宣言別・項別の診断へ進む。旧new0単独の修正成功と同じ失敗箇所であるとはまだ確認していない。全件独立成功/全件all成功ではない。以下や各節の「28093稼働中」は終了前の観測履歴。

- 有界診断 `.cache/wip/probe_full_export_failure.py`、実50330はwrapper終了0を回収済み。子probeは50秒でkill/reapし、12558宣言が完了、index12558/12559のApplyLoop_ch5補助proofが処理中だった。そこでstack overflowを起こしたとはまだ言えない。ログ/状態 `.cache/wip/full_export_failure_probe/`。診断probeは未改変の固定nanoda rlibのcheck_declarを呼び各START/ENDを記録するもので、独立成功の代替ではない。
- 完了したprefixを繰り返さず、同export/configのindex12558以降を診断した実35616はwrapper終了0を回収済み。50秒で子をkill/reap、5494宣言が完了し、index18045のUfMethodPreparePeak.prepare_fields_peak._proof_1_2と18053のprepare_same_peak._proof_1_2が未完了だった。これらがstack overflow原因とはまだ確定していない。range.rsは同じ未改変rlibにlinkする診断wrapperで、2threads/16MiB・50秒を維持する。ログ/状態同folderのfrom_12558/。
- 次の `.cache/wip/full_export_failure_probe/run_range.py 18045` を実83949で開始した。次は同83949をpollする。ログ/状態from_18045/。最小未完了indexから再開しており、長時間の全件検査は再起動していない。

- 継続turnでも32702を同じ実ハンドルでpollし、55秒待機後も稼働を確認した。C++/bridge後のPython検査中で、最新traceはUnion-Find関連から `tests/test_context_method_selection.py` へ進んだ（確認時のtrace更新から0.5秒）。check_cache.run_tracedは成功した検査の出力をcaptureして表示しないため、gateログがbridge末尾のままでも停止とは限らない。検証対象のLean/C++/testsはこの継続turnでは編集していない。
- 元137ファイルのハッシュを再照合し、台帳との差分0を確認。`.cache/wip/inventory_remaining_20261102.json` に現在の手動レビュー状況を保存した。JSON台帳はpending130/partial7、明示的verification_target5件、記録上のlean_proved/publishedは各2件のままである。これは実装全体の新しい検証結果ではなく、台帳の未同期・未レビューを含む記録値。公開59登録から元137ファイルの網羅を自動推論せず、元ファイル/宣言と検証先の対応をレビューして更新する残件を維持する。状態の自動昇格はしていない。

- 原因箇所: `beats_call_unit` の最後の引数、`r.cost + 2*16 + [].length + 2 ≤ 4*n*45414+100+34` のインライン `by simp; omega`。大きな係数を含む費用式の証明項でnanodaがstackを消費した。`SegmentTreeBeatsCall.lean` のprivate補題 `new0_extra_bound` はcost/boundを抽象化して同じ不等式を証明し、両構築定理で `h5` に適用する。既存hp_new0/wr_new0も再利用した。診断用の構築call分割・任意progへの一般化は失敗箇所特定のためだけに試し、最終コードには残していない。
- 最終のexport/config/stdout/stderr/state: `.cache/wip/nanoda_declaration_probe/both_constructors/`。export 65133853bytes、SHA256 `e14046dc6909056a0a4c59ba456e76e1e9c059994faf94c60a8e9d92d7d2a7d6`。実36053は旧定理単独6584宣言成功、実30884内の両構築検査も成功。実30884の最終監査結果は同directory親のfinal_audit.jsonを参照。
- 再発防止: 既存 `tests/test_beats_capacities.py` に固定版exporter/nanodaで両構築定理を検査する120秒上限の回帰を追加。標準stackのまま、非0・timeout・不正な成功メッセージを拒否。最終2testsは終了0/15.693秒、`.cache/wip/nanoda_declaration_probe/regression_both.txt`。登録check数は234のまま。
- 最終正本build実96389終了0/1048targets。直列実30884は両構築独立・上記2tests・変更module直接型検査15.526秒・Lean kernel replay4.590秒・両定理の仕様hash照合・995files source audit・59/876/234/106のregistry確認を終了0で回収した。旧定理hash `fbd875a5a450a03c4acfcc2ab89e1fff4907609cd50e7b3581e8bbba97104c36`、分離版hash `5fa576d08700a1e526ed6fe7ff8dbaf7c99b745fee8886951cdb626ae8fe4b8f` は固定契約と一致し、statements.jsonはreviewed baselineとbyte同一。実67506のsecurity suiteも終了0。新しい証明資源上限指定なし、新/変更moduleのwarningなし、git diff --checkと変更5filesの空白確認も成功。C++変更はないためfixes表への追記対象ではない。
- 診断: 同directoryのprobe.rs/run.pyは未改変rlibのcheck_declarを呼び、2threads/16MiBで各宣言の開始終了を記録。旧exportの6579依存宣言は終了し、旧new0本体だけ未完了と特定。別のphase_checkerはソースコピーへログだけ加えた診断専用で、ARG36の推論中にstack overflowを再現。診断用checkerの結果を独立検証成功とは扱わず、`.tools/nanoda_lib` の原本/binaryは変更していない。試行・timeoutは各state.jsonに残し、元の長時間検査は再起動していない。

**実ハンドル20457は終了1を回収済み**。旧公開定理 `Proofs.BeatsRep.segment_tree_beats_new0` だけを対象にした独立nanoda検査が、12450.545秒後にnanodaのSIGABRT（-6）で失敗した。stderrは **thread_0 has overflowed its stack / fatal runtime error: stack overflow, aborting**。全件gateではなく、独立成功とも扱わない。

- 起動script: `.cache/wip/check_beats_new0_independent_resume.py`
- ログ: `.cache/wip/beats_new0_independent.txt`
- export/config/stdout/stderr/state: `.cache/wip/beats_nanoda_new0_probe/`
- exportは63203870bytes、SHA256 `fed9607931696cb4c76012ed80ba8abf84c3b0ed89d4bdcff50cda77faeb11be`。
- 20457を再poll/再起動しない。`full_check_state.json`は修正前のfailed、stdout空、stderr94bytesを保存した。旧new0は上記の小補題化で解消した。全件BのSIGABRTと同じ宣言・式であることまでは未特定。
- 以前の全件gate B（30374）は終了1、nanodaがSIGABRT。C++/bridge59、227checks、Lean build1736、49923宣言監査、183変更moduleのLean kernel replayまでは成功した。独立成功/全件成功ではない。B/30374を再pollしない。
- 診断保存を `tools/check_proof_security.py` に追加済み。nanoda stdout/stderrをファイルへ書き、非0と不正な成功メッセージを拒否する。関連10tests成功。cache更新は独立成功後のみ。
- 旧chmin_exec単独は独立6483宣言成功、wf/nb_chminは704宣言成功。旧new0の40秒probeはtimeoutだったが、今回の長時間検査でstack overflowの診断を回収した。現在、追跡中の独立検証プロセスはない。

## 証明監査の資源・観測改善（2026-11-02）

- pinned leancheckerのソースを確認し、各argvをNameのprefixとして扱い、prefixごとに全search pathを再走査することを確認した。現在の変更236moduleには集約Proofsが含まれるため、236対象をProofsの1prefixへ圧縮しても検査集合は同じ。compact_replay_targetsを追加し、同名の先頭文字列だけが似た兄弟を混同しないこと・空/重複・全128部分集合でcoverage同一を回帰確認した。実プロジェクト995moduleでも同一集合を確認。次回は--verboseと開始時の対象数を表示する。現在の28093は起動時の旧236指定のまま完了まで追跡する。
- scratchのcompiled modulesは当初996で、監査ソース995に対してProofs.Probeだけが古い生成物だった。kernel replay完了後、独立kernelが読むexportには触れず、Probe.ilean/Probe.oleanを.cache/proof-security-retired/へ保管した。現在のactive compiled modulesは全995sourceと一致。次回sync_scratchでもソースが消えたProofs配下のolean/server/private/ileanを保管する。現行sourceの生成物、集約Proofs、他のnamespaceを残す回帰も成功。
- 監査済みのrowsをkernel起動前に解放するようにした。export対象名とunsupported-name拒否を先に確定し、不要な宣言bodyと外部checkerの式表を同時に保持しない。上限値を増やした変更ではない。環境dumpのfile保存/逐次解析、root差分診断も維持する。
- 追加した上記2回帰は終了0（0.014秒）、Python構文確認とdiff --checkも成功。旧security10testsは前turnで成功しており、今回の追加2件だけを単独実行した。新helper追加による登録check数の変更はない。現行の28093の結果を、改善後スクリプトを再実行した結果とは扱わない。
- scope診断: .cache/wip/kernel_replay_coverage_probe.json、kernel_replay_built_module_scope.json、kernel_replay_scope_after_cleanup.json。最後のfileはactive995と保管した2partsを記録する。

## 不具合修正と次の残件

### Fenwickの汎用性修正（2026-11-02・公開版へ反映済み）

元の `BinaryIndexedTree<T>` は `+=` と `-` が使える型を受けるが、公開 `FenwickTree<T>` のvector構築子だけが `tree[j] = tree[j] + tree[i]` と書き換えられ、追加の `operator+` を要求している。元の汎用性を狭める不具合として、現在は元と同じ+=へ修正済み。`Additive`（+=/-/0からの構築はあるが+はない）の同じ使用例が元ソースでcompile/run終了0、現公開版でoperator+不在のcompile終了1となることを実78246で回収した。

- 再現・候補・確認scriptは `.cache/wip/fenwick_generic_review/`。`state.json` が元と公開の差、`patch_state.json` が候補の結果。公開headerの確認時SHA256は `3dc3e09ffab4175f7b123003b37412962a67d2d35aff4806b35ff3a5df146147`。
- 候補 `fenwick_tree.hpp` は当該代入だけを `tree[j] += tree[i]` に戻す。custom型のcompile/run成功。元公開版と候補からlower_sourceで生成した **全4関数のIRが完全一致**し、long longの既存モデルは変わらない。実28100終了0。候補hashは `600824e69d490149f51d3c76012f99aacd549bad2a5bcc3050ed6d987fd70966`。
- `fenwick_tree_test.cpp` は既存tests/fenwick_tree.cppの全ケースにAdditiveWithoutPlusの全3構築子・add・両sumの回帰を加えた草案。実67948終了0で全ケースのUBSan確認済み（回復なし）。`prepare_regression.py` と `regression_state.json` に記録。元ソース/公開header/TOML/既存testsはこの確認中に変更していない。custom型のLean証明が済んだという意味ではなく、従来のlong longモデルとの同一性と元APIのC++汎用性を確認したもの。
- **32702の終了後に公開版へ反映済み**。headerの+=、TOML source_sha256、新custom型を含む既存C++回帰、部品doc、fixes表の5ファイルを、事前hashを全件確認して同時更新した。新header SHA256は `b6e1924976db63c81429650545062cc65b68df01d373f282c3fcbc0b438819f5`。古い「元が範囲外へ書く」という説明も修正済み。実32269終了0で対象componentのC++（sanitizers/template-firstを含む）とbridge、security10testsを確認。logsは同cacheのpublic_cpp.txt/public_bridge.txt/security_tests.txt（10tests11.318秒）。long longのモデル・Lean定理は変更していない。現在の全件all成功を、変更前32702の部分成功から主張しない。
- 実32702はこのturnの55秒poll後も稼働中。最新traceは `test_uf_object_constructed_state.py` → `test_uf_object_trace.py` → `test_context_method_ir.py` と進み、最後の確認時trace更新から0.1秒だった。別の重い検査やgateの再起動はしていない。

### SquareMatrixの既存最小修正候補のAPI・費用回帰（2026-11-02・追加確認）

原本の比較演算子（存在しないxへの参照）とpowの不要な最終二乗は、このturnで修正・C++回帰済み。既存 `.cache/wip/square_matrix_source_repair_20261031.hpp` を読み、公開候補を丸ごと移すのではなく、元のグローバルSquareMatrix<T,n>・pow(ll) const・公開mat配列・行配列参照・aggregateを保った最小修正候補であることを再確認した。この候補は比較を各要素へ直し、powは指数を右シフトして残りがあるときだけ二乗する。既存の単項マイナス修正は保持している。

- `.cache/wip/square_matrix_source_review/check.py` とregression.cppに、既存の修正候補ケースへ追加した回帰を保存。実8000終了0。UBSan（回復なし）で、比較/各要素の違い/EqualityOnly型/Fibonacci行列の累乗/LLONG_MAXとLLONG_MINの指数0・1/大指数の-1を確認した。
- static_assertでpowのmember pointerが `SquareMatrix<long long,2> (SquareMatrix<long long,2>::*)(ll) const`、mutable/constの行参照型、公開matの型、aggregateを確認。mod17の独自要素型で指数0/1/2/3/4/8/31/LLONG_MAXを評価し、実乗算回数がpopcount(e)+floor(log2(e))（e=0は0）となり、不要な最後の二乗がないことも確認した。
- state.jsonに原本hash `469543532af6e6c0b266474a14dc3cc6af0594dfe2127e896ed95e1b25a32588` と候補hash `7ff812ae0566f16867e522c19c3ccc2b026d5f07f31da9ebe2fc658d3f7c72ab` を記録。この段階の候補は現在の原本へ反映済みだが、クラス全体のAST→Lean証明は未完了。以下に実反映後の検査を記録する。
- 最新の32702は同ハンドル55秒poll後も稼働中。traceはクラスmove→ret_unit→ `tests/test_cpp_nested_invoke.py`（登録Python検査88/234）へ進み、確認時のtrace更新から1.8秒。検査対象のC++/Lean/testsは今回も変更せず、小さな候補C++確認だけを別cacheで直列実行した。

### SquareMatrixの原本反映と台帳更新（2026-11-02・最新）

- 原本experiments/library/cpp/number/square_matrix.hppへ、確認済み最小候補を事前hash確認後に反映した。比較、不要な最終二乗、非負指数assertを修正し、pow(ll)、行参照、公開mat配列、aggregate/trivial/standard-layoutを維持。新hashは7ff812ae0566f16867e522c19c3ccc2b026d5f07f31da9ebe2fc658d3f7c72ab。今turnの元137件の修正はこの1ファイルだけで、過去の「137hash不変」はこの修正前の確認。
- tests/imports/square_matrix_source.cppを追加。既存候補の81行列/6561組の全操作・自己alias・境界powに、pow型/行参照/公開配列/trait、EqualityOnly、Countedの乗算回数を追加した。比較の旧negative compile期待を正常compileへ変更し、原本power/unaryも正常結果の回帰として実行する。element_countの元の不具合は未修正のため、従来のnegative期待を維持した。
- 実44307終了0。check_import_element_count.pyとcheck_import_square_matrix.pyで原本/C++候補を通常・ASan/UBSanで確認した。logsは.cache/wip/square_matrix_source_review/element_count_checks.txt、source_checks.txt。2原本検査の入力はproof auditの保護対象Proofs/verification/public headersと重ならず、進行中nanodaのexport/configは変更していない。
- 候補experiments/verification/number/square_matrix.hppもpowをlong longへ、matをメンバー初期化子なしへ戻し、追加の次元static_assertを外した。標準C++での正次元の前提は文書化。tests/imports/square_matrix.cppにpow型とaggregate/trivial/standard-layoutの回帰を追加。実6488終了0で候補の型と全ケースも通常・ASan/UBSanで確認した（最初の補助実行はclang_astのimport path不足で検査前に終了1、pathを直して再検査した）。
- 同6488で原本1ヘッダーだけを再走査し、18宣言・GCC構文passed・Clang scan passed。docs/verification_inventory.jsonのsource hash/declsを更新し、partial/既知bug fixed/C++・include確認だけを記録した。common_translator/lean_proved/publishedはFalseのまま。137fileのinventory --checkとtest_import_inventory.pyの5testsも終了0。ログは同cacheのinventory_refresh.txt、inventory_tests.txt、inventory_state.json。
- fixes表、findings、square_matrix_experiment、verification_inventory、experiments_statusを更新した。公開square_matrixのfree functionsから元のクラスへ戻す残件は維持し、C配列/非型テンプレート/行参照/初期化状態を変換器で扱う方針へ明確化した。公開matをvectorへ置換して終える案は採らない。クラス全体のLean正しさ・停止・UB不在・時間/領域の証明と公開は未完了。
- 最終監査実34545終了0、.cache/wip/square_matrix_source_review/final_audit.json。995Lean source audit、59/876/234/106の登録、固定2460roots/6140閉包と最新baselineのbyte一致、更新済み137fileのsource hash一致を確認。原本hashは上記7ff812...、候補の最終hashは5729e2641799a305c9e8a68a0fae5d9f209e23891697e8d55b010ebc28feb213。Python構文確認、変更ファイルの空白確認、git diff --checkも成功。最新の同28093の55秒pollでは独立kernelが稼働中で、まだ終了結果は回収していない。

## 現在の登録と固定仕様

### copy本体のlive領域と3種peak（2026-11-03・最新）

- scalarPeakBound/storagePeakBound/peakBoundは、初期状態のlive領域・peak・storage baselineと予算Wから上界を計算する。SpaceBoundsはbaseline保存、scalar/storage live、scalar/storage/全体peakをまとめ、各primitiveを加算予算で合成する。ready_space/source_copy_spaceと生成するcopy_space_of_fieldsは、初期Good/Sourcesから従来の全copy結果とSpaceBounds before after (copyWork before fields)を導く。scalar liveSはmemoryとbindingsを含む。nested StateのliveSpaceを使い子headerの二重計上を避け、baselineの飽和減算を維持した。
- 草案実59440は展開不足とvectorResultの明示不足で終了1。展開後の実27312は一括omegaが標準200000 heartbeatに達した。上限を上げずscalar/storage/全体の単調性と推移へ分解し、Nat.le_transの明示後に実99079が終了0、固定nanodaで **3082宣言** 成功（5.207秒）。失敗・timeoutは `.cache/wip/member_copy_peak/{first_*,arithmetic_timeout_*,monotone_first_compile.stdout}`、成功はstate.json/check.txt/exportに保存。
- 組込み後の実44387は共通部と既存UFの2検査が成功（独立 **3735宣言**）し、非0baselineの具体例のrecord改行構文だけが失敗。fixtureをletによるrecord構築へ直し、実71688は終了0、1test14.585秒。baseline=0/非0でscalar/storage/全体peakとwork増分18を確認し、C++ UBSanも成功した。実65597のBeats統合は終了0、1test72.854秒。一般17field copyの結果にSpaceBoundsを加え、従来の全14メソッド/構成子/descriptor一致、一般receiver証明、copy trace[6,5,6]とC++ UBSanも成功した。
- 最終監査実47728は終了0、同folderのfinal_audit.json。995Lean sourceと生成共通部/具体例/receiver/copy fixtureのsource audit、59公開/876共有modules/235checks/106docs、固定baseline byte一致、Python構文・diff確認を実施。生成共通部をMemberViewSupportAudit.leanへ保存し、docs/constructor_stage_methods.mdも更新した。基礎3公理のみ、標準stack/2threads/各120秒を維持し、新資源指定はない。全件gate72559は今回の証明追加前の結果である。
- copy本体の値・metadata・分離・仕事量・peakが揃った。任意caller AST、borrowed childを含む全保持、assignment/move/destruction、Beats child入力/Safe/任意長列/償却と公開切替、他の旧137件は残る。次の作業前に、上記利用者指示のリリースを進める。

### copy metadataと初期sourceからの正確な仕事量（2026-11-03・最新）

- Copiedのvector後置条件へcapacity=元要素数、limit=元limit、epoch=0、buffer.owner=binding.ownerを追加し、source/targetのKeepsと宣言順の合成を通じて最終ObjectCopiesへ引き継いだ。実行定義や公開C++/Lean正本は変更していない。既存wrapperはこの強化されたObjectCopiesを返す。
- fieldWork/copyWorkは初期sourceからscalar=2、vector=元要素数+3を合計する。初期SourcesとKeepsからfield_work_kept/copy_work_keptを導き、ready_workで各primitiveの実work増分を合成した。source_copy_workと生成するcopy_work_of_fieldsは、従来の成功/保持/値・権限・metadata/配置/確保数に、after.work=before.work+copyWork before fieldsまで返す。中間状態のサイズや成功を初期条件へ追加していない。固定幅要素のcopy本体の仕事量を扱い、fuel・実測時間やcallerの全体費用とは区別する。
- 草案実49432は未importのcongrArg₂とvectorResultの明示不足で終了1。単純な等式書換えと型の明示で修正し、実90348は終了0、依存 **3032宣言** が固定nanodaで成功（3.803秒）。`.cache/wip/member_copy_work/` にfirst_*の失敗、候補state.json/check.txt/exportを保存。資源上限は変更していない。
- 組込み後の実37836は3tests37.723秒・3682宣言の独立成功で終了0。その後、非0の初期workからのscalar差分、3vector/3scalarのcopy work増分18、reserve後のcapacity/epochからコピー先のcapacity=サイズ・epoch=0・limit保持を確認する例を追加。C++/UBSanでも予約後のコピーを確認した。最終の実50707は終了0、3tests38.060秒、共通部と具体例の独立 **3684宣言**。基礎3公理のみ、標準stack/2threads/各120秒、新資源設定なし。最終logはfinal_integrated_tests.txt。
- Beatsのcopy_from_owned_fieldsを新wrapperへ接続し、従来の一般入力からの17field copy、保持/metadata/配置/15owner・2cellの確保に正確なwork差分まで追加。実31084は終了0、1test77.947秒、同folderのbeats_test.txt。全14メソッド・構成子・descriptor一致、既存一般receiver/構築→更新→query証明、copy trace[6,5,6]とC++ UBSanも成功した。
- 最終監査実84340は終了0、同folderのfinal_audit.json。995Lean sourceと生成共通部/具体例/receiver/copy fixtureのsource audit、59公開/876共有modules/235checks/106docs、固定baseline byte一致、Python構文・git diff --checkを確認。独立検査した共通部と具体例はMemberViewSupportAudit.leanに保存し、docs/constructor_stage_methods.mdも更新した。全件gate72559は今回の証明追加前の結果である。
- 次はcopyのscalar/storage/全体peakと、borrowed childを含む任意caller保持、caller AST、assignment/move/destructionへ接続する。metadataや本体仕事量の成功を全寿命・全体資源の完成としない。Beats child入力/Safe/任意長列/償却・公開切替、他の旧137件の検証も継続する。

### copy先owner/addressの正確な配置と分離（2026-11-03・最新）

- MemberCopy.Position/Placementsは、宣言順の各fieldの実slot、vector binding/bufferのowner、scalar bindingのaddressと所有root scopeを記録する。ready_placementsは各primitiveのコピー先をtailのKeepsで保持して合成し、ready_countsはstorage objects数とscalar memory長の増分をvector/scalar field数へ一致させた。placements_atにより、各owner/addressを初期長+そのfieldより前の同種field数として取り出せる。
- vectorOwner/scalarAddressは実vectorSlot→typed resolve、またはscalarCellからIDを取り出す。vector_owners_distinct/scalar_addresses_distinctは異なるコピー先fieldの実IDが異なることを示し、vector_old_separated/scalar_old_separatedは初期storage/memory長未満の既存IDと重ならないことを示す。単なるslot番号の相違ではない。source_copy_positionsと生成するcopy_positions_of_fieldsは、初期Good/Sourcesだけから従来の成功・保持・値/権限対応にPlacementsと正確な確保数まで返す。既存wrapperの型、実行定義、公開C++/Lean正本/固定仕様は変更していない。
- 草案実70988はfilterのtrue側の簡約不足で終了1、List.filter_consを明示して実34956は2969宣言成功。分離補題追加時の実41119は帰納仮説の引数指定とunused simpで終了1となり、固定引数の整理後の実96648は終了0、配置と分離の5rootsの依存 **2994宣言** が固定nanodaで成功（3.757秒）。`.cache/wip/member_copy_fresh/` にfirst_*/rank_first_*の失敗とpositions_*の中間成功、最終state.json/check.txt/exportを保存。資源上限は増やしていない。
- 正本組込み後の実98803は終了0、3tests36.696秒。共通view/copy部と具体例の独立 **3618宣言**、複数vector/const/mutableコピーとC++ UBSan、既存UF全モデル一致を確認。許可は基礎3公理のみ、標準stack/2threads/各120秒を維持。Beatsのcopy_from_owned_fieldsへ新wrapperを接続し、一般入力から実17fieldのcopy・保持・値/権限・配置と、正確な15owner/2scalar cellの増加を導いた。実5668は終了0、1test74.554秒、全14メソッド/構成子/descriptorの一致、既存一般証明、copy trace[6,5,6]とC++ UBSanも成功した。
- 最終監査実27780は終了0、同folderのfinal_audit.json。995Lean sourceと生成共通部/具体例/receiver/copy fixtureのsource audit、59公開/876共有modules/235checks/106docs、固定baseline byte一致、Python構文・git diff --checkを確認。検査した共通部と具体例はMemberViewSupportAudit.leanへ保存した。docs/constructor_stage_methods.mdへ配置と分離の範囲を追記。全件gate72559はこれらの追加前の成功結果で、今回の変更後の全件再実行ではない。
- 次はcapacity/limit/epoch等のmetadataを含む一般class表現と、総仕事量/peak、任意caller AST、assignment/move/destructionへ進む。領域分離だけで全寿命や資源まで証明済みとしない。Beats child入力/Safe/任意長列/償却・公開切替、他の旧137件の検証も引き続き未完了である。

### copy先全fieldの値・権限と返却ObjectRef（2026-11-03・最新）

- MemberCopy.Copiedは元fieldの実読取りに対し、コピー先のtyped scalar値・権限、またはvector内容・権限・元caller scopeの所有rootを対応付ける。初期Sourcesが実読取りの存在を保証する。copied_source_kept/target_keptとready_keepsを使い、後続copyから先行fieldを保ってready_targetsへ合成した。中間状態の成功やコピー先の値を利用者の追加前提にしていない。
- FieldsCopiedは2つのリストを同じ順序で対応付ける帰納的述語。ObjectCopiesは宣言順からvector/scalarで選別した元field列と、返却ObjectRefの実slot配列を要素ごとに結び付ける。targets_at/selected_targets/targets_objectで、単なる所属関係ではなく配列順序まで示した。source_copy_valuesと各クラスに生成するcopy_values_of_fieldsは、初期Good/Sourcesから実copy成功・Good/Keeps・slot数/scope・ObjectCopiesを返す。既存copy_of_fields/copy_layout_of_fieldsの型、実行定義、既定1vector出力、公開C++/Lean正本/固定仕様は維持した。
- 草案実36535は終了1（rflで消去されたbinder名と未importのList.Forall₂参照）。明示的な変数消去と独自のFieldsCopiedへ修正し、実71480は終了0、2959宣言が固定nanodaで成功（3.302秒）。`.cache/wip/member_copy_values/` に初回first_*、修正後check.txt/state.json/exportを保存。Leanのエラー回復のsorry警告は失敗時だけのもので、成功・証明として扱わない。
- 組込み後の実50895は終了0、3tests37.150秒。共通部3384宣言の独立成功、3vector/3scalarのconst/mutable copyとC++ UBSan、既存UFの全モデル一致を確認した。tests/lean/member_copy_values.leanを追加し、readonly sourceからの正常copy、ObjectRefの順序入替えの拒否、コピー先権限の誤りの拒否を証明した。初回の具体例はGoodのDecidable推論/長さ正規化/未importのnorm_numで終了1となったため、定義に沿う単純な還元・具体的な不等値へ修正。実41332は型検査終了0・出力0bytes、実61249は独立 **3582宣言** と1test3.795秒で終了0。許可は基礎3公理、標準stack/2threads/各120秒を維持した。
- Beatsのcopy_from_owned_fieldsを新wrapperへ接続し、元の任意15所有vector/2scalarから、実17field copyと保持・配置・返却ObjectRef全fieldの値/権限/root scope対応まで導く。実81670は終了0、1test65.653秒、同folderのbeats_test.txt。全14メソッド・構成子・descriptor一致、一般receiver/構築→更新→query証明、copy trace[6,5,6]とC++ UBSanも同時成功した。
- 最終監査実69407は終了0、同folderのfinal_audit.json。995Lean sourceと生成共通部/具体例/receiver/copy fixtureのsource audit、59公開/876共有modules/235checks/106docs、固定baseline byte一致、Python構文・git diff --checkを確認した。検査した共通部と具体例の全文はMemberViewSupportAudit.leanへ保存し、docs/constructor_stage_methods.mdも更新した。全件gate72559はこれらの追加前の成功結果で、変更後の全件再実行とは扱わない。
- 次はowner/cellの非alias、各新fieldの正確なowner/address・capacity/limit等を合成して一般class表現を補い、総仕事量/peak、任意caller ASTとassignment/move/destructionへ接続する。ObjectCopiesの値・権限・scope対応だけで全寿命や資源まで証明済みとしない。Beats child入力/Safe/任意長列/償却・公開切替と、他の旧137件の検証も継続する。

### copy先のprimitiveと全copy配置（2026-11-03・最新）

- `verifier/class_copy_layout.py` のMemberCopy共通部へ5補題を追加した。scalar_destinationは新slotのtyped scalar読取り・値・権限・cell address、resolved_payloadは実resolveからpayload契約、vector_destinationは新slotからcopyBindingとコピー内容への実resolveを示す。ready_shapeは宣言順の全Readyからslot数のfield数だけの増加とscope不変を示し、source_copy_layoutは初期Good/Sourcesから実copy成功・Good/Keepsとこの配置条件まで導く。中間状態の成功・copy先表現は初期前提へ加えていない。
- 各opt-inクラスへcopy_layout_of_fieldsを生成し、実copyFields/copyFuel/返却ObjectRefへ配置条件を渡した。既存copy_of_fieldsの型と実行定義、既定の1vector出力、公開C++/Lean正本/固定仕様は変更していない。新規copy先の全fieldの値・権限を最終ObjectRefへ対応付ける合成と、新owner/cellの非alias、総仕事量/peak、caller AST/assignment/move/destructionはまだ残る。primitive成功と全copyの配置だけで一般class表現の完成とは扱わない。
- 草案の実20908はscalarStepのCppState.State.observe展開不足で終了1。資源を上げずその定義を追加し、実50444は終了0、補題5件の依存2870宣言が固定nanodaで成功（compile/export込み3.131秒）。初回の状態・ログは `.cache/wip/member_copy_destination/first_*`、修正後はstate.jsonとcheck.txtに保存した。候補check.pyは失敗時も状態をfailedに記録するようにした。
- 正本組込み後の実98496は終了0、3tests35.319秒。共通view/copy部の独立 **3317宣言**、3vector/3scalarのconst/mutableコピーとC++ UBSan、既存UFの全モデル一致を確認。許可は基礎3公理のみ、標準stack/2threads/export・kernel各120秒を維持し、新資源指定はない。logは同folderのintegrated_tests.txt。
- `tests/lean/beats_member_copy_proof.lean` は元の任意15所有vector/2scalarからのcopy成功・元読取り保持に、slot数+17とscope不変を追加した。実54183は終了0、1test68.523秒、同folderのbeats_test.txt。全14メソッド・構成子・descriptorの一致、既存の一般receiver/構築→更新→query証明、copy traceとC++ UBSanも同時成功した。
- 最終監査実82599は終了0、同folderのfinal_audit.json。995Lean sourceと生成共通部/一般receiver/copy fixtureのsource audit、59公開/876共有modules/**235checks**/106docs、最新固定baselineのbyte一致、Python構文・git diff --checkを確認した。独立検査した生成共通部はMemberViewSupportAudit.leanに保存した。docs/constructor_stage_methods.mdへ現在の暗黙copyの範囲と未証明の後置条件を追記した。
- 次はprimitiveのコピー先の値・権限・新slotを宣言順に合成し、tailのKeepsで先行fieldを保存して最終ObjectRefの全field表現を構成する。slot数/scopeやfuelと、値・非alias・仕事量/peakを区別する。旧137ファイル全体の目標は引き続き未達である。過去の「草案未型検査」「72559稼働中」はこの節で更新された。

### 初期sourceから全copy成功と元の読取り保持（2026-11-03・最新）

- MemberCopy.Good（frame wellFormed/rootWritable長一致）とSources（typed scalarCell、所有vector rootのslot/resolve/header/対応型）を定義した。sourceのwritableは要求しない。resolve_root_kept、vector_slot_prefix、scalar_keeps/vector_keepsを使い、copy/declareによる元のscalarと所有rootの正確なbinding/bufferの読取り保持Keepsを合成する。source_validatedに相当する実名はsources_validated。
- sources_ready/source_copy_completeは**初期Good/Sourcesだけ**から全中間状態のReadyと実copy成功・Good/Keeps保持を導く。中間状態の読取り条件やprimitive成功を利用者の前提に追加しない。各生成クラスのcopy_of_fieldsで、監査済みcopyFieldsとcopyFuel・実ObjectRefへこの証明を渡した。full copy先fieldの一般値/配置・仕事量/peakはまだ別の残件である。
- 実53168終了0/3tests23.694秒、`.cache/wip/copy_initial_source_final_regressions.txt`。共通部のsource_copy_completeまで固定nanodaで **3290宣言** が独立成功（基礎3公理のみ、標準stack/2threads/120秒）。3vector/3scalarのコピー独立性・const/mutable回帰、UF登録モデル全文一致も通過した。前段実93950は共通部3290宣言が独立成功したが、生成wrapper末尾のpureとfinishedのdefinitional equalityを閉じておらずtest終了1。rflで修正した。
- 新fixture `tests/lean/beats_member_copy_proof.lean` は、任意の15所有vectorのVOKG（writable/maximumの両方を関数引数としreadonlyも許す）と2scalarのtyped読取りから、targetConstの両場合の17field copy成功・元の読取り保持を導く。BRepや各中間状態の成功を前提にしない。実66711終了0/1test69.710秒、`.cache/wip/beats_copy_initial_sources_proof_fixed_test.txt`。全14メソッド・構成子・descriptorの一致、従来の一般call/構築→更新→query証明とcopy trace[6,5,6]のLean/C++ UBSanも同時成功した。初回64671は証明自体は通ったがunnecessarySeqFocus警告でtest終了1、`;`へ修正して警告なしにした。
- 最終監査実94437終了0、`.cache/wip/member_copy_initial_sources_final_audit.json`。995Lean sourceと共通部/一般receiver/copy fixtureのsource audit、59/876/234/106のregistry、固定baseline byte一致、Python構文確認・git diff --checkを確認した。共通部は `.cache/wip/member_copy_initial_sources/MemberViewSupportAudit.lean`（SHA256 8457980b6c73eebda91dec884a6d307b706f04ba8c98e1b834ac705ddfb2ee0c）。公開C++/Lean正本/固定仕様・資源上限は変更していない。
- 次は新規copy先の各fieldの値・slot/binding/owner配置と一般class表現を構成し、仕事量/peak、caller AST、assignment/move/destructionへ進む。元の全scalar/所有rootのKeepsと、borrowed child headerを含む任意callerの全保持は区別する。Beats child入力/Safe/任意長列/償却、公開切替、他137件も継続する。全件独立28093はstack overflow/終了1を回収済みで、冒頭の有界宣言別probeへ切り替えた。
- 2026-11-03の全件検査待機中に次の証明の接続先を確認した（まだ新しい証明は実装していない）。scalarコピー先のmemory/binding/slotは `CppClassCopyCommands.scalar_step_fields`、vectorコピー先の実resolveとpayloadは `CppFrameCopy.copied_resolve` を再利用できる。後者は `CppCopyStatementFacts.result` のrelease/chargeを正規化してMemberCopy.vectorResultへ渡す。宣言順の帰納法で各stepの新slotを元slots.length+ordinalと照合し、tailのKeepsで先行コピー先のtyped scalar/所有rootを保持すれば、最終ObjectRefに全fieldの値と権限を結び付けられる。新owner/新cellの非aliasと正確な配置、仕事量/peakは別途示す。既存source_copy_completeの成功だけからcopy先の表現を仮定しない。
- 同待機中に `.cache/wip/member_copy_destination/MemberCopyDestination.lean` へprimitive単位の草案を用意した。scalar_destinationは新scalar slotの型・値・権限・address、resolved_payloadは実resolveからpayload契約、vector_destinationは新vector slotと新copyBinding/コピー内容のresolveを述べる。**未型検査・未独立検証で、正本の生成器には未適用**。続けて `MemberCopyDestinationFull.lean` に現在のMemberCopy共通部と上記草案、Readyの帰納法によるslot数/scope保存、初期Good/Sourcesから実copy成功とこの配置条件まで返す草案をまとめた。両fileのsource policy監査だけは成功したが、**型検査・独立検証は未実行**。全件検査終了後はFullの草案を標準資源で検査し、その後に宣言順の全fieldの値・権限・非aliasと最終ObjectRefへ合成する。README.txtにも同じ保留条件を記録した。重い検査を並走させていない。

### 複数vectorクラスの暗黙copy命令とtyped Ready（2026-11-03・最新）

- member_exports経路にConstruction.copyFields/copyFuelを追加した。暗黙copyの監査済みFieldDeclの宣言順で、通常NStmtのscalar declare/vector copyを生成する。copy先の実slotも宣言順からObjectRefへ戻す。const sourceから通常copyを作る場合も新規root/cellはコピー先の宣言・const/mutableに従う。const viewの制限をsourceへ適用してコピー先までreadonlyにする処理ではない。既定の1vector経路と公開C++は維持した。
- MemberCopy.validateは全sourceのkind/type/slotを最初の確保前に検査する。後のfieldの不正slotが先行コピーで有効になる問題を防ぐ。invalid_sourceはcommandを実行する前のfaultを示す。command_complete/copy_completeは実primitive Stepsの宣言順合成を示す。Ready/ready_steps/copy_ready_completeは中間状態のtyped source cell/buffer、対応vector型、frame配置から各primitiveの成功を既存定理で導き、fields.length+1のfuelで合成する。**一般の初期クラス表現だけから全中間状態のReadyを導くことと、全copy後の一般表現・総仕事量/peakは未完了**。fuelを計算量とは扱わない。
- 実5805終了0/1test15.358秒、`.cache/wip/multi_member_copy_runtime_test.txt`。3vector/3scalarのconst source→通常copy→const copy、copy先だけのmutable更新、元の値・owner保持、宣言順の実slot、将来有効になる不正vector/scalar sourceの拒否をLean/C++ UBSanで確認。実26302終了0/3tests31.450秒、`.cache/wip/multi_member_copy_support_regressions.txt`で旧alias/void/growthとUF登録モデル全文一致も維持した。この時点のview/copy共通部は3072宣言の独立成功。
- Readyを追加した最終共通部は実35049終了0/2tests20.205秒、`.cache/wip/multi_member_copy_ready_tests.txt`。fixed nanodaは **3233依存宣言** を `Checked 3233 declarations with no errors`。許可は基礎3公理のみ、標準stack/2threads/120秒上限を維持した。CPPの同じ実コピー回帰も再確認した。CppClassCopyCommandsのscalar_run、CppCopyStatementFacts.completes、primitive_run/sequence_runを使い、primitive成功自体をReadyの仮定にしない。
- 新fixture `tests/lean/beats_member_copy.lean` を候補生成checkへ追加。実99183終了0/1test87.070秒、`.cache/wip/beats_member_copy_final_test.txt`。Beats実構築→15vector/2scalar copy→copy先query/chmin/query→元queryのtrace[6,5,6]をLeanとC++ UBSanで照合した。全14メソッド・構成子・descriptorの一致、6操作の一般Outcome等式と既存の構築→更新→query一般証明も同じ検査で成功。traceは有限実行回帰であり一般copy後置条件の証明とは区別する。前段実69249終了0/1test70.674秒、実11160終了0/1test79.302秒も成功済み。
- 最終監査実95266終了0、`.cache/wip/member_copy_final_audit.json`。995Lean source、view/copy共通部と一般receiver fixtureのsource audit、59/876/234/106のregistry、固定baselineのbyte一致を確認した。共通部は `.cache/wip/member_copy_support/MemberViewSupportAudit.lean` に保存（SHA256 06b87a87574f720df9d14934071c147e82cc565de7396722dade9a4a755ae398）。Python構文確認・git diff --checkも成功。公開C++/Lean正本/固定仕様・資源上限は未変更。
- 次は初期の一般source述語から、scalar_step_keepsやvector copyのFrame Extends/既存read保持を使って全Readyを構成する。その後、copy先の一般field表現・旧source保持・仕事量/peak、caller AST、assignment/move/destructionへ接続する。const参照view、Beatsのchild入力/Safe/任意長列/償却、他の旧137件も残る。最後の同28093pollは稼働中で、全件独立の終了結果は未回収。重複起動しない。

### 複数vectorのconst構築viewと一般権限証明（2026-11-03・最新）

- `class_copy_layout` のmember_exports経路へ `*_exportViewFuel(..., targetConst)` を追加した。構築本体の通常権限を保ち、終了時に各宣言のconst/mutableに従ってvector/scalarのviewを制限する。通常のexportFuelと既定のContext/copy profileは維持する。既存オブジェクトへのconst参照viewや任意caller ASTへの自動接続まで済んだものではない。
- 生成する共通MemberViewはrestrictVectors、finishView、constructViewFuelと一般定理を持つ。restrict_propertiesはowner/element/header不変、要求したwritable値、件数、権限非昇格を示す。scalarは既存CppConstructorView.restrictValuesを使い値/型を保持する。finishView_okは元のscope/prefix/field match/root Modelsと実permission制限から、終了成功・選択rootと無関係rootの保持・更新済みcallee prefixとfield値・元caller bindings/新規view flags/scopeを導く。finish成功自体は前提にしない。constructView_of_stepsは通常終端とbare returnの両方を扱う。
- 新test_member_view_support_independent_kernelはこの生成共通部の8定義・定理を別moduleへ型検査/exportし、未改変の固定nanodaへ渡す。実59343終了0/1test3.742秒、依存閉包 **3037宣言** を `Checked 3037 declarations with no errors`。`.cache/wip/member_view_independent_test.txt`。許可は基礎3公理のみ、2threads/標準stack、120秒上限、非0/不正な成功メッセージを拒否する。全件独立成功とは扱わない。
- 実74229終了0/3tests38.787秒、`.cache/wip/multi_member_const_view_complete_regressions.txt`。3vector(int/long long混在)/3scalarのconst構築、構成子中の書込みとreturn;、mutableのみの更新・通常fieldへのwrite拒否、通常viewと従来exportの同一結果をLean/C++ UBSanで確認した。別の2vectorクラスでは外部scalar書込み・元readonly別名の保持・new fieldsだけのconst制限も確認。従来UFの登録モデル全文一致も通った。最初の実44658はdeprecated if_pos警告によりtest終了1、ite_eq_leftへ修正後は警告なし。実27738は1test13.460秒、実92470は強化した一般権限/無関係rootの定理込み3tests36.551秒で成功済み。
- 実67603終了0/1test75.346秒、`.cache/wip/beats_member_const_view_regression.txt`。Beats全14メソッド・構成子・descriptorの一致、6操作の一般Outcome等式、生成構築→chmin→calc_maxの意味と更新後receiverの回帰を確認した。この後のconstructView_of_stepsのreturn場合一般化は上記74229/59343でも型検査・独立検査した。公開C++/Lean正本/固定仕様・資源上限は変更していない。
- 最終監査実28061終了0、`.cache/wip/member_const_view_final_audit.json`。995Lean source auditと生成共通部source audit、59/876/234/106のregistry、最新固定baselineのbyte一致、Python構文確認・git diff --checkも成功。独立検査した共通部のソースを `.cache/wip/MemberViewSupportAudit.lean` に同じ内容で保存した（SHA256 6f20249fb37bcab4e4717d47ae473e581665bef8e4517f1cba15191884362422）。最後の同28093pollも稼働中で、全件独立の終了結果は未回収。
- 次は既存オブジェクトのconst参照/任意caller AST、複数vectorのclass copy/move/assignment/destruction、export込み総資源、child header入力、Safe導出/任意長列/償却、公開切替と他の旧137ファイルの残件を進める。独立監査28093は同ハンドルで稼働確認済みで、終了結果は未回収。重複起動しない。

### 生成receiver引数と既存6操作Callの一般接続（2026-11-02・最新）

- `emit_member_methods` は各methodについてarguments_of_fieldsを生成するようになった。任意のvector/scalar slot列と外部引数数から実adapterの引数列を示す。fieldのscalarReference/元型のvariable式を保持し、値のghost置換はしない。実41620終了0、2vector/2scalarの任意slotのalias引数写像と従来のLean/C++ UBSanの一連の回帰を1test25.577秒で確認。`.cache/wip/multi_member_field_mapping_test.txt`。
- 最初のBeats回帰実24418終了0/1test88.019秒、`.cache/wip/beats_member_field_mapping_test.txt`。続く実70850終了0/1test77.205秒、`.cache/wip/beats_member_receiver_general_test.txt`ではvector slotを連続配置へ限定せず、任意写像slとして6つの生成callFuelと既存CallのOutcome全体の一致を証明した。receiver/fuel/引数式も任意。実構築のObjectRef=sourceReceiverのrfl一致も確認した。
- 新fixture `tests/lean/beats_member_receiver.lean` は、生成chmin→生成calc_maxの一般合成を型検査し、結果の数学的意味・Scalars/BVecsまで引き継ぐ。次のreceiverの成功や表現を仮定し直さず、1段目から導出する。元の4*n<2^31、各Safe/値域/添字の前提を維持する。任意長列・償却・総資源の証明へ拡大解釈しない。
- 同fixtureのgenerated_construct_update_queryは元callerの実root入力grantから、生成構築→生成chmin→生成calc_maxの一般接続を示す。実5626終了0/1test72.859秒、`.cache/wip/beats_member_construct_operations_test.txt`。構築成功/field reads/次receiverの表現を仮定せず、元の入力と各Safeから導く。最終queryの数学的意味・実ObjectRef・Scalars/BVecsを返す。全14メソッド/構成子/descriptorの一致と6つの一般Outcome等式も同じ回帰で再確認した。
- 実43699終了0、995Lean source auditに加えて新fixtureもsource audit成功。59公開/876共有modules/234checks/106docs、最新固定baselineのbyte一致を確認し、`.cache/wip/member_receiver_final_audit.json`へ保存した。Python構文確認・git diff --checkも終了0。公開C++/Lean正本/固定契約・資源上限は変更していない。最後の同28093pollも稼働中で、終了結果は未回収。重複起動しない。
- 次はsource bundleのconst view/copy/move/destructionとexport込み総資源、child header入力、Safe導出・任意長操作列・償却、公開切替/全件独立監査、他の旧137ファイルの残件を進める。今回の生成呼出しの一般接続だけで全体完了と扱わない。

### 複数vectorクラスの構築・メソッドbundle（2026-11-02・最新）

- `emit_context_class(..., member_exports=True)` を追加した。既定のContext/1vector copy profileは維持し、新経路は複数flat vectorとscalarが入り交じる元FieldDeclを監査し、型付き構築配置からmulti finishのexportを生成する。同じObjectRefのvectorSlots/scalarSlotsを実NProgramのfield引数へ渡すため、void更新やpush_backも既存評価器の対応範囲で扱える。receiverConst/引数数/各種field数を検査し、非const methodのconst receiver呼出しは拒否する。copy auditの複数vector指定は各宣言の監査用で、複数vector class copy実行の証明ではない。
- `class_copy_layout` の構築this helperも既存inlinerへ渡した。最初のBeats bundle生成（実57129終了1）はこの準備がなくstd::vector以外のmember callとして拒否された。修正後の実49549終了0で596108文字のbundleを生成した。全14メソッド（内部helper含む）と構成子を生成し、宣言を黙って落としていない。
- 標準深度での初回型検査実4095は終了1。apply_op/chmin/chmax/add_val/update_valのsequenceで深度超過し、後続のunknown identifier/sorry警告はこの失敗からのLeanエラー回復だった。成功・証明として扱わない。ログ `.cache/wip/beats_member_bundle_direct.txt`。資源上限は上げず、`share_commands=True` で同じ右結合の命令木を32命令ごとにprivate Commandへ分割した。新bundle生成は603119文字/67共有定義、実26561終了0。実72933終了0で標準上限のLean型検査が通り、ログ `.cache/wip/beats_member_bundle_shared_direct.txt` は0bytes。新経路はset_optionを出力しない。既定経路の出力は維持する。
- 分割前後のNProgram全体のrfl一致は、分岐の両側に70代入がある生成ソースで実11547終了0/1test11.129秒。`.cache/wip/constructor_command_sharing_test.txt`。2vector/2scalarの同じ実クラスで構築helper/参照引数更新/void更新/const query/field自身へのscalar参照alias/vector伸長のLeanとC++/UBSanも実51541終了0/1test22.332秒。`.cache/wip/multi_member_class_helper_test.txt`。
- 最終関連回帰のwrapper `.cache/wip/check_multi_member_regressions.py` は実78306終了0を回収済み。状態と各ログは `.cache/wip/multi_member_regressions/`。クラス9tests139.793秒、従来method6tests、copy audit7tests、構築配置4tests、multi finish5tests25.563秒の合計31testsが直列で成功した。wrapper側の各コマンド経過時間はstate.jsonに保存した。独立監査28093は同ハンドルで稼働確認済み、重複起動しない。
- 実37099終了0、追加Beats bundle検査1test61.729秒、`.cache/wip/beats_member_bundle_source_match_test.txt`。新bundleの構成子とBeatsConstructCall.program、全14メソッドと既存BeatsInstance、15vector/2scalarのdescriptorがすべてrfl一致した。生成出力にset_optionがないことも検査する。関連回帰は計32tests成功。実3522終了0で995Lean source audit、59/876/234/106のregistry、最新固定baseline全同一を再確認し、`.cache/wip/multi_member_final_audit.json` に保存した。共有bundle SHA256は0fb812bb365a39a57cb758d5cac435d7a4d9dcc9281937d51c410d697921cf93。Python構文確認・git diff --checkも終了0。
- 最後の同28093pollも稼働中で、独立kernelの終了結果はまだ未回収。次はこの同ハンドルの追跡を続け、新bundleの返却receiverから既存Beatsの6操作Call/更新後receiverへの一般接続、const viewとcopy/move/destruction、export込み総資源の未完了箇所を進める。全137件の目的をこのbundleの一致だけで完了としない。
- 公開C++/Lean正本/固定契約は変更していない。新経路の任意caller AST、const view、copy/move/assignment/destruction/総資源、child header入力、公開版への切替・全件監査、BeatsのSafe導出/任意長操作列/償却と全137旧ファイルの検証は未完了。

### 復帰後の構成子export生成（2026-11-02）

- 更新済みAGENTS.md・lessons・この引継ぎを確認して単独で復帰した。独立監査28093は同じ実ハンドルで生存を確認した。ログはexport完了後の独立kernel開始のままで、終了結果は未回収。重複起動・資源上限変更はしていない。
- 途中だった `verifier/nested_ir.py` の修正を確認した。構築段階の実fieldから型付きconstruction_layoutを生成し、opt-inの `emit_lean(..., constructor_exports=True)` でvectorFields/scalarFields/exportMembersFuelを出力する。既定のLean出力は維持し、テンプレート構成子exportは未対応として明示的に拒否する。既存class bundle全体やBeats公開版へ切り替えたものではない。
- `tests/test_cpp_constructor_multi_finish.py` に不正な配置情報の拒否・既定出力維持を追加した。実86356終了0、3tests14.355秒、ログ `.cache/wip/constructor_generated_export_all_tests.txt`。実C++の2vector/2scalar構成子から生成したexportのLean実行とC++/UBSan、参照引数の書込み・返却field参照を含む。docs/constructor_stage_methods.mdを更新した。公開C++・Lean正本・固定契約は変更していない。クラス全体のcopy/move/destruction・総資源と全137件の検証は引き続き未完了。
- 続く実32859終了0、候補生成1test34.584秒、`.cache/wip/beats_generated_constructor_export_test.txt`。Beats候補から生成した実15vector/2scalarのdescriptorと既存BeatsConstructorFields、および任意fuel/caller/引数について生成exportとBeatsConstructCallの構築・終了処理がrfl一致することを確認した。テスト内で手書きdescriptorを再構築する処理は除いた。既存のwide式・stage全文・非構成子全関数の一致も同じ検査で維持する。
- 実93387終了0、追加の入り交じるconst/nestedフィールド1test10.568秒、`.cache/wip/constructor_mixed_fields_test.txt`。const scalar/二重vector/mutable scalar/const vectorを宣言順に持つクラスの型付き配置・返却slot・scalar権限・vector権限・子buffer内容とwellFormedをLeanで確認し、C++/UBSanでも値・型・mutable更新を照合した。const vectorへのモデルwriteは失敗する。
- 実90651終了0、既存構築段階5tests39.957秒、`.cache/wip/constructor_export_stage_regression.txt`。公開Beatsの既定生成stage/本体が登録済みLeanファイルと全文一致すること、helper/alias更新、scalarのみのクラス、再帰拒否も通った。C++/Lean正本・固定契約はこのturnでも変更していない。次は既存class bundleの複数vector対応とcopy/move/destruction・総資源への接続を進める。現状の生成export一致だけでクラス全体の完了とは扱わない。
- 実32432終了0、証明監査器の全12tests14.984秒、`.cache/wip/proof_security_twelve_tests.txt`。先のprefix圧縮・stale生成物保管の追加2件も含む。実60586終了0、995Lean source audit・59公開/876共有modules/234checks/106docs・最新固定baseline完全一致を再確認し、`.cache/wip/constructor_export_final_audit.json` に保存した。Python構文確認・git diff --checkも終了0。最後の同28093pollは稼働中で、独立検査の終了結果は未回収。

公開59部品、共有876Lean modules/234checks/106docs。現在の固定契約は **2460roots/6140閉包**。

- 最新baseline: `.cache/wip/beats_aux_reviewed_statements_20261102.json`。`verification/statements.json`とbyte同一。旧 `.cache/wip/beats_caps_reviewed_statements.json`（2461/6141）は履歴として保持し、現在の完全一致baselineに使わない。
- compiler補題のレビュー: `.cache/wip/nanoda_declaration_probe/contract_root_review.json` と `.cache/wip/beats_old_root/aux_review.json`。名前付きの公開定理・計算定義の変更0。旧Separate._proof_1_3（WrM）は既存BeatsRep.wr_new0を再利用、旧Separate._proof_1_4（need上界100→112）は新Separate._proof_1_3へ移動、BeatsRep._proof_1_3は束縛名だけが変化。旧ソースを別module出力へ再構築して旧固定hashと一致することを確認し、Exprの束縛名だけを除く構造比較で3命題が保持されることを確認した。他のhash変更/追加/削除0。固定契約はこの自動生成のroot1削除/hash2更新だけを同期した。checkerの厳密なroot一致・型/定義hash・kernel検査は緩めておらず、--accept-changedも未使用。
- 監査器はInspectEnvironmentの出力をscratch/environment.jsonlへ保存し、1行ずつ解析するよう改善した。巨大なstdoutと解析表の重複保持を避け、失敗時にも宣言一覧を残す。重複拒否は維持し、root不一致エラーにはmissing/addedを表示する。security10tests成功。
- 最終軽量監査は実32064終了0、`.cache/wip/aux_fenwick_final_audit.json`。995Leanファイルsource audit、59/876/234/106のregistry、2460/6140の最新baseline一致、Fenwickの実headerと登録hash一致、元137ファイルのhash不変を確認した。git diff --checkも終了0。SquareMatrixの元ファイルはまだ変更していない。

- 以下は容量分離の追加時点（2461/6141）の履歴。baseline: `.cache/wip/beats_caps_reviewed_statements.json`
- 旧2419roots/6090閉包から追加のみで、既存hashの変更/削除0。追加42rootsはProofs.BeatsSeparateの15Fresh projections、Env、7公開Call、19補助proof。
- review: `.cache/wip/beats_caps_contract_review.json`。`--accept-changed`は使っていない。
- この後のslot/index補助・実構築stageはsupportへの追加で、現JSONはbaselineと全同一をassert済み。現在は上記のauxレビュー後baselineを使う。過去の2417/6088や2419/6090も完全一致baselineには使わない。
- 最新の全59件bridgeは実81615終了0、log `.cache/wip/constructor_stage_all_bridge_retry.txt`。初回53629は全体240秒で38件後timeout。同じ制限で成功cacheを使って残りも検査した。全件all/230checks/独立kernel成功ではない。

## Beatsで登録済みの証明と生成

[部品doc](../segment_tree_beats.md) と履歴に詳細。

1. `BeatsCapCtor/Chmin/Update1/Update2/Update3/Calc` はnode容量Lとstack容量Sを分離する。中点分割Shapeから高さを抑え、実stack256で構築/全6操作の生成本体・表現保存を扱う。
2. `SegmentTreeBeatsCall.lean` の `Proofs.BeatsSeparate` 名前空間に構築/全6操作の公開Callを追加した。旧 `Proofs.BeatsRep` 側は保持。準備/正常終了/意味/caller保持/仕事量と領域を含む。
3. 旧Lensは全stackにもLを要求し、L≥8*n+8からn≥32の実状態と矛盾した。新BRepS/BFreshSはSを分離してこれを避ける。n=32/L=264/S=256の生成構築とFresh条件を `test_beats_capacities.py` で確認済み。
4. 実初期化を含む `Proofs/Generated/BeatsConstructionStage.lean` を登録。readonly入力aはslot0、15vector fieldsはslots1..15、inf/nは16/17。先頭15fillVector後の本体は旧bodyのvector slots i<16を(i+1)%16へ写したIRと完全一致する。scalar slots16以降は同じ。実ソースとの全文生成一致・型検査を要求する。[構築stageの範囲](../constructor_stage_methods.md)。
5. `BeatsSlotCycle.lean` は16slotsの置換/逆、typed scalar/vector読取り、envOf、payload/仕事量/peak/slot数の保存を示す。`CppSlotRename.lean` は任意添字写像の式変換、scalar補助denote・nodes/scalarOnly保存を示す。**BeatsSlotEval/Stmt/RunでContainer/NExpr全構文のevalと、CoreCommand範囲のrunFuelまで接続済み**。実wide構築本体がこの範囲に入ることも証明済み。[範囲](../beats_slot_cycle.md)。BeatsInlineFrame/Execで実15確保・初期Frame・インラインstage全文の実行/表現まで接続済み。
6. BeatsAllocation/Layout/ArgsとBeatsInlineFrame/Execで実15確保、BFreshS/CVecs、実FrameのFWM/QSとインラインstage全文の正常終了/表現/全16buffer内容を合成済み。root入力のreadonly prepareまで接続済み。確保とroot prepareを含む仕事量/peakも接続済み。child header入力、class export/copy/move/寿命とその資源、公開版切替、独立監査/全件allは未完了。償却O(log² n)も未証明。

## 元の入力範囲へ戻す構築候補（今回の主な前進）

**公開版の入力範囲縮小はまだ未解消**。元は4*n確保で、n=2^28なら4*n/2*n0/木添字はi32内。一方公開版の8*n+8はi32を超える。違反一覧・findings・部品docに記録し、巨大配列なしの算術回帰を追加した。8*n+8<2^31を前提にするだけで完了としない。

- 候補: `experiments/verification/segment_tree_beats_wide.hpp`。12本の確保長と、構成子の全4*n走査で使う子添字2個だけをunsigned 64-bit化。公開ヘッダー/生成モデルは未切替。
- 操作側まで広げた初期案は `.cache/wip/segment_tree_beats_wide_broad_20261101.hpp` に保存した。**現候補へ戻さないこと**。高さを使うと操作側のint子添字は元のサイズ範囲で安全なので、この変更は不要だった。
- `Proofs/BeatsIndexHeight.lean` を登録。`idx_of_height`、`original_range_child_indices`で4*n<2^31なら全実節点の子添字がINT_MAX未満と証明。constructor走査のk/intと8*n+8≤2^32の境界、`idx_min`、`Capacities.shrink`、`BRepS.cap_indices`も証明。
- 既存の操作証明には、物理配列長がint上限を超えても、BRepSの下界をmin L INT_MAXへ縮めて渡せる。データ・意味・S・資源を変えない。構築の成功自体を仮定して解決済みとはしない。
- `tests/test_beats_wide_candidate.py` 3tests成功: 既存3000×60操作+大値の通常/ASan/UBSan、巨大配列なしの境界、実候補のstage/body生成・Lean型検査。構成子以外の全生成関数は公開版と完全一致する。実93348終了0、3tests28.587秒、log `.cache/wip/beats_wide_candidate_test.txt`。
- index補題の最終build実46107終了0/1039targets、新module警告なし。最新容量回帰実27886終了0/1test2.023秒、log `.cache/wip/beats_wide_capacity_test.txt`。実使用配列を大きく確保した検査ではない。
- [候補doc](../beats_wide_candidate.md)。Cpp候補の全範囲構築実行/意味/資源証明は未完了。構成子だけが変わるため、次はphase1でn/kのi32境界と64-bitの確保長/子添字を分離する。phase2のentered nodesには数学的な実木のidx境界を渡す。6操作の実行モデルを変更せずに接続する方針。
- `Proofs/BeatsWideExec.lean` を追加登録。u64の変換/literal/cast/localと、実候補の `2ULL*(unsigned long long)k+d` の補助評価を証明した。元の4*n範囲と走査位置から、wrapなしの数学的な値と確保長内の境界を得る。子添字にint上限を課さない。実ソースの2つの生成式と定理中の式のrfl一致、INT_MAXを超える4294967288の境界例も既存候補テストへ追加。新module build実30156終了0（871targets、新module警告なし）、候補3tests実26161終了0/27.976秒、log `.cache/wip/beats_wide_exec_test.txt`。構築ループ/命令列全体への接続はこれからであり、公開Cppは未変更。
- 同moduleの `vden_wide_count` は実入力vectorの長さから `8ULL*a.size()+8ULL` を評価する。元の4*n<2^31の範囲でsize/unsigned cast/積/和/最後のcastを扱い、実stageの12本すべての確保長式と `wideCount 0` のrfl一致を追加した。n=536870911で長さ4294967296を得る抽象vectorの回帰例も成功（巨大確保なし）。最終build実94529終了0/871targets、新module警告なし、候補3tests実3901終了0/26.335秒、log `.cache/wip/beats_wide_count_test.txt`。初回91931終了1は境界例のsimp onlyが数値式を簡約しなかったためで、通常simpへ修正して再検査した。registry/source audit/diffcheck成功、公開仕様baseline全同一。確保自体の成功/費用・初期表現・ループ全体は未完了。独立20457は当時稼働中だったが、後にstack overflowで終了1。詳細は冒頭。

### wide構築の最初の走査まで接続

- `BeatsExec_WideCtLoopDefs/Ch0..12` と `BeatsExec_WideCtLoop` の15modulesを追加。候補の49命令を最大4命令ずつ13補題に分けた。pexecMでの1回の走査について正常終了・状態/配列・仕事量≤20580・storage work≤12を示す。u64 localへのcast付き添字も `den_idx64u_cast` で扱う。**新16modulesにmaxRecDepth/maxHeartbeats/maxMemoryの指定はない**。旧生成補題の上限設定はコピーしていない。
- `Proofs/BeatsWideCtorLoop.lean` に `ct_iter_wide` と `ct_loop_wide` を追加。CtInvから1回の実行条件を導き、更新後のCtInv・ValidOK・分離したCapS・lo/hiの長さを保つ。残りd回の最初のwhileを停止まで合成し、fuel≤d+1、仕事量≤d*20620+20、storage work≤d*12。物理配列長L<2^31の仮定を外し、**4*n<2^31**を使う。旧ct_iter_separate/ct_loop_separateは変更していない。
- 正本build実80293終了0/889targets、実99454終了0/1055targets、新modules警告なし。logs `.cache/wip/beats_wide_vc/canonical_build.txt` と `phase1_build.txt`。候補3testsの最終実78758終了0/27.564秒、`phase1_candidate_test.txt`。通常/ASan/UBSan・算術境界に加え、候補ソースの49命令と条件/scopeを含むwhile全体が正本定義とrfl一致することを確認。registry/source audit/diffcheck成功、公開仕様baseline全同一。
- 試作用の生成器/モデルは旧cacheを保ったまま `.cache/wip/beats_wide_vc/` に分離。草案は全13chunks/mainとも標準上限で終了0。正本では未使用の引数名/simp引数/tryを整理して警告も除いた。
- 残りは後半のentered nodesの集約処理、実確保から初期CtInv/Frameを作ること、実caller/runFuel/export/寿命と構築全体の資源、公開版切替・独立監査。phase2で使うentered indexが実木の節点であることを示し、`BRepS.cap_indices` 等のint境界を接続する。最初のwhileの補助実行モデル上の証明だけで構築全体を完成扱いにしない。独立20457は当時稼働中だったが、後にstack overflowで終了1。詳細は冒頭。

### wide構築本体・表現まで接続済み（最新）

- `Proofs/BeatsWideCtorExec.lean` を追加。`rngOf_index` の既存の不等式から、内部節点eなら **2*e+2<4*n** を導く `inner_children_lt_four_n` が得られた。CtInv/mem_LLrがentered listの内部節点条件を与えるため、phase2へは `C=min L 2147483647` を渡せばよい。4*n≤C、各子添字<C、ne≤C、Capacities.shrinkを示し、既存ct_upd_all_separateを変更せず再利用した。SameLenで結果の物理容量Lを戻す。**phase2のための新しいInSk対応証明は不要だった**。
- `ct_exec_wide` は両ループと本体初期化を合成し、WideCtorCmdの正常終了、HRel/数学的な木との一致、ValidOK/分離容量/lo/hi/LenOK、仕事量≤4*n*45414+100、storage work≤4*n*18+10を示す。`ctor_rep_wide` は高さ/添字を加えてBRepSとneed≤P.length+100を構成する。L<2^31は使わず、4*n<2^31を使う。新moduleに資源上限指定はない。Nbを一括decideした草案15909は再帰深度に達したので、構文別のsimpへ変更し、上限もneedの100も増やさず解消した。
- 正本build実59903終了0/1057targets、新module警告なし、log `.cache/wip/beats_wide_vc/exec_build.txt`。候補3testsの最終実35478終了0/27.664秒、`exec_candidate_test.txt`。実候補の全文生成構築本体とWideCtorCmd 16のrfl一致を追加。記号的な実初期配列から任意の元サイズ範囲へctor_rep_wideを適用するfixtureと、n=2^28/L=2147483656の論理的な境界例も成功（巨大配列を実確保/走査した検査ではない）。registry/source audit/diffcheck成功、公開仕様baseline全同一。
- **公開Cpp/modelは未切替**。残件は実15確保からFrame/初期表現を構成すること、slot置換のeval/runFuel全体、実caller/export/copy/move/寿命と確保費用、公開定理・生成モデルへの切替/独立監査/全件gate。旧公開new0の証明は旧source bodyへの依存があるため、切替時にはimportの循環を避ける整理と、固定仕様の変更箇所の明示的なレビューも必要。独立20457は当時稼働中だったが、後にstack overflowで終了1。詳細は冒頭。

## 共有変換器の修正と検査

### スロット置換の状態付き式評価

- `Proofs/BeatsSlotEval.lean` を追加登録。EvalRelは、renameした評価結果の状態置換と元の式の評価の一致、および評価中のslots不変を組にする。bind/precharge/変換/Frame操作を合成して、**Container/NExprの全構文**（row/size/read、cast/targetCast/unary/binary/divrem/短絡logicalを含む）を相互再帰で証明した。`container_eval_permute` / `expr_eval_permute` はOption全体の等式、`expr_fault_permute` は失敗の同値。成功やwellFormedを仮定せず、16slotsの存在だけを要求する。Frameの新binding、権限・参照先・全カウンタも対応する。
- 新module build実15428終了0/32targets、新module警告なし、log `.cache/wip/beats_slot_eval_build.txt`。新規登録 `tests/test_beats_slot_eval.py` 1testは終了0/0.968秒、log `.cache/wip/beats_slot_eval_test.txt`。異なる16vectors+末尾scalarの複合read/size、範囲外read、短絡で失敗右辺を飛ばす式、rowの新bindingとsize/readを実評価し、結果状態全体とカウンタ等を照合する。初回はテストのmap内でPropをBool化していなかったため失敗し、decideを付けて修正した。
- 宣言/書込み/scope/while/runFuelは未接続。次はrotateとslots末尾追加、release/declared/leftの対応を示し、Beats構築本体で使う命令列へ式評価の定理を適用する。独立20457は当時稼働中だったが、後にstack overflowで終了1。詳細は冒頭。

### スロット置換の宣言・代入・書込み・scope終了

- `Proofs/BeatsSlotStmt.lean` を追加。rotate_append、release_permute、declared_permute、enter_permute、**leave_permute**を証明。leaveはscalar prefix型検査、戻りvectorの移譲とscope破棄を含む実定義に対し、任意の戻り値でOption全体が対応する。leave自身に16slotsの前提は不要。状態のrecord projectionsを明示化せずifをrewriteするとDecidable側の表現が揃わなかったため、outer/innerを構成要素へ分解して解消した。
- declare_run_permute / assign_run_permute / write_run_permuteはNStep全体の対応。宣言の末尾slotとscalar追加、writable/変換失敗を含む代入、右辺先行評価→container→index→elementRef→実Frame.write→release→chargeまでを扱う。値だけの一致や成功前提にしていない。新moduleに資源上限指定なし。
- 正本build終了0/35targets、新module警告なし、log `.cache/wip/beats_slot_stmt_build.txt`。既存登録test_beats_slot_eval.pyを2testsに拡張し、最終実32010終了0/2.007秒、`beats_slot_stmt_test.txt`。宣言先slot17と値、通常/readonly/型変換失敗の代入、対象vectorの実更新と他vector保持、row書込み後の一時binding除去、scope終了によるslot/scalar復元とprefix失敗を確認。新fixtureは `tests/lean/beats_slot_stmt.lean`。
- 次は命令のrename定義と、Beats本体で使うprimitive/sequence/scope/branch/whileのrunFuel対応を合成する。full statement/command一般の意味保存、vector確保命令、実15確保からのFrame/初期表現とclass export/寿命は未完了。独立20457は当時稼働中だったが、後にstack overflowで終了1。詳細は冒頭。

### スロット置換のrunFuelとwide構築本体（最新）

- `Proofs/BeatsSlotRun.lean` を追加登録。CppSlotRename.stmt/commandは構文の置換を定義するが、意味対応は **CoreStmt/CoreCommand** で範囲を明示する。skip/declare/assign/write/check/ret/retVector/retUnit、sequence/scope/branch/while/breakを扱う。vector確保・reserve/append/copy等とinvokeScalarは述語が拒否し、一般全構文を証明済みとはしない。
- stmt_long/run_longは成功後も16slotsを保つ。**run_permuteは任意のfuelで、正常終了・fault・exhaustedの全Outcomeを対応させる**。outcomeViewは状態だけをpermuteし、return/breakの制御情報を保つ。成功だけを前提にせず、scope復元とloop継続も扱う。全新補題は標準資源上限で通過した。
- BeatsWideCtorExecにwide_ctor_core/wide_ctor_cycle_runFuelを追加。実WideCtorCmdがCoreCommandの範囲に入ることを証明し、その本体へrunFuelの対応を適用した。候補ソースの15確保後の全文が **CppSlotRename.command cycle (WideCtorCmd 16)** とrfl一致する生成回帰も追加した。
- 最終build実97387終了0/1062targets、新moduleと変更module警告なし、`.cache/wip/beats_slot_run_build.txt`。slot回帰3tests実65991終了0/3.129秒、`beats_slot_run_test.txt`。毎回localを破棄するloopの実配列更新、break/return後の無効check省略、branch fault、有限fuel/無限loopのexhaustedを確認。候補3tests実20062終了0/28.083秒、`beats_slot_run_wide_test.txt`（通常/ASan/UBSanと実stage本体の命令置換一致も含む）。registry/source audit/diffcheck成功、公開仕様baseline全同一。
- **次は実15確保からFrame/16slots/初期表現を構成し、上記の状態付き本体へ接続する**。確保を含む全体資源、class export/copy/move/寿命、公開Cpp/modelへの切替・固定仕様レビュー、独立監査/全件gateは残る。独立20457は当時稼働中だったが、後にstack overflowで終了1。詳細は冒頭。

- `ast_stream.class_construction_stages` に宣言順の実field局所変数 `_all_fields` を付け、direct_functionsから同じClang IDのhelperをcommon inlinerへ渡す。helper自体は出力rootにしない。
- `_read_only_fields` は可変scalar参照引数があるクラスでscalar値渡し最適化を行わない。inspect(count)がcountを9にしてから読む例で旧値5を返す不具合を確認し、参照保持で修正した。
- 新規constructor-stage5tests、UF構築3tests、constructor layout1test、Context methods6testsが直列実97944終了0。既存UFモデルのbyte/rfl一致も維持。ログ名は `constructor_stage_methods_test.txt` と `ctor_stage_{uf,layout,context}_regression.txt`。
- registry/source audit/git diff --check成功。Cpp public sourceはこの作業で変更していない。fixes表のwide候補は「候補のみ・公開未反映」と区別している。

## 次の作業と全件の残件

### 6操作後のBVecs/Scalarsと次receiverの復元（2026-11-02・最新）

- `Proofs/CppCallUnitFrame.lean` を追加登録。既存CppCallFrameのscalar-result用call_headersをunit-resultへ拡張した。NoResizeScope.Allowed、callerの全context上界、実prepare/body/finish成功からCallEffects（全buffer headers・flags・vector/scalar bindings・slots・scope・base・memory長・scalar live）を導く。finish_unit_frameは戻りnone/some unitを扱う。scalar値不変は主張せず、参照引数への更新も許す。旧CallEffects/CallFrameの型・証明は変更していない。
- `Proofs/BeatsReceiverRestore.lean` を追加登録。scalar_cell_eq/scalars_keptはCallEffectsと明示的なmemory等式から、任意slotのscalarCell同値とINF/nの読取りを導く。restore_bvecsは更新後payloadとwellFormed、SameHeadersのlimit/size等、flags/bindings/scope/baseから新BVecsを導く。更新後BVecsを前提にしない。
- 6操作の同名拡張定理（新namespace）を追加。従来のprepare/callFuel成功・query/更新意味・BRepS・ScalarPostMBを残し、CallEffects・Scalars・新buffer familyのBVecsも返す。unit4種は新helper、scalar2種は既存call_headersを使う。各Safe/i32境界/x値域は従来どおり明示前提で、物理L<M31を要求しない。元4*n範囲と操作用min L INT_MAXを保つ。
- Allowedの更新4関数の一括simp/decideとcanonical ApplyOpCmd/ALoopの一括rflは標準再帰深度に達した。上限を増やさず、SimのAllowed保存、W6/初期化/ALoop/ULoopの合成と既存ApplyLoop14chunksの小補題へ分割して解消。query2種は標準decide成功。初回6拡張headerではCppNestedEvalのopen不足でenvOfが未解決だったため明示した。新2modulesに資源上限指定なし。
- 正本最終の直列実88157はbuild1187targetsと新2modules direct型検査を終了0で回収。新module警告0、direct出力各0bytes。build `.cache/wip/beats_receiver_restore_build.txt`、direct `cpp_call_unit_frame_direct.txt` と `beats_receiver_restore_direct.txt`。unit helper初回の未使用liftChecked simp引数2個を除いてから最終build/directを確認した（実装の挙動変更なし）。
- 新fixture `tests/lean/beats_receiver_restore.lean` は任意receiver/区間/値と従来Safeからchmin出力のScalars/BVecsをcalc_maxへ渡し、意味と次BVecsを導く。更新後receiverの成功・表現を追加前提にしていない。`tests/lean/cpp_call_unit_frame.lean` はvectorを書き換え、scalar参照引数7→9とreadonly aliasへの反映、bindings/slots/epoch/limit保持、none/some unitのfinish一致・型違いreturn拒否を確認。metadata保持だけから値不変を誤推論しない例でもある。
- 既存のreceiver method trace checkに2fixturesを追加し、単独実93835終了0/1test22.551秒、`.cache/wip/beats_receiver_restore_test.txt`。C++/UBSanとの同一objectの6操作trace照合も含む。全回帰実11949終了0/10tests70.191秒、`.cache/wip/beats_receiver_restore_allocation_tests.txt`。candidate生成一致検査へ新moduleをimportし、実99067終了0/1test24.502秒、`.cache/wip/beats_receiver_restore_source_test.txt`。新2modulesのwarning除去後には最終build/directを再確認し、実行コードが変わらない全runtime回帰の重複はしていない。
- registry（59公開/876共有modules/234checks/106docs）、995Leanファイルsource audit、公開仕様baseline全同一、git diff --check終了0。公開C++/生成モデル/固定仕様は未変更。全件all/独立nanodaは再実行せず、旧new0のstack overflowも未解消。追跡中の検査プロセスはない。
- **次は各Safeを明示した任意長操作列の意味・総資源の合成、または公開切替に残るconverter/寿命と独立new0の改善**。各stepのBVecs/Scalarsは復元できたので、旧stateを仮定し直さず次callへ渡せる。全操作列の一般証明はまだなく、現在の一般検査は2段階、実traceは固定有限列。CallEffects.transは全headers/metadataを合成する基礎として使える。配列下界min L INT_MAXの反復はidempotentとして整えるとよい。各Safeの一般入力からの導出、constructor export込み/操作列/寿命の仕事量・peak、全無関係vector内容保持、child header入力、class converter/copy/move/destruction、公開版切替・固定仕様レビュー、旧new0の独立stack overflow解消と全137旧ファイルの検証も残る。


### 実scalar fieldsを読む6操作の呼出し（最新）

- `Proofs/BeatsReceiverCalls.lean` を追加登録。infExpr/sizeExprはbase+15/base+16の実variable式で、Scalarsは実scalarCellの成功を保持する。scalars_of_layoutとconstruct_argumentsは元callerからの実構築成功・BRepS・BVecsと同時にScalarsも導く。inf_denote/size_denoteはenvOfからINF/nを読み、構築時定数への置換をしない。
- chmin/chmax/add_val/update_val/calc_max/calc_minの6定理を追加。2field式と任意scalar-onlyなqa/qb/x式を既存の生成NProgramへ渡し、実prepare/callFuel成功、query/更新意味、更新後BRepS、ScalarPostMBの全結果（caller memory/slots/scope・配列内容・仕事量とpeak等）を引き継ぐ。従来の各Safe・qa/qbのi32境界・x値域を明示前提として保つ。物理容量L<M31は要求せず、4*n<M31からBRepS.cap_indicesでmin L INT_MAXへ**操作用の下界だけ**縮める。実buffer/入力範囲を狭めない。
- 正本最終build実82778終了0/1176targets、新module警告0、`.cache/wip/beats_receiver_calls_build.txt`。初回草案は不要なCppRootModelのopenでHeapがBT用Heapと衝突したため除去した。新moduleに資源上限指定なし。旧6定理や公開C++/生成モデル/固定仕様は変更していない。
- 新fixture `tests/lean/beats_receiver_calls.lean` と既存確保checkの1methodを追加。1つの実prepare→構築→exportの状態からquery2種、chmin/chmax/add_val/update_valとqueryを続け、毎回INF/nをfieldから読み、更新後状態を次の呼出しへ渡す。結果[6,5,5,5,8,3,7]と元scalar別名/slots/bindings/input bufferの保持、wellFormedを確認。同じtraceをtemplate-first includeした候補C++/UBSanで照合する。nのcellを2へ実代入するとsizeExpr.denoteも2になる例でghost定数化を検出する。単独実34806終了0/1test20.489秒、`.cache/wip/beats_receiver_calls_test.txt`。
- 確保/構築/操作の全回帰実25701終了0/10tests64.140秒、`.cache/wip/beats_receiver_calls_allocation_tests.txt`。candidate source一致検査にも新moduleをimportし、stage/program/descriptor・非constructor全生成関数の旧モデルとの一致を検査。実45997内で終了0/1test22.903秒、`.cache/wip/beats_receiver_calls_source_test.txt`。同じ直列実45997の新module direct型検査も終了0・出力0bytes、`.cache/wip/beats_receiver_calls_direct.txt`。ヘッダー単独Clang AST取得時の既存#pragma once警告のみ。通常/ASan/UBSanの全3000×60操作は今回は再実行せず、既存記録を保持した。
- registry（59公開/874共有modules/234checks/106docs）、993Leanファイルsource audit、公開仕様baseline全同一、git diff --check終了0。全件all/独立nanodaは再実行せず、旧new0のstack overflowも未解消。追跡中の検査プロセスはない。
- **次は一般の更新後receiverの復元と操作列**。6wrapperは各Safeを従来どおりの明示前提とし、一般入力からのSafe導出は未完了。runtime traceの複数操作の成功を、任意長の操作列の一般証明とは扱わない。ScalarPostMBはscalarMemory・slots・scope・vector bindings・配列items等を返すが、scalar bindings/base・root flags/strict・buffer limit/Validを次のBVecs/Scalarsとしてすべて返す型ではない。実call/finishのmetadata保持、最終FWMの追加結果を別の拡張補題で取り出して、既存公開型を保持しながら次の入口へ渡すとよい。scalarCell条件の保持を先に一般化すればfield式の読取りを継続できる。constructor export込み総資源、全無関係vector保持、child header入力、class converter/copy/move/destruction、公開版切替と独立監査/全137旧ファイルも継続。


### export後のbuffer契約・全scopeと6操作用BVecs（最新）

- `Proofs/CppConstructorRetirement.lean` を追加登録。retired_context_someはwell-formedなforestで退役後に残るroot/子vectorのcontextが元と同じで破棄scopeとは異なることを示す。context_noneとownerの強帰納法を使い、未知ownerのrootOwnerを再帰simpし続けない。movedFrame/movedAll_scope_leとfinished_scope_leはroot移譲→callee scope破棄後の全ownerのscope上界を導く。finished_bufferは選択rootの**buffer全体**（items/capacity/limit/epoch/owner）の保持を示す。最終helper buildは実コマンド終了0/120targets、`.cache/wip/constructor_retirement_build.txt`。草案のparentOKのprojection前の明示展開と、一般Models.tagの名前空間指定を修正した。資源上限指定なし。
- ExportLayoutへFieldBuffersとstrictを追加。finish_from_layout_fullは最終FWMの各field bufferのValid/標準limit/owner/内容長<2^64を実退役後まで保ち、scopeも最終FWM/QSと実移譲・破棄から導く。元callerへ新条件を追加しない。congr_fieldsとconstruct_fullもこれらを保持する。最終FWMにある契約をexport後へ仮定し直す形にはしていない。
- BeatsConstructReceiver.field_buffer_factsは実lookupから選んだfieldBufferと、Modelsが持つpayload bufferが同一であることを照合する。receiver_bvecs/construct_readyは元callerから構築成功・BRepS・既存6操作の**BVecs全条件**を導く。返却slots/bindings、相異なるowner、writable/max grant、実lookup、Valid/limit/owner/small、全scopeのstrictとscalar baseを含む。ctyと操作用btyはi<15で一致。最終build実85271終了0/1175targets、`.cache/wip/beats_receiver_bvecs_build.txt`、新/変更modules警告0。
- 新fixture `tests/lean/cpp_constructor_retirement.lean` を既存roots checkに追加。nested rootとflat rootのbuffer全体保持、退役対象とは異なる大きいscope8のrootもcontextを保持する例、一般finished_scope_leを確認。実82955内で終了0/1test1.154秒、`.cache/wip/constructor_retirement_test.txt`。
- 既存receiver fixtureへ、実prepare→構築→export後の全15bufferのValid/limit/owner/small、全ownerのscope上界・base、および一般callerでconstruct_readyからBRepS/BVecsを同時に得る例を追加。単独実82955内で終了0/1test11.613秒、`.cache/wip/beats_buffer_contracts_test.txt`。確保/構築全回帰も実9472終了0/9tests43.498秒、`.cache/wip/beats_buffer_contracts_allocation_tests.txt`。
- 生成モデル一致・candidate stage/program/descriptorの型検査は直列実1466内で終了0/1test23.026秒、`.cache/wip/beats_buffer_contracts_source_test.txt`。同じ実1466で新helper/BeatsConstructorFields/BeatsConstructCall/BeatsConstructReceiverのdirect型検査も終了0・各出力0bytes。logsは `.cache/wip/constructor_retirement_direct.txt` と `beats_buffer_contracts_{fields,call,receiver}_direct.txt`。Cpp source未変更のため通常/ASan/UBSan全操作は今回は再実行せず、既存成功記録を保持した。
- registry（59公開/873共有modules/234checks/106docs）、992Leanファイルsource audit、公開仕様baseline全同一、git diff --check終了0。公開C++/生成モデル/固定仕様は未変更。全件all・独立nanodaは再実行せず、旧new0のstack overflowも未解消。追跡中の検査プロセスはない。
- **次は返却scalar fieldsから各method引数の式を作り、区間/値域/Safe条件と実call・更新後receiverへ接続する**。BVecsの入口条件は揃った。INF/nはExportLayout.infCell/nCellとCppNestedEval.envOfからvariable式のdenoteへ渡せる。既存Proofs.BeatsSeparateの6定理はBeatsPrepare.vargs sl 0 15と4/5scalar値を受ける。大きい物理容量にはBRepS.cap_indicesを使い、操作用下界をmin L INT_MAXへ縮め、元4*n範囲を狭めない。n/stack256/qa/qbのi32境界、各Safeとscalar式の意味を実receiverへ結ぶ。総資源（export込み仕事量/peak）、元callerの全無関係vector保持、child header入力、converterの複数vector bundle、copy/move/destruction、公開版切替と独立監査/全137旧ファイルの検証も残る。


### 返却fieldの配置・実resolveとscalar別名保持（最新）

- `BeatsConstructorFields.ExportLayout` を追加。返却memory/scalar bindings/vector bindings/slots/scope/scalar baseline、15fieldのtrueな最大書込み権限、rootWritable表の長さ、実vectorSlot/binding lookup、INF/nのscalarCellをまとめる。finish_from_layout_fullは共通multi finishのrestored結果と最終FWM/QSから導き、ExportFacts/stage_export_fullへ残す。construct_fullは元callerからこの配置を導き、memory=元caller.memory+[INF,n]、新owner=旧objects数+iへ揃えた結果を返す。従来のfinish_from_layout/constructは元の型の射影として維持。congr_fieldsはi<15の範囲で等しいowner写像へ配置を移す補題。
- `CppConstructorRoots.movedAll_length` を追加し、任意root列の移譲でforest objects数が変わらないことを示した。実retireScopeでもobjects数が変わらないことと合成し、export後のrootWritable長の整合を最終FWMから導く。移譲中にpayloadコピーを追加したものではない。資源上限指定なし。
- `Proofs/BeatsConstructReceiver.lean` を追加登録。resolve_field/construct_fieldsはExportLayoutとfield Modelsから**実返却slot→writable root binding→実buffer**のresolve成功とpayload一致を導く。old_scalar_keptは元callerで成功していた任意scalarCellの読取りが、同じbinding/readonly権限・同じcellで成功することを示す。別名を含む。元の無効addressの失敗まで同値とは仮定しない。
- 最終build実6497終了0/1174targets、`.cache/wip/beats_construct_receiver_build.txt`、新/変更modules警告0。途中の草案はList.map_congr_leftが関数であること、baseのrfl不足、mv.nvの明示、normalizeのslot permuteまでの明示展開、Option.bindの型クラスBind.bindの明示で修正した。資源上限を増やす失敗回避はしていない。
- 既存root構築checkへ `tests/lean/beats_construct_receiver.lean` を追加し、同じmethodのimport先をBeatsConstructReceiverにした。返却vector slotで最大値6を読み、同じ実参照で12へ書き換えて読み直し、他field/元入力buffer保持、readonly入力へのwrite拒否を確認。一般callerでconstruct_fieldsからmemory配置、任意の有効old scalar参照保持、全15fieldの実resolveまで導くfixtureも型検査。初回fixtureは結果に使わない存在変数bufferの型が未指定だったため失敗し、実resolveの返却bufferを等式に含めて修正した。最終単独実74815終了0/1test10.396秒、`.cache/wip/beats_construct_receiver_test.txt`。
- 確保/構築全回帰実16657終了0/9tests43.297秒、`.cache/wip/beats_construct_receiver_allocation_tests.txt`。source-matched candidate NProgram/stage/descriptorの生成型検査も実40116内で終了0/1test22.875秒、`.cache/wip/beats_construct_receiver_source_test.txt`。Cpp sourceは未変更のため今回は既存通常/ASan/UBSan全操作の再実行はせず、前turnの3tests成功記録を保持した。既存#pragma onceのClang警告だけでLean側警告なし。
- 同じ直列実40116でCppConstructorRoots/BeatsConstructorFields/BeatsConstructCall/BeatsConstructReceiverのdirect型検査も終了0・各出力0bytes。logsは `.cache/wip/beats_construct_receiver_{roots,fields,call}_direct.txt` と `beats_construct_receiver_direct.txt`。registry（59公開/872共有modules/234checks/106docs）、991Leanファイルsource audit、公開仕様baseline全同一、git diff --check終了0。全件all/独立nanodaは再実行せず、旧new0のstack overflowも未解消。追跡中の検査プロセスはない。
- **次は既存6操作の入口に必要な残りのbuffer Valid/limit・strict/base等の条件と総資源**。いま返却fieldのslots/bindings/最大権限/Modelsとresolve、scalar配置・old scalar別名は一般証明済み。FWMにはbuffer Valid/limitもあるが、退役後の各field bufferのmetadata保持を外へ取り出す補題が必要。strictは元callerのscope上界→移譲→callee scope破棄の全owner条件として接続する。元callerの無関係vector全体保持、export込み総仕事量/peak、child header入力、converterの複数vector bundle、copy/move/destruction、公開版切替と独立監査/全137旧ファイルの検証も残る。fieldへの直接write回帰はgrant検査であり、書換え後のBRepS保持は主張しない。


### 元callerからprepare・構築・exportを接続（最新）

- `Proofs/BeatsConstructCall.lean` を追加登録。programはreadonly vector入力1本・unit結果・15確保を含むwide stage。initial_prefixは実preparedのmemory=callerPからcaller prefixの長さ・値を導く。constructは元callerのVOKG/内容/標準limit、1≤n、4*n<2^31、InRangeだけから、実program.constructMembersFuelの成功、15vector/2scalarのObjectRef、BRepS、全15fieldのcaller.scopeでのModelsを示す。wb/maximumは元grantの有効な任意の組合せで、slot/binding/owner番号や既存scalar別名を限定しない。calleeのreadonly化だけを行い、初期prefix長さ/型/scopeを利用者の追加前提にはしない。
- `BeatsConstructorFields.ExportFacts/stage_export_full` は構築後の全16root Models、実scope、exportで元scope外の無関係なrootを保持する性質を返す。従来stage_exportは同じ型の射影として維持した。constructは入力owner<旧objects数、新規field owner≥旧objects数と、元入力scope≤caller.scope<callee.scopeを元VOKGから導き、**export後も入力rootの型/scope/内容が保たれる**ことも結果に含める。
- 最終build実82290終了0/1173targets、`.cache/wip/beats_construct_call_build.txt`、新/変更modules警告0。草案は予約語prefixを局所名へ使った構文エラー、cty 15のsimp onlyでor_true不足を修正した。資源上限指定なし。公開C++/生成model/固定仕様は変更していない。
- 既存確保checkへ新fixture `tests/lean/beats_construct_call.lean` と1methodを追加。owner2/binding3/slot2、scope2、既存3vectorとscalar別名のcallerで実constructMembersFuelを評価。可変入力、readonly binding、最大権限もreadonlyの入力、scalar別名を持つ4通りで、元memory/slots/bindings/権限/baseline/3buffers、15新rootと実resolve、返却INF/n、木の最大値6/最小値4を確認。fuel不足と型違いslotも拒否する。初回fixtureはctyの名前空間をBeatsPrepareと取り違えたため失敗し、BeatsRepへ修正。単独実99030終了0/1test8.572秒、`.cache/wip/beats_construct_call_test.txt`（後の最終検査で更新）。巨大確保なしのn=2^28でconstructを記号的に適用する例も追加した。
- 確保/構築全回帰実45780終了0/9tests44.646秒、`.cache/wip/beats_construct_call_allocation_tests.txt`。候補生成検査へ**候補から生成したNProgram全体とBeatsConstructCall.programのrfl一致**を追加し、通常/ASan/UBSan・大値・境界・既存stage/descriptor一致を含む候補3testsも実45992終了0/30.180秒、`.cache/wip/beats_construct_call_candidate_tests.txt`。この全9回帰後に追加したn=2^28の記号的例を含め、最後の単独回帰と新/変更2modulesのdirect型検査を直列実27492で終了0まで回収した。direct logsは `.cache/wip/beats_construct_call_fields_direct.txt` と `beats_construct_call_direct.txt` で各出力0bytes。追跡中の検査プロセスはない。
- registry（59公開/871共有modules/234checks/106docs）、990Leanファイルsource audit、公開仕様baseline全同一、git diff --check終了0。全件all/独立nanodaは再実行せず、旧new0のstack overflowも未解消。
- **次はexportを含む総仕事量・peakと返却receiverから既存6操作への接続**。constructの一般結果はfieldと入力のModelsであり、元callerのすべての無関係な領域保持・返却field slots/grants・scalar layoutを一括で示す形への強化も残る。これらのmetadata保持は実回帰と共通multi finishの補題で確認したが、Beatsの最終定理へすべては公開していない。receiver接続にはfinish_from_layout_full等でgeneric finish_okのrestored結果/lookup条件も外へ出すとよい。child header入力、converterの複数vector class bundle、copy/move/destruction、公開版切替と独立監査/全137旧ファイルも継続。


### Beatsの最終Frameから15vector/2scalarをexport（最新）

- `BeatsInlineExec.FinalLayout` と body_exec_full/stage_exec_fullを追加。実構築の最終FWM(root tags/bindings/rootWritable/buffers)とscalar QS(CtCells INF n 0 (4*n))を保持する。従来body_exec/stage_execは同じ入力・結果型の射影として維持した。新成功条件を元callerへ追加せず、実runFuelの成功を引き続き導く。変更module build実63952終了0/1163targets、`.cache/wip/beats_final_layout_build.txt`。
- `Proofs/BeatsConstructorFields.lean` を追加登録。final_modelsでviewによらない実Frameの全16flat rootモデル、final_lengthsで実slot/binding長を導く。final_field/final_vector_fieldsはslot循環置換とbinding indexの逆写像を通して、実slots1..15のvectorSlot/resolve/型/元scope headerを得る。最大権限とwritableの区別を保持する。scalar_cell_from_layoutは任意state/cellの抽象的なlookup補題で、これを使うfinal_scalar_fieldsは実slots16/17のINF/nを捕捉する。
- final_rootsはFWMのdistから15ownerの相異性と元scopeのModelsを作る。finish_from_layoutは新multi finishの実成功、15rootのcaller.scopeでのModels、元scope外の無関係なrootの保持まで合成。**stage_exportは構築前のRealizes/Input/Entryと初期prefixの長さ/型/scopeから、実15確保→wide本体→15vector/2scalar exportの成功、BRepS、全field payloadの保持を導く**。構築後のFWM/field capture/finish成功を前提にしない。元の4*n<2^31を使い、8*n+8<2^31へ狭めていない。
- 最終正本build実41726終了0/1171targets、`.cache/wip/beats_constructor_fields_stage_build.txt`、新/変更modules警告0。direct型検査実77072も両modules終了0・各出力0bytes、`.cache/wip/beats_final_layout_direct.txt` と `beats_constructor_fields_direct.txt`。途中は名前空間指定、List.mem_mapの局所仮説名の衝突で失敗し、明示的な名前へ修正した。scalar読取りをNat値で直接展開した草案はkernel深度に達したため、上記の一般cellの小補題へ分割し、**資源上限を増やさず**解消した。新moduleにmaxRecDepth/maxHeartbeats等の指定なし。
- 新fixture `tests/lean/beats_constructor_fields.lean` と既存 `test_beats_allocation.py` の新methodを追加。長さ1/3の実prepare→stage→finishを評価し、全15rootのscope・返却vector/scalar slots・INF/n・入力buffer保持・field参照・binding/slot/memory長を確認。単独実23240終了0/1test18.956秒、`.cache/wip/beats_constructor_fields_test.txt`。確保/構築全回帰実55721終了0/8tests35.917秒、`.cache/wip/beats_constructor_fields_allocation_tests.txt`。
- 候補の生成検査へ、実construction_fieldsと15vector/2scalar descriptorsのrfl一致を追加。既存のstage全文一致・通常/ASan/UBSan 3000×60操作・大値・巨大確保なし算術境界も含め、実8584終了0/3tests31.406秒、`.cache/wip/beats_constructor_fields_candidate_tests.txt`。ヘッダー単独Clang AST取得時の既存#pragma once警告のみでLean側警告なし。巨大配列を実確保した検査ではない。
- registry（59公開/870共有modules/234checks/106docs）、989Leanファイルsource audit、公開仕様baseline全同一、git diff --check終了0。公開C++/生成モデル/固定仕様は未変更。全件all/独立nanodaは再実行せず、旧new0のstack overflowも未解消。
- **次はBeatsInputPrepareの元callerから、このstage_exportへ初期prefix長さ/型/scopeを自動接続する**。現在は準備済み入力の段階での全stage+exportが接続済みで、root prepareを含む単一の最終呼出し定理はまだない。新multi finishを含む総仕事量・peak、返却ObjectRefから既存6操作へのreceiver接続、converterの複数vector bundle対応、child header入力、copy/move/destruction、公開版切替と独立監査/全137ファイルの検証も残る。


### 複数vectorの実field slotsからcallerへの構築終了（最新）

- `Proofs/CppConstructorMultiFinish.lean` を追加登録。VectorField(slot,element)の列から実NState.vectorSlot/Frame.resolveで型・権限・元scopeのroot headerを検査し、全vector bindingsとscalar値を捕捉してからfinishRootsを一度実行する。restoredはcallerの元metadataへvector/scalar bindings・slotsを追加し、vector headersをcaller.scopeへ張り直す。ObjectRefはvectorSlots/scalarSlotsの両列を返す。owner/element/writableとrootWritableを保持し、payloadをcopyしない。scalar memoryは**実calleeの更新済みcaller prefix**+捕捉field値。scalar baselineはcaller、storage baselineは終了Frameから保持し、管理処理のscalar仕事量をvector本数+scalar個数+1追加してobserveする。
- finish_okはfield slot/resolve/型/headerの一致、scalar capture条件、相異なるowner列/正しいModelsから実finishの成功、全選択rootと元scope外の無関係なrootのModels、更新済みcaller memoryとcaller側のbindings/slots/scopeを導く。finish成功自体は前提にしない。restored_vector/restored_scalarは実lookup/cellを示す。NProgram.constructMembersFuel/construct_of_stepsで実prepare/runFuel/finishを接続する。旧1vector用finish/constructFuel・公開Cpp/modelは未変更。
- 正本最終build実76207終了0/121targets、新module警告0、`.cache/wip/cpp_constructor_multi_build.txt`。direct型検査実61566も終了0・出力0bytes、`.cache/wip/cpp_constructor_multi_direct.txt`。初回26263はscalar slot証明でsimp後の余分なomegaだけが失敗したため除去した。資源上限指定なし。
- 新規登録 `tests/test_cpp_constructor_multi_finish.py` の最終実67293終了0/2tests8.849秒、`.cache/wip/cpp_constructor_multi_test.txt`。nested root/子・readonly binding保持、slot/型/scope/権限/child header/重複owner/短いまたは型の違うcaller prefixの拒否、scalarのみ/vectorのみ/空layout、一般finish_okとlookup補題を確認。実C++の2vector/2scalar構成子を生成し、prepare→stage→新finishの成功、参照引数への9の書込み、元scalar別名/readonly cell・非ゼロbaseline・無関係vector・元7を捕捉した2fields・返却vector参照の実書込み・fuel不足を検査。同じCppをUBSanでも実行した。
- 最初の2testsはfixtureがStoreのpeak/baseSpaceの位置を取り違えたことと、InhabitedのないVectorFieldへget!を使ったことで失敗した。Storeを名前付き指定へ変更し、重複fieldを明示して修正。前turnの共用roots fixtureもstore baseline=5/peak=100の名前付き指定に修正し、新2testsはそのfixtureも再検査済み。C++や実行モデルの不具合ではない。
- registry（59公開/869共有modules/234checks/106docs）、988Leanファイルsource audit、公開仕様baseline全同一、git diff --check終了0。全件all・独立nanodaは再実行せず、旧new0のstack overflowも未解消。
- **Beats class全体のexportはまだ未完了**。次はBeatsInlineExecの最終FWMから各fieldのModels/resolve/headerを取り出し、この新finishへ接続する。現body_exec/stage_execの公開結果はbuffer lookup/itemsを返すが最終root tagsやbindingsを外へ出していないため、それらを保持する拡張補題または追加の最終Frame条件が必要。元APIへ成功条件として押し付けない。converterの複数vector class bundleはまだ新entry pointを使わず、テストでconstruction_fieldsのslot表と手書きdescriptorを照合した段階。descriptor生成・copy/move/destruction/総資源、child header入力、公開版切替・独立監査と全137ファイルを継続する。


### 複数rootの構築scopeからの移譲と一括破棄（最新）

- `Proofs/CppConstructorRoots.lean` を追加登録。旧 `CppConstructorFinish.finish` は選んだ1本だけを移してscopeを破棄するため、そのままBeatsの15本へ適用しない。旧関数は変更せず、新transferAll/finishRootsでowner ID・element型の列を順に移譲し、すべて移譲した後に一度だけ元scopeを破棄する。実行関数の引数に論理的なvector内容は含めず、specsで証明用View列から実行用descriptor列へ対応させる。
- transferAll_okは異なるowner列と元scopeのModelsから、実transferRoot列の成功、全選択rootの移譲先でのModels、無関係なrootのModels保持を導く。movedAll_layoutは移譲中のstorage全体・binding表・rootWritable表を保持する。finishRoots_okは実retireScope成功と選択rootの保持、元scope外の無関係なrootの保持を合成する。flat/rows両方を扱い、rowsの子bufferも保持する。空の選択も扱い、同じ元scopeの未選択一時rootは通常どおり破棄する。資源上限指定なし。
- 正本build実6296終了0/119targets、log `.cache/wip/cpp_constructor_roots_build.txt`。direct Lean型検査も終了0・警告0、`.cache/wip/cpp_constructor_roots_direct.txt`。新規登録 `tests/test_cpp_constructor_roots.py` の最終実69327終了0/1test1.180秒、`.cache/wip/cpp_constructor_roots_test.txt`。15本のflat roots、nested root/子buffer、未選択一時rootの破棄、他scopeのデータ保持、epoch/権限/binding表を実評価し、重複owner・誤scope・child header・誤型の失敗と一般定理の適用を確認した。初回fixtureはList.mem_consのnil分岐と未使用simp引数で失敗し、修正後に成功を回収した。
- registry（59公開/868共有modules/233checks/106docs）、987Leanファイルsource audit、公開仕様baseline全同一、git diff --checkが終了0。既存の公開C++/生成モデル/固定仕様は変更していない。全件all・独立nanodaは再実行していない。旧new0のstack overflowも未解消。
- **まだclass export全体の完了ではない**。次は実field slotsからのroot capture、scalar値・更新済みcaller prefixを含むcaller再配置、Beats stageの最終rootモデルとの接続、copy/move/destructionとその仕事量/peakを進める。現transferAllはFrameのbinding表を保持するため、scope移譲後のcallee root bindingsはそのままcallerのobject参照として使わず、終了処理でcaller側のroot headers/slotsを再構成する必要がある。converterの複数vector export対応、child header入力、公開版切替・独立監査と全137旧ライブラリの残件も継続。


### 確保・stage・root prepareを含む仕事量とpeak（最新）

- `Proofs/BeatsAllocationResources.lean` を追加登録。fill_resourcesは実fillVectorの評価からscalar仕事量/peak、liveS保持、storage baseline保持、capacity+root headerを含む常駐領域とstorage仕事量増分、storage/全体peakを導く。既存clone_costと同じ実確保stateの式を照合してliveSpace増分を得るもので、実C++に余分なcopyを挿入していない。
- Bounds.refl/trans、prefix_bounds/resourcesで15確保を合成。scalar仕事量増分≤319（2*count.nodes+2*value.nodes+3を15個足した上界）、常駐領域/storage仕事量増分=G=12*(8*n+8)+783。scalarPeak≤S=max 初期scalarPeak (liveS初期+319)、storagePeak≤T=max 初期storagePeak (初期liveSpace+G+1-初期baseSpace)、全peak≤Q=max 初期peak (S+T)。baseline減算は自然数の飽和減算のまま扱う。実成功を仮定するfill補助lemmaを使うが、prefix_resources自身はRealizes/Inputから実prefixの成功も導く。
- stage_resourcesはstage_execの確保結果と同じ実prefix結果を照合し、実確保後outに依存しない閉じた上界へ合成する。scalar仕事量増分≤4*n*45414+419、storage仕事量増分≤G+4*n*18+10。stageScalar=Q+S+初期caller-memory長+100、stageStorage=T+初期liveSpace+G+1で各peakを抑え、全peakは両者の和以下。初期状態を固定したときnに線形である。
- total_workはstage全体を**初期work+181824*n+1308**以下とする。prepare_resourcesはroot入力の実prepareとstage正常終了・BRepSも合成し、prepareの増分3を加えて**元caller.work+181824*n+1311**以下を得る。root prepare後のpeak式のcalleeは元callerから明示計算するpreparedであり、実確保後の未知状態ではない。抽象仕事量とcell領域であり実測時間/bytesではなく、class export/finish/copy/move/寿命の資源は含まない。
- 正本build実45798終了0/1165targets、新module警告0、log `.cache/wip/beats_allocation_resources_build.txt`。新moduleに資源上限指定なし。確保/構築回帰の最終実62829終了0/7tests15.451秒、`.cache/wip/beats_allocation_resources_test.txt`。空入力/長さ3の実prefix、scalar/storage両baselineが非ゼロの状態で仕事量・liveS・liveSpace・storage work・各peakを照合し、閉じたstage/root prepare上界の一般適用を型検査した。
- 初回回帰47436は新fixtureのrecord改行構文、次の99175はscalar StateのbaseMemory/peakの位置を取り違えたfixtureで失敗した。新fixtureを修正し、既存root caller fixtureもbaseMemory=0/peak=4へ直し、baseline≤memory長のguardを追加してから全7testsの終了0を回収した。C++や実行モデルの定義の不具合ではない。
- registry（59公開/867共有modules/232checks/106docs）、986Leanファイルのsource audit、仕様baseline完全一致、新module警告0を確認。公開C++/生成model/固定仕様は未変更。新全件gate・独立nanodaは再実行していない。追跡中のbuild/testプロセスはない。
- 次はnested rowのchild header入力、class export/finish/copy/move/寿命とその資源、公開版切替・固定仕様レビュー、旧new0の独立stack overflowの分割/改善と独立検証を進める。公開版のint確保長の入力範囲縮小は未解消。全137旧ファイルの検証も未完了。

### 元callerからroot入力のreadonly prepareとstage

- `Proofs/BeatsInputPrepare.lean` を追加登録。元callerのroot VOKGから、caller bindingのwritable=true/falseの両方を許して実prepareを導く。parametersは[vector s64 false]で、登録済みBeatsConstructionStage.SegmentTreeBeats_construct0.parametersとのrfl一致を回帰で要求する。slot/binding/owner番号、既存scalar/参照alias/scopeは任意で、元の最大権限とstorage/forest/rootWritableを保つ。callee bindingだけreadonlyとなる。
- layoutは実prepared状態の1vector slot/binding、scalar formal bindingsなし、callerPのmemory prefix、同じbaseMemory、caller.scope+1を示す。prepared_family/real/input/entryで入力rootのモデルと正しいRealizes/Input/Entryを作り、strict/base条件も元callerから引き継ぐ。元callerへEntryの配置を追加で要求しない。prepared_workはprepareのscalar仕事量増分がちょうど3であることを示す。
- prepare_stageは実prepareから実15確保とインラインstage全文の正常終了・BRepS・15fieldの実buffer内容と元入力buffer内容保持を導く。callerのowner数をそのままnew fieldの開始ownerとし、caller bindingsの並びや余分なrootsを削っていない。class objectとしてexport/finishする証明はまだない。
- **root grantの範囲の入口接続**。nested vectorの行をborrowしたchild header入力は現Flat/FWMのroot tag条件では扱えず、元C++が許す利用形態として未検証のまま残る。row入力を削って解決扱いにしない。一般のborrowed flat-ownerモデル/readonly入力slotの表現と既存root用FWMの接続が必要。元の一般APIを狭めて公開版へ切り替えない。
- 正本build実7468終了0/1164targets、新module警告0、log `.cache/wip/beats_input_prepare_build.txt`。確保/構築回帰6tests実43945終了0/14.778秒、`.cache/wip/beats_input_prepare_test.txt`。owner2/binding3/slot2、無関係scalarと参照alias、scope2のcallerを使い、可変/readonly参照から同じreadonly calleeを作ること、最大権限/storage/memory prefix/owner cursorの保持、prepareからstageまでの一般適用を確認。新moduleに資源上限指定なし。
- registry（59公開/866共有modules/232checks/106docs）、985Leanファイルのsource audit、仕様baseline完全一致、新module警告0を確認。公開C++/生成model/固定仕様は未変更。新全件gate・独立nanodaは再実行していない。追跡中のbuild/testプロセスはない。
- 次はrow等のchild header入力の一般性、確保中scalar仕事量/peakを含む全体資源、class export/copy/move/寿命、公開版切替・固定仕様レビューと独立監査を進める。公開版のint確保長の入力範囲縮小は未解消。全137旧ファイルの検証も未完了。

### 実15確保とインラインstage全文の実行・表現

- `Proofs/BeatsInlineFrame.lean` を追加登録。Entryは準備済み1vector入力の内部配置（p.slot=0、次binding=1、slot長=1、scalar formal bindingsなし）。allocation ownersとscalar caller-memory prefixは任意。normalized_frameは実binding表を先頭16個だけ回した表、allocated_slots/normalized_slotsは実slot表とidentity表、normalized_fwm/normalized_qsは実storage/権限/strict条件/全bufferと実memory/bindingsからFWM/QSを導く。prefix_environmentは初期callerから実15確保、最終Realizes/正確なstorage work、CVecs/FWM/QSを同時に作る。
- `Proofs/BeatsInlineExec.lean` を追加登録。body_execはctor_rep_wideとsoundM_ownedを正しい初期FWM/QSへ適用し、両viewのOutcome等式から**実インライン本体の正常終了**を得る。BRepS、scope、全16vectorの実lookup/最終内容、本体scalar/storage workとpeakを扱う。追加のprepare/finishやscope増分はない。
- stageは15本のfieldStmtの後へこの本体を直接つなぐ。field_control/prefix_continueは実prefixと本体の成功から、余分なskipを挟まないstage全文のrunFuelを構成する。stage_execは正しい初期caller/Entryから実15確保とstage全文の正常終了・BRepS・全16vector最終内容を導く。確保後の不変条件や成功は前提にしていない。n≥1、元の4*n<2^31と従来のInRangeを使い、8*n+8<2^31は要求しない。Entryを元callerからreadonly prepareで導く接続は未完了で、元APIに追加前提として押し付けて完了扱いにしない。
- 本体scalar work≤4*n*45414+100、確保込みstorage workの増分≤12*(8*n+8)+783+4*n*18+10。peakは確保直後outを基準にscalarBound=out.peak+out.scalars.peak+caller-memory長+100、storageBound=out.storage.peak+out.liveSpace+1、全peak≤両者の和。確保中のscalar work/peakを初期callerだけの閉じた全体上界へ合成する部分は残る。モデル上の資源であり実測ではない。
- Frame最終正本build実56325終了0/1162targets、`.cache/wip/beats_inline_frame_build.txt`。Exec正本build実15499終了0/1163targets、`.cache/wip/beats_inline_exec_build.txt`。新modules警告0、資源上限指定なし。草案はList.rangeのlookup補題へ必要なboundを明示し、prefixはrunFuelを全展開せずsequenceの一段だけをchangeして正常終了へ合成した。
- 実52635終了0で直列回帰を完了。allocation/frame/stage5testsは12.110秒、candidate3testsは29.161秒、log `.cache/wip/beats_inline_stage_tests.txt`。通常/ASan/UBSanの既存3000×60操作と大値、元サイズ境界、構成子以外の生成関数一致に加え、**候補からのstage全文とBeatsInlineExec.stage 0 15のrfl一致**を要求する。n=2^28のstage正常終了の記号的適用例、実normalized Frameのbindings/slots/scalars/scope/storage/work保持も成功。巨大配列の実確保/測定はしていない。
- registry（59公開/865共有modules/232checks/106docs）、984Leanファイルのsource audit、仕様baseline完全一致、新modules警告0を確認。公開C++/生成model/固定仕様は未変更。新全件gate・独立nanodaは再実行していない。追跡中のbuild/testプロセスはない。
- 次は元callerからのreadonly prepare/Entryの導出、確保中scalar仕事量とpeakを含む全体資源、class export/copy/move/寿命、公開Cpp/model切替と固定仕様レビュー・独立検証を進める。公開版のint確保長の入力範囲縮小はまだ未解消。全137旧ファイルの検証も未完了。

### binding viewとCoreCommand全体のrunFuel

- `Proofs/BeatsBindingRun.lean` を追加登録。CoreStmt/CoreCommandは既存BeatsSlotCycleの定義をそのまま使い、skip/declare/assign/write/check/ret/retVector/retUnit、sequence/scope/branch/while/breakを扱う。vector確保/reserve/append/copy等とinvokeScalarはこの述語が拒否する。全構文一般の意味保存とは扱わない。
- stmt_long/run_longは各実成功後も16bindings以上を保つ。release_longは評価後/開始時の両方の長さ、leave_longは内側/外側の両長さを使い、rowの一時bindingとscope復元後も後続へ条件を渡す。stmt_commuteはretVectorもinverse binding番号から同じowner/elementを返す。run_viewは任意fuelでNState全体/returned/breakingに加えfault/exhaustedも対応するOutcome等式で、全体の成功を仮定しない。
- `BeatsWideCall.body_view/inline_body_view` を追加。実WideCtorCmdがCoreCommandの範囲に入ることを使い、slot位置の置換とbinding viewの両方を実インライン本体へ合成した。元の状態からview(permuted state)への実runFuel対応で、余分なprepare/finishやscope増分はない。**まだview後の初期FrameからFWM/QSを構成していない**ため、数学的本体証明との合成・実stage全体の成功/表現/資源は未完了。
- 最終正本build実94415終了0/1160targets、新/変更modules警告0、log `.cache/wip/beats_binding_run_build.txt`。初回83399はwrapperでprogram.bodyを明示展開していなかったためrewrite失敗、simp only [program]へ修正後に成功。新moduleに資源上限指定なし。
- 実63279終了0で直列回帰を完了。slot/binding/scope8testsは8.643秒、allocation/call4testsは9.213秒、log `.cache/wip/beats_binding_run_tests.txt`。複数fuelでloopの局所宣言/実書込み/scope復元、break/return/check省略、fault/exhausted、vector/unit returnと無効slotをOutcome全体で比較し、実wide本体の両view合成も一般例で型検査した。
- registry（59公開/863共有modules/232checks/106docs）、982Leanファイルのsource audit、仕様baseline完全一致、新/変更module警告0を確認。公開C++/生成model/固定仕様は未変更。新全件gate・独立nanodaは再実行していない。追跡中のbuild/testプロセスはない。
- 次は実15確保後のFrameについてview(permuted state)のbinding表/slotsを示し、FWM/QSとsoundM_owned、数学的なwide本体を実stageへ合成する。元callerからreadonly入力prepare、確保を含む全体資源、class export/copy/move/寿命、公開版切替・独立監査と全137旧ファイルは未完了。

### binding viewと宣言/代入/書込み・release/leave

- `Proofs/BeatsBindingStmt.lean` を追加登録。rotate_takeは先頭16bindingsの回転と16以上のprefix takeの対応を示す。release_viewは評価後の一時binding解放、declared_view/enter_viewはscalar宣言とscope進入を対応させる。declare_run_view/assign_run_view/write_run_viewはOption/NStep全体の等式で、型変換・権限・添字等の失敗も含む。
- writeは右辺→container→添字の順を保ち、実Frame.elementRef/write、実配列更新、一時bindingの解放と課金まで接続する。commit_bindings/write_bindingsとwriteValue_growthで途中のbindings条件を引き継ぎ、最後はtoReleasedStepで元のbinding長へ戻す。解放後の長さが途中の長さ以上とは仮定しない。
- leave_viewはouter/innerの16bindings以上を条件に、任意のRet（戻りvectorを含む）と成功・失敗を対応させる。exitFrame_rebind/exitFrame_bindingsは実transferRoot/retireScopeに基づき、leave_normalはhelperと元NState.leaveの実定義の一致を示す。scalar memory長/型prefixの検査を保ち、vectorの所有権移譲とscope破棄も扱う。元のCppNestedProgram側の定義は変更していない。
- 正本build実96988終了0/38targets、新module警告0、log `.cache/wip/beats_binding_stmt_build.txt`。slot回帰7tests実39014終了0/7.282秒、`.cache/wip/beats_binding_stmt_test.txt`。宣言/代入/実配列書込み、readonly/変換失敗、rowのRHS/target両方で増えた一時bindingの解放、正常/異常scope復元、内側のvectorが実際に外側へ移る返却を確認した。新moduleに資源上限指定なし。
- registry（59公開/862共有modules/232checks/106docs）、981Leanファイルのsource audit、仕様baseline完全一致、新module警告0を確認。公開C++/生成model/固定仕様は未変更。新全件gate・独立nanodaは再実行していない。追跡中のbuild/testプロセスはない。
- 次はcheck/ret/retVector/retUnit/skip等のprimitiveと16bindings条件の保存、制御全体のrunFuelを合成する。初期実Frame/FWM/QS、soundM_owned、元インラインstageのrunFuel、readonly入力prepare、確保を含む全体資源、class export/寿命、公開版切替・独立監査と全137旧ファイルは未完了。

### binding viewとContainer/NExpr全構文の実評価

- `Proofs/BeatsBindingExpr.lean` を追加登録。bindChild/child/size/readValueのFrame対応とbindings長の単調性を証明した。rowの新bindingは旧bindings長（16以上）へ追加され、uncycleでも同じ番号になる。container結果はuncycle、整数結果はidで写すEvalRelを用い、bind/precharge/finish/frameStepからContainer/NExprの全構文を相互再帰で合成した。cast/targetCast/unary/binary/divrem/logical、size/read、再帰的rowを含む。
- expr_eval_view/container_eval_viewはOption全体の等式で、初期16bindings以上だけを要求し、妥当性や成功を仮定しない。Frameの新binding/権限/storage、scalar状態、仕事量/peakを含む結果NState全体が対応する。expr_fault_viewは失敗の同値、expr_binding_growthは実成功後のbindings長単調性。元のBeatsSlotCycle側の式評価/命令runFuelは変更していない。
- 正本build実13172終了0/37targets、新module警告0、log `.cache/wip/beats_binding_expr_build.txt`。slot回帰6tests実81386終了0/5.853秒、`.cache/wip/beats_binding_expr_test.txt`。算術/型変換/targetCast/divrem/短絡、型変換・ゼロ除算・範囲外失敗、rowの新binding16と値/長さ、readonly親から子bindingへの権限継承、全結果状態の対応を確認した。
- 草案ではsizeの固定u64判定を分岐ごとに直接展開するとkernel深度に達したため、Bool判定と整数値を抽象化したchecked_frame/checked_growthの小補題を適用し、標準資源上限のまま解消した。成功を追加前提にしたり判定を省いたりしていない。新moduleに資源上限指定なし。
- registry（59公開/861共有modules/232checks/106docs）、980Leanファイルのsource audit、仕様baseline完全一致、新module警告0を確認。公開C++/生成model/固定仕様は未変更。新全件gate・独立nanodaは再実行していない。追跡中のbuild/testプロセスはない。
- 次はbinding viewに対する宣言・代入・書込み・release/leaveと命令run/runFuelを合成する。初期実FrameからのFWM/QS、soundM_owned、元stageのrunFuel全体、readonly入力prepare、確保中を含む全体資源、class export/寿命、公開版切替・独立監査と全137旧ファイルは未完了。

### binding参照の対応と同一scope所有の実行定理

- `Proofs/BeatsBindingCycle.lean` を追加登録。rebindは先頭16bindingsをrotateし、Reference.slotと各vector slotにuncycleを適用する。resolve/elementRef/grant/read/write/commit/updated/addBindingのOption全体の対応を証明し、readonly/古いepoch/誤ったowner/範囲外の失敗も含む。owner・buffer・forest・権限は同一。16以降のbindingはそのままで、末尾追加にも対応する。rebind/restoreとreference/unreferenceの逆変換も証明した。
- viewはslotの位置を変えず、binding番号を写す。scalarSlot/scalarCell、vector slot→resolve、work/charge/observeとslot長を保つ。通常の確保後状態を既存BeatsSlotCycle.permuteで見るとslots=[1..15,0]で、さらにviewを適用してidentityのbinding番号と回転した表へ対応する。**まだ式eval・命令run/runFuel・scope/leave・一時bindingのrelease全体のview対応はない**。Frame primitivesの対応だけでインライン本体全体を完成扱いにしない。
- 追加でscopeの差を特定した。旧MultiVec.soundMはmv.sc≤sc、FWM.strictは全context<mv.scなので、context=scで確保したfieldにはそのまま適用できない。`Proofs/MultiVecOwnedSound.lean` のfresh_ownedはmv.sc≤sc+1から内側scope sc+1にrootがないことを導く。soundM_ownedはこの条件で同じRunsTo/QpostM（状態・正常実行・仕事量・領域）を証明する。旧soundM/FWM/公開定理の型は変更せず、成功やscope退出を追加で仮定しない。新2modulesとも資源上限指定なし。
- binding正本buildは実コマンド終了0/36targets、log `.cache/wip/beats_binding_cycle_build.txt`。scope正本の最終build実86337終了0/71targets、`.cache/wip/multivec_owned_sound_build.txt`。新modules警告0。slot回帰を5testsへ拡張し、最終実86462終了0/4.765秒、`.cache/wip/beats_binding_owned_test.txt`。binding順だけの変更で古いgrantが無効になる例、両方を写した読書き/他owner保持、各種失敗、tail binding/逆変換、slotとbindingの別写像、同一scopeのrootを保持する実leave、owned soundnessの一般適用を確認した。初回scope fixtureは不足したnamespace openで失敗し、修正後に全5testsの終了0を回収した。
- registry（59公開/860共有modules/232checks/106docs）、979Leanファイルのsource audit、仕様baseline完全一致、新modules警告0を確認。公開C++/生成model/固定仕様は未変更。新全件gate・独立nanodaの成功は主張しない。追跡中のbuild/testプロセスはない。
- 次はviewを式/命令列/leave/releaseへ合成し、soundM_ownedと初期配列/実Frameからインライン構築stageのrunFuelを導く。readonly入力prepare、確保を含む全体資源、class export/copy/move/寿命、公開版切替、独立検証と全137旧ファイルの残件も継続。

### 正規化したwide構築本体の実prepare/callFuel

- `Proofs/BeatsWideCall.lean` を追加登録。programはparameters=vparams cty cw 0 16、result=unit、body=WideCtorCmd 16。writable_bodyを標準上限で証明。prepare_frameは実prepareの新binding表bl cty V vsc cw 0 16、同じstorage/rootWritable、slots=slN 16 0、scope=caller.scope+1とFWMを導く。実callerの入力→fieldのbinding表を、field→入力の表と同一視していない。
- callはCVecs/BFreshSから元の4*n<2^31でprepare/callFuelの正常終了、BRepS、ScalarPostMBを導く。L<2^31は使わない。本体+呼出しのscalar仕事量≤4*n*45414+134、storage仕事量≤4*n*18+10、元caller memory/bindings/slots/scopeの復元を含む。allocated_callは実fillPrefixの正常終了とこの明示的呼出しを合成し、全16vectorの最終内容とstorage仕事量（確保分storageWork n 0 15を加算）を得る。確保中のscalar work/peakはまだ全体上界に合成していない。
- **これは確保後の本体を独立した呼出しで実行する中間モデル**。候補のインライン構築stageが余分なprepare/finishを持つとは扱わない。scope、scalar prefix、binding表、仕事量を含む状態/view対応を示し、元stage全体のrunFuelへ接続する作業は残る。元callerからreadonly入力参照をprepareする接続、class export/copy/move/寿命、公開版切替・固定仕様レビュー・独立監査も残る。
- 正本build実69575終了0/1156targets、新module警告なし、log `.cache/wip/beats_wide_call_build.txt`。確保回帰4tests実75771終了0/9.159秒、`.cache/wip/beats_wide_call_test.txt`。実prepareのbinding順[1..15,0]、元caller順[0..15]、identity slots、storage/権限保持、readonly入力、scope増分、初期callerから実確保+正規化呼出しの正常終了/表現/復元を得る一般例を確認した。programの引数が旧generated new0と、bodyがWideCtorCmdとrfl一致することも要求する。
- registry（59公開/858共有modules/232checks/106docs）、977Leanファイルのsource audit、仕様baseline完全一致、新module警告0を確認。新moduleの資源上限指定なし。公開C++/生成model/固定仕様は未変更。全件gate・独立nanodaは再実行していない。追跡中のbuild/testプロセスはない。全137旧ファイルの検証は未完了。

### 実確保からCVecs全条件と初期fresh条件

- `Proofs/BeatsAllocationArgs.lean` を追加登録。slot/binding/owner/scopeを別々のoffset関数として定義し、initialの各fieldが実fillPrefixの内容と一致するinitial_field/ctor_fieldを証明した。cvecs/prefix_cvecsは正しい初期callerから実runFuel 16の正常終了と全16vectorのCVecs（ok/dist/items/valid/limit/owner/small）を導く。実Frame.bindingsの順を入れ替えたり、slot番号とbinding番号を同一視したりしていない。
- initial_valid/initial_capacities/initial_freshは実node容量8*n+8とstack容量256のBFreshSを示す。元の4*n<2^31を使い、8*n+8<2^31は要求しない。CVecsの入力p.writable=falseは構築用に準備済みのreadonly参照の条件で、p.maximumは保持する。入力buf.limit=sizeLimit(s64)は通常のstd::vector初期契約であり、fieldのlimitは実配置から導く。prefix_argumentsまでの一般証明は入力writableを限定していない。元callerからreadonly参照をprepareする接続を公開API制約と取り違えない。
- 最終正本build実10112終了0/1132targets、新module警告なし、log `.cache/wip/beats_allocation_args_build.txt`。確保回帰を3testsへ拡張、最終実12902終了0/6.331秒、`.cache/wip/beats_allocation_args_test.txt`。genericな初期callerからのCVecs、slot/binding/owner/scopeが異なるoffset例、全16配列の内容、n=2^28の記号的fresh例を確認した。新moduleに資源上限指定なし。草案のfresh証明は通常simpによるreplicate展開で深度に達したため、長さのsimp onlyへ分けて解消。初回の新fixtureはrecord構文/未指定数値引数で失敗し、修正後に全3testsの終了0を回収した。
- registry（59公開/857共有modules/232checks/106docs）、976Leanファイルのsource audit、仕様baseline完全一致、新module警告0を確認。公開C++/生成model/固定仕様は未変更。独立nanodaと新全件gateは再実行していない。追跡中のbuild/testプロセスはない。
- 次はこのCVecsをprepare/実binding表/構築本体へ接続し、確保を含む全体資源とclass export/寿命を扱う。新旧binding表の順の差は未解消。全137旧ファイルの検証も継続中。

### 確保前からのscope/base条件と16vectorの引数条件

- `BeatsAllocationLayout.fill_layout` はscalar memory/bindings/scopeに加えbaseMemoryの保持を示す。`declareRoot_strict` は最終rootのlookup/parentから既存root・新root・範囲外を分類し、旧子vectorを含む全ownerのscope条件を保つ。未知ownerのcontext/rootOwnerを再帰simpし続ける形にはしていない。
- `prefix_conditions` は初期callerのstrict(scope)とbaseMemory≤memory.lengthを実fillPrefixの正常終了後まで引き継ぐ。`input_argument` は保持された実入力bufferのVOKG/Buffer.Valid/items/ownerを導き、p.writable/p.maximumをそのまま保つ。`prefix_arguments` は確保前の条件のみから実runFuel 16、最終Realizes、正確なobjects/storage work、15fieldと入力のVOKGを同時に導く。確保後のstrict/baseや成功を仮定しない。**CVecsのdist/items/valid/limit/owner/small全体の合成とbinding順のviewは引き続き残る**。
- 正本build実64299終了0/954targets、変更module警告なし、log `.cache/wip/beats_allocation_conditions_build.txt`。確保回帰2tests実85672終了0/4.321秒、`.cache/wip/beats_allocation_conditions_test.txt`。初期条件から全16vectorのVOKGを得る一般例と、既存root/子vector/新root/範囲外ownerのcontext例を追加した。証明器の資源上限は変更していない。公開C++/生成model/仕様baselineは未変更。新全件gate・独立検証の成功は主張しない。
- registry（59公開/856共有modules/232checks/106docs）、975Leanファイルのsource audit、レビュー済み仕様JSONとの完全一致、git diff --checkは終了0。新規登録ファイルはなく、既存moduleと既存回帰fixtureを拡張した。追跡中のbuild/testプロセスはない。

### 確保後の正確なbuffer配置と呼出し条件

- `Proofs/BeatsAllocationLayout.lean` を追加。Flatモデルにはcapacity/limit/epochがないため、CVecsのlimit条件を仮定で埋めず、**実fillVectorの結果からobjects配列・forest・storage work・scalar memory/bindings/scopeを取り出すfill_layout**を証明した。prefix_layoutは15確保を合成し、古いobjectsにfieldBuffer列をappendすることとstorageWorkの正確な増分を示す。新bufferはcapacity=count、limit=sizeLimit(fieldTy)、epoch=0。buffer_atで新lookup、old_bufferで既存bufferの全metadata保持を得る。
- storageWork_fifteenは **12*(8*n+8)+783**。これは保存処理の実行モデル上の仕事量で、scalar評価を含む全work/peak上界ではない。field_argumentはactual_fieldと正確なbufferを組み合わせ、15fieldのVOKG、Buffer.Valid、limit/ownerを構成する。通常のcaller条件strict(scope)とbaseMemory≤memory.lengthは明示的に要求し、prefixがこれらを引き継ぐ証明はこれから。入力vectorを含む16個のCVecs全体はまだ構成していない。
- 正本build実85022終了0/954targets、新module警告なし、`.cache/wip/beats_allocation_layout_build.txt`。test_beats_allocation.pyを2testsへ拡張、最終実84097終了0/3.980秒、`beats_allocation_layout_test.txt`。全bufferのcapacity/limit/epochとobjects配列、storage work、既存inputのcapacity=5/limit=7/epoch=9を保持するmodel上の例、genericなprefix実行→field引数条件を確認。初回の回帰例でomegaが不要な大きい状態仮説まで展開して再帰深度に達したため、Nat.add_assocを使う直接の等式変形へ修正した。資源上限は変更していない。registry/source audit/diffcheck成功、公開仕様baseline全同一。
- 同じturnで独立20457の終端を回収した。**旧new0単独はSIGABRT/stack overflow**。詳細は冒頭。各節の稼働中の記録は当時の観測であり、現在の状態ではない。

### 実15確保とFrameへの接続

- `Proofs/BeatsAllocation.lean` を登録。fieldTy/fieldCount/fieldValueとcountCode/valueCode/fieldStmt/fillPrefixは実candidate stageの15確保と全文rfl一致する。12node配列は8*n+8、stack3本は256、lvalだけINF。型・値・sizeLimit、実入力sizeからcount/valueの評価を元の4*n<2^31で証明した。
- statesが各確保後の論理状態を記録し、states_inputは入力slot/parameter/内容を保つ。input_of_realにより入力owner<次ownerは正しいcaller表現から導ける。**prefix_actualはRealizes/Inputから実runFuel 16の正常終了、15owner/15binding/15slotsの増加を導く**（確保成功を前提にしない）。開始slots=1なら終了16。actual_fieldは全fieldのFlat実Frameモデル・writable root binding・slot・rootWritable、actual_inputは入力内容保持を示す。物理配列を仮定してBFreshSとするだけの証明から前進した。
- 正本build実44392終了0/952targets、新module警告なし、`.cache/wip/beats_allocation_build.txt`。新規登録test_beats_allocation.py実81857終了0/1test2.004秒、`beats_allocation_test.txt`。空入力/長さ3のreadonly入力から15確保を実評価し、全配列の初期値・型・権限・owner/binding/slot、入力保持と燃料不足を確認。候補3tests実93608終了0/29.325秒、`beats_allocation_wide_test.txt`。実sourceの15確保prefixとfillPrefix 0 15のrfl一致を追加。registry/source audit/diffcheck成功、公開仕様baseline全同一。
- **次の接続でbinding順の差を同一視しないこと**。入力だけを登録した通常の開始状態では、prefix後のFrame.bindingsは入力→15fields、slotをcycleで見ると[1..15,0]を参照する（一般のcallerについてはstates_binding/actual_fieldのoffsetを使う）。一方、旧MultiVec.FWM.bindings（MultiVec.lean:105）はList.range nvをbindOfへmapし、slN（同:28）はvector indexとbinding indexが同じ順を仮定する。新actual_fieldから柔軟なCVecs（SegmentTreeBeatsCall.lean:345、sl/vb/Vを別に取る）を組むか、binding表のviewと評価対応を追加して本体へ接続する。slot置換だけで旧FWMを満たすと扱わない。
- 確保を含む全体のwork/peak上界、class export/copy/move/寿命、公開Cpp/modelへの切替と固定仕様レビュー、独立監査/全件gateは残る。新moduleは標準資源上限で証明し、大規模配列を実確保する検査はしていない。独立20457は当時稼働中だったが、後にstack overflowで終了1。詳細は冒頭。

1. 独立new0のstack overflowを依存宣言・式の分割で特定・改善する。20457は終了1を回収済み。上限を増やしたり同じ長時間検査をそのまま再実行したりして解決扱いにしない。
2. wide候補の公開版への切替を完成させ、元のintサイズ範囲を復元する。補助実行モデルでは構築本体全体とBRepSまで接続済み。次は実確保/Frame/callerとの接続と、旧model依存の整理を進める。
3. slot置換はCoreCommand範囲のrunFuel全体、実15確保は正確なbuffer/Frame/初期配列/16slots、初期scope/base条件の引継ぎと15field/入力のVOKGまで接続済み。入力を含むCVecs全条件と実初期配列のBFreshSまで接続済み。正規化した明示的callのprepare/binding表/FWM/本体/復元までは接続済み。binding表/保存参照のFrame primitives対応と同一scope所有のsoundM_ownedまで追加済み。Container/NExpr全構文のeval view対応まで追加済み。宣言/代入/書込みとleave/releaseのview対応まで追加済み。CoreCommand全体のrunFuelと実wide本体の両view合成まで追加済み。view後の実初期FWM/QSとインラインstage全文まで追加済み。root callerのreadonly入力prepare/Entryも接続済み。stageとroot prepareを含む仕事量/peakの閉じた上界も追加済み。次はchild header入力、class export/寿命とその資源をつなぐ。型検査・構文一致だけで完了としない。
4. 新正本のLean kernel replay/独立監査/全件all/台帳を確認する。全件中は正本を固定し、実terminal0を回収する。
5. 他の旧API/型/機能/入力範囲の違反と未検証ヘッダーを続ける。lazy/segment treeの汎用M/Fと述語検索、Tree全体、SquareMatrixクラス、set/multiset/geometry等、多数未完了。[違反一覧](../experiments_status.md)が現対象。sum版Beatsも別途未検証。

旧SquareMatrix比較/.pow最終二乗の修正候補もcacheにあるが、元ファイルは未修正。Fenwick構築・SquareMatrix単項マイナスはClaude Codeが修正済みで、inventory hash/回帰checkも更新済み。詳細・過去の全ログ/ハンドルは履歴の該当節を検索する。
