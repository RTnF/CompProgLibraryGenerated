# CI修正・リリースの引き継ぎ（2026-11-03）

この文書をCI作業の再開点とする。[全体の引き継ぎ](handoff.md)の過去の「稼働中」は、その時点の観測履歴である。

## 再開時に最初に確認する状態

- **機密確認:** 変更15ファイルの差分/前後内容は検出0。全公開予定treeの1件はverification/statements.jsonのProofs.MultiVecN.rowKeyの公開SHA256指紋で、検証環境のkind/module/type/levels/body/unsafeから再計算して一致を確認した誤検出。reviewed_false_positive.jsonに根拠を保存した。既定ルール・ignore無効化を維持してraw findingを残し、この厳密な照合以外の未分類検出があれば停止する。最終結果はci_fix_supervisor/secret_scan.jsonを参照する。
- **33537/10899はともに全工程terminal終了0。再pollしない。** ローカル重い検査は全て終了済み。33537はPython3.11/cacheなしで59部品/共有235、独立build1790、52238宣言監査、Mathlib778範囲、Lean replay、固定nanoda49092、ZIP成功。10899は子孫回収修正後のcache有効all/ZIP成功、1916入力hash一致。証明入力1005件不変でproof-securityは成功cacheを使用した。反映後に独立kernelを再実行したとは扱わない。
- 10899のall2864.992秒/全2873.037秒、証拠はci_fix_supervisor/{checks_state,final_gate_receipt,input_manifest}.json。ZIP SHA256 `6a1de0f778436f64b13c654b35c1a136b43449910f37f825212feac1b018626e`。33537の証拠はci_fix_py311/、all5432.667秒/全5440.876秒。STL契約定理2件は別区分。
- 子孫回収はtools/process_supervisor.py/check_cache.pyと既存SupportTestsへ正本反映済み、17tests成功。共有登録は235のまま。AST/借用binding保持の修正も含む。リリース準備snapshotとしてgit status/logとCIを照合し、最新差分/公開予定treeの機密検査→stage照合→commit→手動承認付きpush→新SHAのCI/releaseを終了まで確認する。scan_latest_diff.py/verify_staged.pyはci_fix_supervisor/に保存。最新scanは差分/前後内容0、1918ファイル全体の1件を検証用SHA256として照合し、未分類検出0で通過した。raw findingも保存した。
- 修正前push4129afeのCI41757715784は失敗/release skip。まだ修正SHAのCI/release成功は確認していない。全137件の未完了義務は全体handoffを参照する。

## 反映後gate実行時の状態記録（各記録時点の観測）

- **稼働中は反映後gate実10899のみ。** CPython3.11.3、cache有効/jobs1/7200秒、ci_fix_supervisor/check.py。inventory成功、all/ZIPは終了未確認。実handleを確認し、stateだけで再起動しない。
- 10899途中確認: C++59再実行成功、AST59成功cache、共有ログは登録96番目class_copy_auditまで進行。1916入力hash一致。cache有効時は前runのhitも残るので、旧observe_shared.pyのprefix一致を現runの終了根拠にしない。
- **キャッシュなし33537は全工程終了0、再pollしない。** ci_fix_py311/checks_state.json: C++59/AST59/共有235、独立build1790jobs、52238宣言の仕様/公理、778module範囲、Lean kernel replay、固定nanoda49092宣言、59header ZIP成功。all5432.667秒、全5440.876秒、1915入力hash一致。sort契約定理2件は別区分。Zip SHA256 `6a1de0f778436f64b13c654b35c1a136b43449910f37f825212feac1b018626e`。
- **traced停止漏れの修正は正本反映済み。** tools/process_supervisor.py/check_cache.pyと既存SupportTestsへ統合し17tests成功。Linux subreaper/親死亡通知/別sessionの監視役で、別groupへ逃げる子孫と親group SIGKILLも回収する。sourceがcache依存へ記録されることも確認。新たなcheck登録は不要、235のまま。変更のない証明入力1005件のhashを確認して10899を開始した。反映前gateと反映後の成功cache利用を区別する。
- **最新push4129afeのCI41757715784は失敗・release skip。今回の修正は未commit。** 10899終了→機密再確認→commit→手動承認付きpush→新SHAのCI/release完了確認へ進む。詳細と未完了の137件全体の義務は全体handoffを参照する。

## 反映前の状態記録（各記録時点の観測）

- **現在はローカル全件gate実33537のみ稼働中。** CPython3.11.3、キャッシュなし/jobs1/7200秒、ログと状態はci_fix_py311/。inventory、C++全59、AST照合全59が成功。共有全235成功（Python3.11 fingerprintと最終監査への遷移を確認）。最終監査は独立build1790jobs/Mathlib関連778module範囲確認まで成功。監査全体・ZIPは未確認。1915入力は途中照合でhash一致。実handleをpollしてterminal結果を回収するまで同じ検査を再起動しない。
- **最新push4129afeのCI41757715784は終了1、releaseはskip。** watch32873とログ取得26641は終了済み。Python3.11で再現したASTのcapture不具合を修正し、proof build前に軽い境界テストを追加した。修正と借用参照保持証明はローカル未commit。全件gate後に機密再確認→commit→承認付きpush→新SHAのCI/releaseを確認する。

- 追加のtimeout診断でcheck_cache.run_tracedの子停止漏れを実再現した。候補/実結果はtraced_deadline_probe/。単純group停止候補は別sessionの子で失敗したので採用しない。専用subreaper/親死亡通知のprocess_supervisor.py候補はPython3.11/offlineの8ケースとcache連携で成功（prototype_receipt.json）。正本はまだ変更していない。33537終了後に専用groupのkill/reapと回帰を統合・必要な再検証を行ってからcommit/pushする。進行中gateの入力を途中変更しない。詳細は全体handoff冒頭。

## 2026-11-04の状態記録（以下は記録時点の観測）

- **修正後の全件gateは実33537で実行中。** CPython3.11.3からci_fix_py311/check.pyを起動し、inventory終了0、allは`--no-cache --jobs 1 --timeout-seconds 7200`。続いてZIP/package検証、終了時に入力manifestを照合する。ログ/状態はci_fix_py311/。nice19/ionice3/offline/Lean1thread、資源上限は増やしていない。借用参照保持の新module/生成器/回帰もこの作業木に含む。all終了・新commit/push・再CIは未確認。検査実33537以外の旧handleを再pollしない。

- AST失敗をCPython3.11.3で再現・修正した。診断用runtimeはuvでast_trailer_repair/python/へ取得（cacheのみ、3.12既定は維持）。修正前は既存stream3testsが30 failures/87 errors、実Bellman ASTもtruncated。SKIP外側の`*+`だけ`*`へ変更すると3tests成功、実AST95rootsの全サイズ/hashが旧実装と一致（1MiB±1/65537/4093bytes各chunk）。`.github/workflows/ci.yml` に同3testsをproof build前に実行するstepを追加。証拠はast_trailer_repair/{python311_tests.before.log,python311_tests.after.log,reproduction_(3, 11, 3).json,regex_minimal.py,variants311.log}。まだこの修正の全件gate/commit/pushは行っていない。

- **CI 41757715784/watch32873は終了1を回収済み。再pollしない。** scratchの1789jobsは成功（2611.7秒、約44分）、test imports配布後にbellman_fordのnested_bridgeで `ast_stream.root_objects` の `invalid translation-unit trailer` が発生した。今回は7200秒上限ではない。release-headersはskip、リリース未完了。job126337671060のAPIログ取得実26641は終了0、全文は `.cache/wip/release_20261103/job_4129afe.txt`。既存ローカルのAST比較をすり抜けたチャンク境界の可能性を調べる。下の稼働中記録は以前の観測。

- 最新再確認では対象commitの43blob hash一致、現在の引継ぎ2文書の5289bytes差分も機密検出0・終了0。`diff_secret_scan_4129afe/current_worktree_receipt.json` に保存した。この追記は検査後のローカル記録。watch実32873は実handleで稼働を確認し、push約25分後も全件検証工程中。archive/releaseは終了未確認。

- **この文書のcommit後記録:** 現行SHA `4129afe52b30e94585dd2ffd0411586b752b6fe3` を通常pushして終了0。対象[CI 41757715784](https://github.com/RTnF/CompProgLibraryGenerated/actions/runs/41757715784)は進行中。Gitleaks 8.30.1の公式archive/checksumをAPIのSHA256と照合し、network禁止・project ignoreなし・inline allow無視のdefault rulesで、commit範囲/差分全文/変更前後43版を各検出0で確認後にpushした。summaryとtool検証はdiff_secret_scan_4129afe/、watch実32873は稼働中、ログはci_watch_4129afe.txt。このpush後の文書追記はlocal差分として保持する。以下の「未commit」はcommit前snapshot。

- **現行版の全件検証は実56399のterminal終了0を回収済み。再pollしない。** `ci_fix_deadline/checks_state.json` は全工程成功。inventory、登録59部品のC++/AST、共有235項目、固定仕様/公理、Lean kernel replay、固定nanoda、59ヘッダーZIPの内容/単独・結合コンパイルが成功した。
- allは5308.249秒、全wrapperは5316.946秒。独立nanodaは49088宣言成功、stderr 0bytes、export 917517490bytes。監査前の52228宣言の固定仕様/定義・公理依存チェックとMathlib関連778moduleの範囲一致も成功。STL契約依存のsort work定理2件は引き続き契約付きで区別する。
- 検証済み入力1525ファイルは終了後もhash一致。ZIPのSHA256は `6a1de0f778436f64b13c654b35c1a136b43449910f37f825212feac1b018626e`。現行のmode保存付き配布1990partsも、source/destinationのmodeとsize一致を確認済み。
- この記録時点では修正は未commit。機密再走査は1916ファイル・1914内容で検出0、binary/symlink0。APIで確認したremote mainはローカルHEAD/追跡参照と同じ `38e01716c2cce45d7dbfbcbff824b18d56ba6387`。そのCIは失敗・release未更新であり、**リリース未完了**。次は走査manifestとstageの照合→commit→手動承認付きpush→対象SHAのCI/release確認へ進む。
- このローカルgateはbuild/一部チェックの成功cacheを再利用した。cold CIが7200秒に収まるとは断定しない。旧137ファイル全体の検証、元API/汎用性/寿命/Safe/償却等の残件も未完了。
- 旧実51437は制御修正を適用するため手動中断130でterminal回収済み。旧stateの停止前snapshotとterminal_evidenceを保存。ローカル検査は終了済み。commit後のCI監視は上の追記を参照する。

## 修正再開後の検証経過（各記録時点の観測）

- **正本11ファイルへ性能修正を反映済み。** AA/UM/UNは主定理前だけ、ApplyLoopCh8/9/10/11/12/13とCalcLoopCh6はnamespace内で `attribute [local irreducible] gS VVB` を追加。証明・前提・結論・上界・プログラム定義は元のまま。
- opaque_state_probe/実46153終了0、AA46.886秒/UM28.521秒/UN30.406秒（1thread/通常linter/各120秒）。宣言比較1691終了0: AA88/UM64/UN67の名前/型/levels/kind/unsafe/計算定義bodyが完全一致。定理bodyは構造hash参考比較で差0。
- **固定nanoda実93799終了0。** 基礎3公理のみ、2threads/標準stack、export2.202秒/kernel1.201秒、3752宣言成功。kernel_state.jsonと各ログ保存。全件gateの代わりにはしない。
- **state_chunk_probe/実20024終了0。** 7候補はそれぞれ57.686/53.814/51.530/44.254/46.731/40.243/37.147秒で成功。その後正本へ同じ局所設定と理由コメントを反映した。
- **不要simp引数のlinterだけをProofsライブラリと独立監査scratchのLake設定で無効化した。** linter_probe/比較実87676終了0、31宣言の型/計算定義/構造hashを含む比較出力が一致（1,216,641bytes）。元のstyle診断通常18.460秒→無効9.658秒の候補に対応。source audit、公理/固定仕様監査、Lean/kernel replay、nanodaは維持。scratchへ任意のroot設定を取り込む変更はしていない。
- tests/test_beats_capacities.pyに正本AA/UM/UNを新しいoleanへ各120秒/1threadで再コンパイルする回帰を追加（timeoutは専用groupをkill/reap）。この回帰を含め、全件gateで検査する。
- 全件root buildの実ログでもAA43秒/UN29秒/UM27秒で成功した。単独診断だけでなく通常の依存関係下でも型検査を通過。全件の終了、固定仕様、両kernel、CIのcold時間はまだ未確認。
- **実57874は終了1を回収済み（7200.220秒）。** 正本1789jobsは成功したが、共有196/235番目のtest_vector_construction.py中に全体上限。ZIP/全件proof-securityまでは未到達。再pollしない。cold初回の正本995modules表示時間合計は3690秒（修正前CI7053秒とは環境が違うので比率を性能保証にしない）。build_profile.jsonに降順保存。Cpp/bridge59は成功または内容一致cache、共有prefixも成功分cache保持。全件/CI成功とは扱わない。
- 診断の限界: Trueの途中補題abstract_valid/17009は12.443秒成功、対照typed_valid/64129は60秒打切りで、公開証明の代替ではない。古いseparate/packet/typed候補のby decideはfree variableエラーがあり比較対象から除外。比較51873はproof Expr reprStrがDAGを展開し6.9GBになり、生成した巨大出力を除去してaborted_full_proof_dump.jsonへ理由/sizeを記録。定理bodyを全文reprStrしない。
- 続行後の追加診断graph_state_probe: TreeFullDpExecにlocal irreducible gS/VAを加えた候補は20.091秒で終了0（現root build170秒に対する候補）。まだ正本へ未反映。最初のFindCycleOuterはdoccommentとstructure間へattributeを挿入してしまいparse error、117.479秒で終了1。性能比較に使わない。
- run_rest/実41180は終了済み。TopoSortExecのgS/VT候補は96.832秒で終了0だが明確な改善なし、IntervalCallのB6/callerP候補は120.029秒打切り。未採用。
- FindCycleOuterのdoccommentを修正した再診断は実18635。run_restがまだIntervalを検査中に誤って起動して短時間重複したため、速度比較に使わない。実18635は終了0を回収済みだが、Leanは120.037秒打切り/-9で未成功。findcycle_state.jsonに保存済み。今後は前のwrapperのterminalを確認してから次を起動する。
- vector_construction_profile/実85437は終了0、元の2testsは26.222秒で成功。subprocess計測ではLean合計3.412秒、Clang AST3.037秒に対しPython側が約18秒。field検査の集約は見送り、まずast_streamのJSON文字列をPythonで1quoteずつ走査している処理を調査する。全ケース・元の単一Clang processの宣言ID・標準ライブラリ宣言を維持する。この単体計測終了時点では検査なしだったが、その後に下記の全件実51437を起動した。
- AST走査修正を正本へ仮反映。正規表現内で通常文字列/非braceをまとめて走査し、Pythonへbraceと未完了文字列だけ返す。test_direct_file_astへ生bytes/UTF-8/escape長0..16/全chunk1..128/長大文字列/不正trailerの回帰2件を追加し、stream3tests成功。同じClang出力の全95roots（53,718,912bytes）は旧版とSHA256/sizeが全件一致、通常chunkと4093bytes chunkの両方で一致。最初の文字列単位候補は逆に遅く未採用、その後のbulk候補を採用した。vector_construction_profile/実48915終了0、元の2testsは18.819秒（wrapper）、全ケース維持。実測はローカルの診断でありcold CIの保証ではない。
- TreeFullDpExecはtree_checked_probe/実74142で404宣言の名前/型/計算定義一致（proof構造hashも差0）、実50804で固定nanoda4354宣言成功（export2.406秒/kernel1.401秒）。正本へ局所irreducibleと理由コメントを反映した。最初のcompareは出力先置換漏れで旧overlayを参照し無効、最初のexportも環境不足で失敗した。正しい専用overlay/search pathでやり直した結果だけを採用。置換漏れでopaque_state_probeの旧exportログ/kernel_stateを上書きしており、当該ファイルを過去実93799の証拠と見なさない。
- 追加修正: 通常build→独立scratch buildという全件コンパイルの重複を解消する。check_public.build_leanはcheck_proof_security --prepare-test-importsを呼び、source audit→固定Lake設定のscratch build→コンパイル済みimportsだけを通常テスト環境へ一方向copyする。通常projectのolean/traceはscratchへ取り込まない。テスト後の全件監査（固定仕様/公理/両kernel）は維持し、scratchは同じsourceならLakeが再利用する。失敗buildからのcopy禁止、旧module/不要private partの退避、symlink先を更新しないcopy、trace/hash非copyの回帰追加。public_support9件、新しいsecurity回帰5件成功。不正sourceのbuild前拒否とroot設定非混入も確認。copyは元artifactのmodeも維持する。全件起動後の小変更はmode保存/対応回帰のみで、proof sourceは起動後変更なし。全件gateで実経路を確認するまでは未検証とする。
- 新しい全件wrapperは実51437、ci_fix_shared_build/checks_state.jsonとall.txtへ出力中。inventory成功後、独立scratchのsource同期まで到達。nice19/ionice3/1thread/jobs1/offline/7200秒を維持。以降はこの実ハンドルをpollし、stateファイルだけで稼働/終了を断定しない。直近の実pollでも稼働中、ログは947/1351のTreeLcaMathまで到達しており、全件成功はまだ未確認。gate開始後にcopy時mode保持を加えたため、終了後には現行helperでprepare-test-importsを再実行して実配布経路も確認する（scratchは成功済みsourceを再利用、重複cold buildは不要）。
- 続行時の実pollでも51437は稼働中、ログは1071/1367のFindCyclePrepareまで到達。独立scratchの995 Lean sourceは作業木と全件byte一致を再確認し、関連入力1525ファイルのSHA256をci_fix_shared_build/input_manifest.jsonへ保存した。これは進行中gateの入力照合用であり、全件成功の証拠ではない。
- 続行時の機密走査実3593は終了0、tracked/nonignored1916ファイル・1914内容を確認して検出0、binary/symlink0、未push commit0。source_secret_scan.json/source_manifest.jsonに保存。以降の変更とステージ内容はcommit前に照合する。全件実51437は引き続き稼働中、直近の実pollは引き続き稼働中、ログは1092/1372 RunLengthCall。input_manifestの1525ファイルも変更なしを再確認。
- 次の続行ターンもverified wait。実51437の複数回の実pollは稼働中を返し、ログは1217/1386のFindCycleOuterまで進行（当該moduleは成功）。コンパイルエラーは未検出だが、ビルド全体/共有テスト/全件kernel/ZIPは終了未確認。新しい検証は起動していない。
- 実51437の独立scratch buildでTreeFullDpExecは19秒で成功（1331/1789）。候補単体の成功に加え、通常の依存関係下でも採用修正の型検査が成功した。全件終了とは区別する。
- 今回の続行も実51437を同じhandleでpollし、稼働中を確認したverified wait。独立buildのApplyLoopCh13/12/11/10/9/8は67/86/96/64/79/57秒で全件成功、未変更Ch7/6も成功。この後、CalcLoopCh6も1476/1789で55秒成功を確認済み。変更したループ分割7ファイルは今回の独立buildで全件成功。この後AA/UM/UNも50/29/32秒で成功を確認済み。全件gateの終了はまだ未確認。別execのUTC差だけでtimeout/停止を推定せず、実handleのterminalとwrapper内部elapsedを使う。check_publicはmain開始時に7200秒のmonotonic deadlineを設定し、そのremainingをprebuildのsubprocess timeoutへ渡すコードのまま確認済み。
- **独立scratch buildは1789jobs全件成功。** 実51437のallログで `scratch build finished` は4202.2秒。AA50秒/UM29秒/UN32秒、TreeFullDpExec19秒、変更した分割7ファイルも成功して、正本11ファイルの今回の型検査は全件成功。build_profile.jsonへ完了moduleの表示時間を保存した。テスト用importsの実配布も成功してC++段階へ到達し、floor_sum_unsignedまで成功を確認。CPP/bridge59全件、共有235checks、固定仕様/両kernel/ZIPの今回の終了はまだ未確認。mode保持追加後のhelper再実行は全件終了後に行う。
- **C++/bridgeは今回も59部品全件成功、実51437は共有テストへ到達し稼働中。** 監視中にcheck_leanの最終監査へdeadlineが渡っていない既存不備を見つけ、残時間のcache前後確認と、残時間付きrunを通すよう修正した。runは専用process groupを作り、timeout時にexporter/kernel等の同group子孫もkill/reapする。public_supportは実5147で15件成功（1.114秒）。/proc状態読取の消滅raceもその後処理した。入力manifestとの差はtools/check_public.pyとtests/test_public_support.pyの2件のみ、Proofs/C++/verifier入力は変化なし（control_changes.json）。実51437は旧制御コードで開始しているため、この結果だけで追加deadline修正の統合成功とはしない。実51437のterminal後にcheck_ci_fix_deadline.pyを実行し、mode保持追加後のprepareもそこで確認する。新しいwrapperは作成済み・未起動。
- **実51437は手動中断130でterminalを回収済み。現行版は実56399で開始した。** 旧stateのbefore_interrupt snapshotとterminal_evidenceを保存。CPP/bridgeの成功名集合はregistryの59部品とそれぞれ完全一致した。制御変更はcheck_public/test_public_support/test_beats_capacitiesの3件のみで、Proofs/C++/verifier入力に変更なし。中断時にも所有process groupをkill/reapし、Beatsの単独Lean検査も中断時にcleanupするよう補完。public_supportは実36027で16件終了0（1.104秒）。現在入力1525件のhashはci_fix_deadline/input_manifest.jsonへ保存済み。mode保持後の実配布と新しい監査deadlineは実56399の全件gateで確認するため、別のprepare実行は不要。全体7200秒/jobs1/Lean1thread/offline/nice19/ionice3を維持。旧実行の成功範囲を、現行版全件の成功やcold CI成功とは扱わない。
- **現行実56399もCPP59/bridge59が全件成功し、共有テストへ到達。** 独立buildは成功済みcacheを再利用して7.9秒で終了、現行mode保存付きimports配布を実行した。995 source由来の配布1990partsについてsource/destinationのmodeとsize一致を確認し、import_publication_receipt.jsonへ記録。byte同一の新たな全件hash検査を主張するものではない。入力manifest1525件も変更なしを確認。cold CIの所要時間の証拠とは区別する。
- 続行時も実56399を実handleでpollし、稼働中を確認。成功時の共有テスト出力は捨てられるため、単体所要時間は旧allログから復元できなかった。代わりにsnapshotしたcheck-resultsを現在入力のfingerprintで照合し、先頭16/235項目が一致（最後はtest_disjoint_set_getter_call.py、次の未確認はtest_context_method_selection.py）。shared_prefix.jsonへ保存。過去runと同じ入力の成功cacheも含むため、新規実行16件や全件成功とは主張しない。変更後のBeats容量検査もこの一致prefixに含まれる。
- 次の続行でも実56399の実pollは稼働中。現在入力と一致する共有成功prefixは31/235へ進行（最後test_uf_object_query_amortized.py、次の未確認test_uf_object_total_peak.py）。照合はローカルのpoll_shared_progress.pyへまとめて出力量を抑えた。helperはcache読取snapshotだけを使い、実handleのliveness確認の代わりにはしない。共有検査後の全件監査/ZIPの終了は未確認。
- 続行中も実56399の実handleは稼働中。現在入力と一致する共有成功prefixは先頭183/235（最後test_nested_ir_oracle_0.py、次の未確認test_nested_ir_oracle_1.py）。helperは上限235を指定して照合し、shared_prefix.jsonへ記録。全件監査/ZIPは終了未確認。検証入力の編集や検査の重複起動は行っていない。
- **共有235項目を通過し、全件proof-securityへ到達。** 先頭235/235の現在入力一致cacheに加え、共有検査後だけに実行する監査側buildの開始をallログで確認した。2回目buildはcacheを再利用して12.1秒。Mathlib関連778moduleの監査範囲一致、52228宣言の固定仕様/定義・公理依存監査が成功。登録STL契約依存のsort work定理2件は契約付きとして区別したまま。Lean kernel replayは監査開始109.6秒時点で開始（171 changed modules、1 covering prefix）し、直近の実pollも稼働中。独立nanoda/ZIP/全件wrapper終了は未確認。235の成功を旧137ファイル全体の完了とは扱わない。
- 追加の確証を得てから全件gate/固定仕様/両kernel/ZIPを確認し、機密走査/commit/承認付きpush、そのSHAのCI/release-headersを追跡する。上限は増やさない。**リリース未完了。**

## 修正再開前の状態（経過履歴）

- 機密走査、ローカル全件検証、59ヘッダーZIPの検証後にcommit・pushを実施済み。ただし最新CIは失敗し、ヘッダーRelease更新はスキップされた。**リリース完了ではない。**
- ローカルHEAD・origin/main追跡参照は `38e01716c2cce45d7dbfbcbff824b18d56ba6387`。実リモートの現時点の先端は再開時に確認する。
- 最新の停止原因は、初回Leanビルドが約118分を消費し、続くC++検査で全体7200秒制限に達したこと。上限・メモリ・stack・heartbeat・並列数は増やしていない。
- 最適化候補は `.cache/wip/release_20261103/` 内だけ。**Proofs正本、C++、固定仕様、公理、検査器は今回の診断では変更していない。**
- 未commitの引継ぎ文書と、公開対象から除外したローカル `MEMORY.md` を保持する。reset/cleanしない。
- 公開59部品の成功と、旧137ファイル全体の検証完了を区別する。元API・汎用性・Beatsのcaller AST/寿命/Safe/償却等の残件は引き続き未完了。

## push済みの変更とCI

| コミット | 内容 | CI結果 |
| --- | --- | --- |
| `3aaa6e6` | Claude Code/Codexの既存成果、公開59部品、class copy資源証明を収録 | [41594742022](https://github.com/RTnF/CompProgLibraryGenerated/actions/runs/41594742022): container内のGit所有者チェックで検証開始前に失敗 |
| `e62828c` | CIの `GITHUB_WORKSPACE` だけを `safe.directory` へ登録 | [41595322068](https://github.com/RTnF/CompProgLibraryGenerated/actions/runs/41595322068): C++59部品/AST照合は成功。共有テストがLean buildより先にimportし `unknown module prefix Proofs` |
| `38e0171` | `build_lean()` を共有テストより先に実行し、テスト後に証明監査。順序とbuild失敗時停止の回帰を追加 | [41603164208](https://github.com/RTnF/CompProgLibraryGenerated/actions/runs/41603164208): build1789jobsは成功。その後 `cpp:floyd_warshall` のsanitizer compile中に全体時間制限 |

- 所有者修正は一時repoと `GIT_TEST_ASSUME_DIFFERENT_OWNER` で登録前拒否・登録後成功・別repo拒否を確認済み。
- `tests/test_public_support.py` は追加2件込み8tests成功。
- `tools/check_public.py` は `build_lean()` と証明監査 `check_lean()` を分離した。cpp/bridgeの部分モードではLeanをbuildしない。
- pushはすべて通常の `git push origin main` で手動承認後に終了0。次のpushにも [git-push.rules](../../.codex/rules/git-push.rules) の手動承認が必要。[git_workflow](git_workflow.md)に従う。

## ローカル検証・機密確認の証拠

共通の作業ディレクトリを `.cache/wip/release_20261103/` とする。以下のパスはそこからの相対パス。

- `checks_state.json`: 初回リリース前のinventory/all/package/archiveが終了0、987.181秒。
- `order_fix/checks_state.json`: 順序修正後も全工程が終了0、3157.625秒。allは3149.547秒、59部品/共有235checks、Lean build1789。変更のない正本のproof-securityは成功cache。ZIP単独・全体includeのcompile/実行も成功。
- 上記はビルド済み成果物のあるローカル結果。**キャッシュのないCIの所要時間を保証する結果ではない。**
- `scan_sources.py` と `source_secret_scan.json`: 秘密値を出力しない走査。作業木と未pushコミットのblobを確認し、各commit前の検出0。初回ステージ全1914ファイルは走査manifestのSHA256と一致した。
- `.cache/`、`.tools/`、`.lake/`、`benchmarks/local/`、`MEMORY.md` はステージに含めていない。
- 初回の巨大ステージには引継ぎ済みファイルの行末空白/末尾空行の警告があった。無関係な整形はせず `staged_whitespace.txt` に記録した。後続CI修正の差分checkは成功。

## 最新CIの性能診断

- `job_38e0171.txt`: ジョブ125806488498の全文、58,749,084bytes。約61万行あるため丸ごと表示しない。
- 通常の `gh run view --log-failed` はHTTP/2 CANCEL、HTTP/1.1再試行もunexpected EOFとなった。最終的に `gh api repos/RTnF/CompProgLibraryGenerated/actions/jobs/125806488498/logs` のストリーム保存が終了0で成功した。空の `ci_failed_38e0171.txt` を診断結果と誤認しない。
- `Build completed successfully (1789 jobs)` は10:26:53 UTC、時間切れは10:28:16 UTC。ビルドは失敗していない。全体検証は完了していない。
- 初回buildの994 Proofs modulesの表示時間合計は約7053秒。主な遅い部品は下表。

| module | CI表示時間 |
| --- | ---: |
| `Proofs.BeatsExecAA` | 1006秒 |
| `Proofs.BeatsExecUN` | 623秒 |
| `Proofs.BeatsExecUM` | 566秒 |
| `Proofs.IntervalCall` | 296秒 |
| `Proofs.TreeFullDpExec` | 224秒 |
| `Proofs.FindCycleOuter` | 142秒 |
| `Proofs.TopoSortExec` | 118秒 |

### 実施した診断と限界

すべてnice19/ionice3、単独・1thread、通信禁止で実行。120秒診断のtimeout時は専用process groupをkillしreapする。結果JSONの `timed_out` と `exit_code` を確認し、wrapper自身の終了0をLean成功と混同しない。

| ディレクトリ | 結果・注意 |
| --- | --- |
| `linter_probe/` | CalcLoopIterDset: 通常18.460秒/警告2,306,987bytes、`-Dlinter.unusedSimpArgs=false` で9.658秒/7,883bytes。ソース・資源上限は同一。AAは両設定とも120秒で打切り。linter無効化だけでAAが改善したとは言えない |
| `linter_probe/compare.py` | linter前後の宣言の型・証明本体を比較する補助。初回はCompareDeclarations.leanのList.qsort不足で失敗。Array.qsortへ修正したが再実行していない。**意味不変の比較は未完了** |
| `cost_context_probe/` | AA/UM/UNの最後の `simp at *; omega` のcontextを費用/領域仮定だけに限定。AAが120秒で打切り。他2件は未実行 |
| `cost_context_narrow/` | 小さい `(by omega)` も `clear * - hnv` で絞る候補。初回は補助補題にhnvがないのに置換しており診断不適切。主定理 `aa_exec`/`umm_exec`/`unm_exec` 内だけへ修正済み。修正後の単独成功は未確認 |
| `cost_context_trace/`, `cost_context_trace_fixed/` | 前者はIO名/hnvの診断コード不備を含む。後者のstdout/errも定理完了までbufferされており、出力が止まった行を実際の停止地点と扱わない。両方終了済み |
| `cost_context_trace_file/` | 通過地点を `progress.txt` へ直接書く診断。AAの最初のwrite（元source209行）から次のwrite（216行）までにも時間を要した。120秒で打切り、最終地点216行。証明の途中にIOを入れた診断専用であり正本へ移さない |
| `cost_context_bounds/` | narrow候補に加え、小さい `by simp [vwp,...]; omega` の資源上界証明も必要な仮定へ絞る。AA9箇所、UM/UN各6箇所。終了結果は下記の最新診断状態を参照 |

### 前回引継ぎ時の診断終了状態

`cost_context_bounds/run.py` の実35752は終了結果を回収済み。AAは120.025秒でprocess groupをkill/reapし、Lean終了コード-9、timed_out=true、ログ0bytes。wrapper自身は終了0だが、Leanの成功ではない。UM/UNは未実行。`cost_context_bounds/state.json` に記録済み。**引継ぎ時点で、この作業の検査・CI監視・ログ取得はすべて終了しており、稼働中の検査はない。**

実行ハンドルはこの会話固有であり、別エージェントが同じハンドルを操作できると仮定しない。再開時は結果ファイルと実プロセスを突き合わせ、動作中の検査と重複起動しない。

## 次の作業

1. 機密再走査と対象差分を確認し、検証済み入力からの意図しない変化がないことを確認する。`MEMORY.md` と `.cache/`、`.tools/`、`.lake/`、`benchmarks/local/` をstageしない。
2. 対象ファイルだけstageし、走査manifestとindexを照合してcommitする。固定root/型/計算定義の判定やテストケースは緩めない。
3. `.codex/rules/git-push.rules` の手動承認を得て通常の `git push origin main` を実行し、**そのSHAのCIとrelease-headersの終了結果まで追跡する。** CIが時間切れなら上限やメモリを増やさず、実ログから残る負荷を改善する。
4. Release本文のverified commitと59ヘッダーassetを確認してからリリース完了と報告する。旧137件全体の目標は引き続き継続する。

## 終了済みハンドル

再pollしない: 全件17394/96035/72559、CI watch27532/7099/36152、log取得46586/95011/24083、診断29284/11922/62549/8847/48438/2871/95008/28181、初回宣言比較28178、最新診断35752、再開後の26318/66144/32940/34348/70620/28659/7091/13694/12357/78832/64320/31792/48174/17009/64129/46153/51873/1691/93799/20024/87676。全件57874（時間切れ1）、51437（中断130）、56399（成功0）も終了済み。再pollしない。

古い段階の「稼働中」記述より、この文書の最新状態を優先する。
