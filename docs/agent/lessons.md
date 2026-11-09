# 作業上の教訓

## 2026-11-08: recordの条件付き返却は選んだ全fieldをコピーする

- 返却式がconditionalでも、外側はimplicit copy constructorになり得る。実ASTのconstructor signature・NoOp const化・lvalue分類と各parameter/fieldの宣言を確認する。値構成子で再構築するとnoop等の状態を落とす。
- 条件は一度保存し、同じ判定で全fieldを選ぶ。既存inlinerのscalar conditional展開を新経路だけに使い、未選択operandを前置しない。NestedBodyがConditionalOperatorを直接扱えると仮定しない。
- 条件付き返却を追加しても、nontrivial copyや副作用付き条件・入れ子条件等の未対応境界を消さない。readonly入力からのcopy先の権限は元fieldとtargetConstで決める。

## 2026-11-08: record値引数を参照として渡さない

- trivial recordの値引数も、元のfield順で値をcopyしてからcalleeを実行する。参照引数のfield viewとmetadata/ABIを区別し、元のreadonly fieldでもコピー先の通常値引数は使えるようにする。nontrivial copyをscalarコピーとして省略しない。
- object wrapperは全入力の型・個数・値・参照権限をcaller上で検査してからprepareへ進める。値snapshotをcalleeの確保と交互に作ると、不正な未来slotが入力として有効になり得る。mixed value/referenceとaliasも検査する。
- 明示的なRecord(...)はCXXFunctionalCastExprのConstructorConversionを挟む場合がある。実ASTを確認し、このcastだけ内側の構築へ進む。構成子signatureとselected recordの照合は残す。

## 2026-11-08: factoryの標準呼出し監査とconstexpr選択を共用する

- 構成子引数のstd呼出しも、通常の本体と同じTUの宣言ID・pristine body監査を通す。名前だけの許可を増やさず、最終stageでも元callを保持してnumeric_limitsのpointer/value probeとmin/max監査を行う。
- sole if constexprの選択はcompiler-resolved bool ConstantExprだけに限定する。runtime initializerやcondition variableは捨てず拒否する。構成子専用経路だけで選択すると、同じ原本を読む既存のfield投影で退行する。rootとcalleeのinlinerにも共通処理を使い、両経路を検査する。
- 新しい一般証明は単独compileしてから重い登録検査へ進む。失敗時はfailfastで止め、raw logと実終了コードを保存する。実行中の入力を固定し、観測の切断だけで同じ検査を再起動しない。

## 2026-11-08: friendの本体証明を実callerの全field exportまで接続する

- readonly参照4個でも型が混在する。各scalarCellからmemory内のtyped値/有効性を得てcallerPへ保持し、prepareのfield参照と本体の入力bindingを合わせる。aliasや負sizeを排除して証明を簡単にしない。
- 本体の結果memoryだけではtyped exportへのQS接続に足りない。入力readonly bindingとfresh field bindingを含むPS全体の一致を記録し、元参照先と生成fieldの位置を保つ。scopeでbindingを回収する補題では、局所定義も展開して一致を確認する。
- 本体のpexec成功だけで呼出し全体を検証済みとしない。StraightLine.sound/runFuel、callee scope回収、typed field capture、const制限、旧scalar/vector観測の保持、ObjectRef wrapper、work/peakを接続する。
- 同じ証明を別familyへ再利用するときも、元の宣言とwitnessからモデルをfresh生成し、両方をkernel/nativeで検査する。元のCPP型を統合して証明の一致を作らない。
- Leanは `error(lean.unknownIdentifier)` の形式でもエラーを出す。`error:` だけのfilterが空でも成功とせず、実returncodeとraw logを必ず照合する。

## 2026-11-08: record参照を全fieldで検査してから返却objectを構築する

- friendのrecord参照を1fieldの投影で代用しない。元parameter/memberの宣言IDを照合し、const/mutableを保って全fieldの参照へ変換する。record値引数のcopy/moveは別の義務であり、参照として受け付けない。
- ObjectRefは全fieldの個数/型/値/権限をcaller上で先に検査する。callee確保後に存在し始めるslotを入力と誤認しない。typed viewの検査と、厳密なclass identity/lifetime証明を区別する。
- 新しいfriend対応は明示opt-inにする。未対応の値渡しfriendがあるために、以前から使えるstatic factory exportまで拒否しない。本体の任意入力pexec証明と、callerのprepare/run/export一般定理を別の義務として記録する。

## 2026-11-08: factory返却ではmaterializeした全fieldを直接exportする

- 委譲構築のfactory内で全fieldを作る処理と、factory自体を呼ぶ処理を共用する。factoryの返却objectをexportするときは、field別の再評価や外側構成子への追加moveで代用しない。同じfieldの宣言ID・型・mutable属性をcopy auditと照合する。
- factoryのstageには元factory bodyのrangeを保持する。合成CompoundStmtにrangeがないとNestedBodyのscope終端が取得できず、model生成が止まる。本文は構成子由来でも、stageのsource由来の情報を欠落させない。
- 元factoryのclass返却と、内部unit stageのcallFuelを混同しない。任意callerの検証はprepare/runとtyped exportをつなぎ、未使用の構成子引数の失敗やbodyの失敗を含めて、完成していないobjectをexportしないことを確認する。

## 2026-11-08: receiverの置換と未使用return式の評価を保持する

- factoryの構築bodyがmethodを呼ぶとき、外側constructorのfieldをreceiverとして流用しない。materializeした全fieldを明示引数にし、入れ子の呼出しも同じfieldへ結び付ける。通常のinlinerでも、calleeの元のfield仮引数IDを次の呼出しへ渡さず、現在の実引数へ置換する。直接構築とfactory経由、const getter、caller prefix、失敗例を確認する。
- 副作用のないreturn式でもゼロ除算や符号付きoverflowが起こる。呼出し側が戻り値を捨ててもreturn式を評価する。代入・callがないというpure判定は式の省略を正当化しない。成功値だけでなくfaultとC++/UBSanの失敗も回帰する。
- thisへの呼出しでは元receiverを継承する。readonly fieldのhelper ABI上の値captureを新receiverにすると、Beatsのn/inf読取slotだけが変わり、既存生成modelとの一致が崩れた。差分を6関数のslotへ絞り、元receiverを保つ修正でconstruction-stage/bodyのbyte一致と構築中alias/入れ子呼出しの両方を回帰した。既存modelを再生成して差を隠さない。
- `long long &get()` のcall式の型は `long long` でvalueCategoryがlvalueになる。ポインタ/参照返却を対象外とする場合、call式の型だけでなくexactなmethod宣言の返却型を確認する。

## 2026-11-07: scalar構築後の既存vector内容を別途保持する

- FAのobject数/live/workやSameHeadersのsignature保持は、buffer要素値の保持を意味しない。scalar-onlyの実行についてforest/storage.objects/baseSpace/rootWritableを保つ共通定理を作り、prepare/body/exportを通した不変条件へ含める。旧frame bindingの復元と合わせてExtendsへ接続し、既存vectorのresolve/readを確認する。
- scope回収では既存ownerが外側scope以下にあることから回収対象がfreshと示す。frameのbinding切詰めで構造体の添字全体が変わる場合、Contentsの各field等式を再構成し、同一frameと扱わない。

## 2026-11-07: 委譲構築のfactory返却値は全fieldを1回だけ作る

- `Ctor():Ctor(e())` のASTはclass返却からのmove/copyを含み得る。factory側の引数と全field、構成子bodyを先に実行し、全fieldをtargetへ移してから外側bodyを実行する。field投影を別々に実行して代用しない。未対応の特殊メンバーやreceiverは拒否し、任意T/lifetime完了としない。
- delegation prefixにCompoundStmtがある。cloneではprefix/初期化子/bodyを別groupとして保持し、最初のCompoundStmtをbodyと誤認しない。bodyに値変更のあるfactoryと委譲chainで戻り値だけでなくcaller prefixと一時回収を確認する。途中returnは内側call境界がないまま埋め込まない。
- constructor stageを作った後のhelper収集でconstructor自体を旧形式へ再変換しない。method-onlyの入口を明示し、既存constructor入口の既定動作を保って回帰する。

## 2026-11-07: 条件式の呼出しは選択branch内で展開する

- 条件式内の構築や既知helperを単純に前置すると、未選択側の副作用やゼロ除算も実行する。整数prvalueは結果localとIfStmtへ変換し、条件を一度評価してoperandの処理をbranch内に保つ。参照/object結果やloop/short-circuitは別の対応が必要なので拒否を維持する。
- 回帰ではbranchの戻り値だけでなく条件/operandの実行回数と元callerメモリを確認する。失敗例は単にfinishedでないだけでなくfaultを要求し、fuel切れを成功扱いしない。
- 生成モデル数を証明済み数としない。原本の各宣言から登録rootを照合したところ、Add/MaxMinのcompose一般callerの登録漏れが見つかった。値渡しと元の型範囲を保った定理を追加し、freshモデルと固定kernelで検査した。

## 2026-11-07: record名を含む型をrecord自身として消去しない

- 型名の正規表現searchでclass membershipを判定すると、unusedな `Probe *`、`vector<Probe>`、配列参照の引数をscalar fieldに変換できてしまう。原本CPP/native/UBSanが成功する3例で、生成ABIの誤りを再現した。全件gateの成功は未登録の型境界の証拠にならない。
- canonical/desugared typeの全体を、record自身と許可したトップレベルconst/参照修飾に限定して照合する。引数だけでなく返却型と局所宣言も検査し、methodの返却署名は型名を書き換える前に検査する。pointer/vector/array/function pointer、複合返却型/局所宣言と単一/複数fieldの18ケースを登録した。
- 拒否テストは意図した境界へ到達させる。pointer/vector返却のfixtureがconstructorを使わないと、未具体化のconstructor本体による先行拒否になった。witnessでconstructorも具体化し、拒否理由を固定して検査する。既存の意味対応やCPPのAPIを狭めてテストへ合わせない。

## 2026-11-05: scalar消去はhelperの寿命と初期化順も検査する

- 委譲先のクラスだけtrivial copy/dtorを確認しても、factory内の別helperの独自copy/dtorは消せてしまった。1bitのfieldも格納幅を省くと、C++の-1をモデルが1として受理した。C++実行と生成モデルの `by decide +kernel` /固定nanoda2523宣言で不一致を確認した。
- 全ての消去対象recordでtrivial copy/move/dtor・baseなし・bitfieldなしを確認する。元CPPの機能削減で合わせず、未対応の効果はobject/lifetime経路の残件として保持する。複数fieldのliteral factoryでも、置換後fieldだけでなく未使用を含む置換前の全構成子引数を調べる。unused randは置換すると消えてしまう。 非委譲の一般投影でも、未使用引数の純粋な算術は失敗し得るため、局所宣言として必ず評価してからfieldを返す。7/nの成功・ゼロ除算を両fieldのモデルで確認する。
- 初期化式をbody後のreturnへ移すだけでは、bodyが引数を書き換えると別の値になる。状態変更/field参照を伴う単一field構築は先に局所fieldを初期化し、その同じfieldでbodyとreturnを実行する。引数だけ/fieldだけ/両方の変更をnativeとモデルの結果・caller保存・work/peak上界で比較する。body内の別helperの構築も呼出しであり、直接の代入/CallExprだけを調べると見落とす。CPP1/IR2の不一致を固定nanoda2517宣言で再現し、構築呼出しも含める修正後の5ケースを固定nanoda2529宣言で確認した。証拠は`.cache/wip/scalar_erasure_effects_20261105/`。既存gateの成功を、新しく見つかった未登録境界の正しさの証拠にしない。

## 2026-11-04: max不等式の証明探索で大きいstateを展開しない

- IntervalCallのprep_refs6は、`repeat first`で`Nat.le_max_left`を目標全体へ試すたびに、失敗する定義的等価性比較が入れ子のcharge stateを展開していた。単独profileではファイル全体233.125秒の大半がこのexact探索だった。
- `refine Nat.le_trans ?_ (Nat.le_max_left _ _)`で外側のmaxから先に一致させ、既知の段数だけ進めて最後の不等式を閉じると2.922秒になった。同じ前提・結論の2定理を固定nanodaで2156依存宣言まで確認した。単純なomegaへの置換も71秒へ短縮したが、oleanが約1.9MBから20.6MBへ膨らむため採用していない。証拠は`.cache/wip/ci_timeout_20261104/`。
- CIの7200秒timeoutは、直前に表示されたテスト固有の無限ループを意味しない。独立buildと先行検査が消費した時間を分け、各checkの開始・終了・所要時間をflushして記録する。時間枠や並列数の増加で回避しない。

## 2026-11-04: timeout時は別sessionの子孫も回収する

- `check_cache.run_traced` のsubprocess.runはtimeoutで検査Pythonだけを止め、子が後からmarkerを書いた。単純なkillpgも、別sessionを作る検査の子では漏れた。通常の親子だけを使う回帰では、この停止漏れを検出できない。
- 専用のLinux監視プロセスをsubreaperにし、親死亡通知を設定して別sessionで動かす。検査終了・timeout・割込み・親groupのSIGKILLでも子孫をkill/reapし、cleanup完了の記録から実コマンドの終了コードを親へ返す。監視設定とprocfs確認に失敗したら実コマンドを開始しない。
- 通常/別sessionの子、成功後の残子、親の強制終了、stdin/stdout、失敗コード/負signal、cacheの成功のみ保存を確認する。停止用例外はtrace hookのexcept Exceptionに飲まれないものにする。証明sourceが変わらない場合でも、反映前gateと反映後のcache利用を区別して記録する。

## 2026-11-04: CIのPythonでもAST境界を先に検査する

- CI41757715784は独立Lean build成功後、ASTのinvalid translation-unit trailerで停止した。CPython3.11.3で同じ境界テストを実行すると30 failures/87 errors、同じBellman–Ford ASTも切断扱いになり、3.12では通った。skip正規表現の外側をpossessive repetitionにすると、後続の未完了文字列のcaptureが3.11でNoneになる最小例を確認した。
- 外側だけ通常のgreedy repetitionへ戻し、文字列内部のpossessive runと生bytes保持は維持する。3.11でも不正文字列の拒否と全境界テスト、実AST95rootのサイズ/hash一致を確認する。CIではこの軽い検査を全件proof buildより先に置き、ローカルPythonだけの成功をCI互換性の証拠にしない。

## 2026-11-03: member copyは元slotを確保前に全件検査する

- 宣言順にfieldを追加すると、初期状態では存在しなかった不正source slotが後のcopy時に有効になり得る。各fieldを実行直前に調べるだけでなく、元ObjectRefの全sourceを最初の確保前にkind/typeとともに検査する。scalar-firstの実クラスで、後からvector/scalarとして読める不正slotを指定する回帰を追加した。
- const viewの権限制限とcopy先の権限決定を混同しない。const sourceから新しい通常オブジェクトを作る場合、コピー先のnonconst fieldは書込み可能になる。新規root/cellを作り、元の宣言とコピー先のconst/mutableから権限を設定する。copy先を変更しても元のvector/scalarが変わらないことを、実slot/ownerとC++の両方で確認する。

## 2026-11-03: const構築の権限は本体終了後に制限する

- constオブジェクトでも構成子の本体は通常fieldへ書き込める。targetConstを構築段階の一時bindingへ先に適用せず、本体終了後のfield capture/exportで宣言のconst/mutableに従い制限する。要求したTrue権限は元bindingでもTrueであることを検査し、owner/element/header・値を変えない。
- caller scalarは元callerの古い値に戻さず、構築後calleeの更新済みprefixを保持する。const exportで追加fieldをreadonlyにしても、元readonly別名は同じ更新済みcellを読み続ける。構成子内の書込み/return;、mutable更新、権限非昇格、既存alias保持を回帰に含めた。共通部の3037依存宣言は固定独立kernelでも標準資源のまま成功した。

## 2026-11-02: 深い生成命令列は定義共有で分割する

- 複数vectorクラスのBeats bundleを標準のLean深度で検査すると、apply_op/chmin/chmax/add_val/update_valの大きいsequenceで深度超過した。生成器の従来のmaxRecDepth設定を新経路へ引き継いで回避せず、右結合のsequenceを32命令ごとにprivate Command定義へ切り出した。
- 命令木・順序・scope・課金を変えず、参照先を展開すれば同じ項になる。分岐の両側に70代入があるC++から、分割前後のNProgram全体のrfl一致を検査した。Beatsの全構築・メソッドbundleも67個の共有定義で標準上限の型検査に成功した。既定生成経路の出力は維持する。
- class_copy_layoutで構築段階を直接作る経路にも、同じclassのthis helper呼出しを既存inlinerへ渡す必要がある。通常のlower_sourceが展開できても、別の構築frontendで同じ準備が済んでいるとは限らない。構築時helper、外部参照の更新、field自身への別名を同じ実クラスの回帰に含める。

## 2026-11-02: 大きな係数を含むomega証明項の独立検証

- Beatsの旧構築CallはLeanでは通ったが、固定版nanodaでは12450秒後に16MiBのstackがoverflowした。宣言別のログで依存6579宣言が終了し、構築Call本体だけが残ることを確認した。診断コピーの引数別ログでは、最後の仕事量上界の `by simp; omega` の証明項の推論中にoverflowした。
- `cost ≤ bound` から `cost+2*16+0+2 ≤ bound+34` を示す小補題を先に証明し、具体的な `bound = 4*n*45414+100` へ適用する形にした。大きな係数を含む算術証明項を作らず、元の前提・結論・費用上界・checkerのstack上限を保てる。旧版と容量分離版の両構築Callの6824宣言が、未改変nanodaでexport込み約14秒で通った。
- Lean buildの成功だけで独立検証も軽いと見なさない。宣言→引数→証明項と絞り、具体的な大きな式を抽象的な値の小補題へ渡す。診断用に変更したcheckerは成功判定へ使わず、最終確認は固定版で行う。両Callの独立回帰はtest_beats_capacities.pyに追加した。
- 証明項の分割でcompiler生成の `_proof_*` が再利用・改番されると、手書きの定理を変えなくても固定root/型hashが変わる。今回の全件gateは234checksと両buildの後、root一致で停止した。旧ソースを別のmodule出力へ再構築して旧hashと照合し、束縛名だけを除いたExprの構造比較で旧3補題の命題が新補題/既存wr_new0へ保持されることを確認した。他の公開定理・計算定義は変更0を確認してから、compiler生成root1削除/hash2更新だけを同期した。--accept-changedの一括使用やroot一致検査の緩和はしない。

## 2026-09-29: push 後の GitHub Actions 確認漏れ

- 症状: Associative Array の実装を push した後、ローカル検証が通ったことだけを報告し、GitHub Actions の結果を確認しなかった。後で確認すると CI は失敗していた。
- 原因: `gcc:13.3.0` コンテナ内の `run` は `sh` で実行されたが、テスト手順に Bash 専用のプロセス置換 `<(...)` を使っていた。ローカルでは Bash で試していたため見逃した。
- 修正: 期待出力と実際の出力を一時ファイルに書き、`diff -u` で比較する POSIX `sh` 対応の手順に変えた。ローカルでも `sh -e` で確認した。
- 次回: push 後は対象コミットの Actions 実行が完了するまで確認する。失敗時はジョブとログを読み、修正後に再度 push して新しい実行を確認する。CI のシェルとコンテナを読んでから同じ条件でテストする。

## Git 操作と承認

- 所有者が異なるリポジトリでは `git` が `dubious ownership` を報告した。ユーザーの指示を受けて、このリポジトリをグローバル `safe.directory` に登録した。設定が必要かは `git status` で確認する。
- この環境の `.git` は通常のサンドボックスから書けない。ステージやコミットで権限エラーが出たら、定められた昇格手順を使う。
- CI 修正後の push は自動承認レビューに拒否された。拒否されたコマンドを別の書式や別ツールに置き換えて回避しない。未 push のコミットを保持し、拒否された操作と理由、ブランチの状態を報告する。

## ベンチマークと検証

- ローカルのマシン情報と実測値はコミットできない。記録自体は `benchmarks/local/` に残し、`git check-ignore` とステージ済み差分で追跡対象に含まれないことを確認する。リポジトリには入力の出典・生成法・ハッシュ、測定手順、再実行スクリプトを残す。
- Library Checker の公式ケースは、公式リポジトリのコミットを固定して生成し、`hash.json` で入力と正解出力を照合した上で測る。出力の一致と処理時間は別々に確認する。ローカルで公式ケースを通しても、ジャッジでの AC や実行時間を断定しない。
- 公開ライブラリでは C++ ソースを正本とし、AST 対応チェック、Lean 証明、C++ テスト、ライブラリ内のテンプレートと部品を順に include した確認を揃える。STL 契約と C++ から Lean モデルへの意味対応は信頼前提として明示する。
- コンテストの適用ルールを先に確認し、この環境からコードを提出しない。

## 2026-10-16: 自然数に特殊化した評価証明のkernel深度

- 構成子の評価器をNat nからIntへの変換値で直接simpすると、1変数の読取りでもkernel deep recursionになった。深度上限を上げても解消しなかった。数値範囲・定数・変換補題単独は成功しており、限界値だけを原因と決めつけない。
- 同じ読取りを一般Int値で証明し、Natの変換値へ定理を適用する形は成功した。Proofs/UfConstructionStage.leanのargLocals/env_argument/eval_argument/eval_count/eval_check、抽象stateのdeclare_valueへ分離して構成子全体の型検査を通した。再現には.cache/wip/UfEnvironmentProbe.leanを使った。
- 直接展開に依存した深い証明は、最小の失敗例を作り、抽象的な値/stateでの小さな補題を先に証明して再利用する。成功した実行を前提にする形へ弱めたり、カーネルを迂回する評価を使ったりしない。


## 2026-10-22: forest の文脈計算と再帰 simp

- Forest.context/rootOwner/lookup を同時に simp へ渡すと、未知の owner を含む分岐で rootOwner の再帰展開が loop し、最大再帰深度に達した。上限を上げて回避しない。
- 既知 lookup と parent=none から rootOwner を一段だけ rewrite し、context_of_root/context_of_none の小補題を作って利用した。有限表の各ケースでは、この補題を適用してから scope の不等式を処理する。再現・修正は .cache/wip/CppMoveRestore.draft.lean/check_cpp_move_restore.py にある。

## 2026-10-22: readonly fieldの値捕捉と外部参照alias

- method内でfieldへの直接代入がないことだけでは、その値がcall中に不変とは限らない。inspect(int& value)がvalue=9の後にcountを読むとき、inspect(object.count)ではcountも更新される。fieldを古い値で渡すとC++とモデルの返却値が異なる。
- 新context_method_irでは外部の可変scalar参照を持つclassのscalar fieldsを参照で渡し、const methodの参照権限も保持する。元FieldDeclからsynthetic parameterとbodyを再構成し、型・参照mode・権限を再監査する。UFの外部引数は値渡しなので既存modelとの一致を保つ。
- test_context_method_ir.pyでfield自身を外部refへ渡すLean/native ASan/UBSan例とconst getterを確認した。readonly最適化を旧backend等へ展開する際も、外部aliasによる変更を扱う条件が必要。新receiverの検査を旧caller全体の証明と混同しない。


## 2026-10-24: projectのslot長と単独moduleの依存

- `project caller` のslotsは元slotsのmapなので、長さが同じでもdefinitional equalityではない。`change`では元slots長へ変換できず、先に `simp only [project,List.length_map]` を使ってからlookup等式を適用する。大きなmaterialize全体を同時に展開しない。
- 草案checkerの上位importがCppMoveContextを読み込んでいると、草案自身のimport不足が隠れる。正本化したmoduleを単独buildし、必要な直接依存を明記する。今回の再現はUfObjectConstructionExport.leanのCppMoveContext依存。
- constructor終了時のcaller prefixは実callee memoryから取得する。参照引数への書込みがある場合、元callerの古い値で置き換えない。test_cpp_constructor_layout.pyはfield初期化時7/constructor body後の元変数9をLeanと元C++ UBSanで照合する。


## 2026-11-01: 構築段階のフィールド局所変数と参照別名

- 構築中のthis呼出しには、既に確保・初期化したフィールド局所変数を宣言順に渡す。通常メソッドの疑似receiver引数をそのまま参照したり、メソッドを標準vector操作として扱ったりしない。構築用の共通inlinerへ同じClang宣言IDのヘルパーを渡し、再帰・評価順の拒否規則を共用する。
- フィールドへの直接代入がなくても、可変scalar参照引数がフィールド自身を指すと値は変わる。構築時のinspect(count)が参照を9にしてからcountを返す例で、旧値5の捕捉が不正な結果を生成することを回帰検査で確認した。_read_only_fieldsもContext経路と同じく、可変scalar参照を持つクラスのscalarフィールドを参照で保持する。修正後はcount/observedがモデル・Cppとも9になる。
- Beatsの15本のvector確保prefixと、既存の検証対象本体へのスロット循環置換が構文上一致することを確認したが、これは評価器の置換に関する意味保存ではない。確保からBFreshS/CVecsを構成すること、実caller/export/寿命と確保自体の費用を含めることは別の証明として続ける。

## 2026-11-01: 構築本体の追加領域上界の一括計算

- WideCtorCmdのNb≤100を一括のdecideで計算すると標準の再帰深度に達した。資源上限を増やさず、Nb/grC/grS/exS/vwpと式の構文ごとの式をsimpで分解すると、同じ上界100の証明が通った。BeatsWideCtorExecのwide_ctor_nbを `by decide` に置き換えた草案で再現した（実15909終了1）。式全体の再帰計算が失敗した場合、構文に沿う小さな計算・合成へ分け、主張や資源上限を緩めない。

## 2026-11-03: CIコンテナ内のGit所有者確認

- run41594742022は公開検証開始前のgit ls-filesでdubious ownershipとなった。checkout action内の一時HOMEでの設定だけに依存せず、検証runと同じ環境でGITHUB_WORKSPACEだけをsafe.directoryへ登録する。ワイルドカードで全リポジトリを信頼しない。
- 一時リポジトリとGIT_TEST_ASSUME_DIFFERENT_OWNERを使い、登録前の拒否、POSIX shでの登録後の成功、別リポジトリの拒否を確認した。

## 2026-11-03: ビルド済みLeanモジュールへの暗黙依存

- CI41595322068はC++59部品/AST照合後、MatPow独立検査とmulti finishテストのimportでunknown module prefix Proofsとなった。check_public.pyが共有テスト後にlake buildを行っていたため、既存oleanのあるローカルだけ通過した。
- 全件gateは最初にLeanモジュールをbuildし、テスト後に証明監査を行う。ビルド失敗でテスト/監査へ進まないことと、build→import利用テスト→監査の順序をtest_public_support.pyで回帰確認する。部分cpp/bridgeモードの範囲は維持する。

## 2026-11-03: 実状態を補題適用ごとに展開しない

- cold CIでBeatsExecAA/UM/UNのコンパイルが非常に遅くなった。小さいomegaだけのcontext削減や評価器pexecM/vdenMの局所irreducibleでは解消せず、seq_writeへ具体的なPSとvector写像を渡す型合わせに時間を要した。
- 主定理の範囲だけでgS/VVBをlocal irreducibleとし、既存の読取り/更新補題で扱う。元の宣言名・型・計算定義を照合し、固定nanodaの3752宣言を基礎3公理・標準stackで通した。定理の条件や上界、プログラムを小さくして回避しない。cold leaf再コンパイルを時間内で行う回帰をtest_beats_capacities.pyへ加えた。
- 定理のproof ExprをreprStrすると共有DAGが重複展開され、診断出力だけが巨大になり得る。型/計算定義は正確に比較し、証明本体は共有を保つexportと独立kernelで検証する。構造hashは参考値であり安全性の判定を代替しない。

## 2026-11-04: 独立buildとテスト準備の重複

- 通常projectを全件buildしてから独立scratchを全件buildすると、cold CIでコンパイル時間を二重に消費する。監査済みsourceだけから固定設定でscratchを先にbuildし、テスト用importsをscratchから通常環境へ一方向に配布する。通常projectのolean/traceを監査側へ取り込まない。テスト後の仕様/公理/両kernel監査は引き続き必須とする。
- ASTのroot抽出では、quoteごとのPython loopより、正規表現内で完全な文字列と通常文字をまとめて走査してbraceだけPythonへ渡す形を検討する。任意chunk境界のescapeと生bytesを回帰で確認し、同じClang processの全rootを比較する。文字列単位のregexに変えるだけでは遅くなる場合もある。

## 2026-11-04: 最終監査にも全体deadlineを渡す

- buildと共有テストだけにremainingを渡しても、最後のproof-securityがsubprocess.runへtimeoutなしで渡されると全体制限が効かない。cache判定の前後にも予算を確認し、実監査にはその時点の残時間を使う。監査のtimeoutでは親だけでなく同じ専用process groupのcompiler/exporter/kernelも止める。期限切れ時の未起動、cache走査後の再確認、実子プロセスの停止を回帰で確認する。


## 2026-11-08: 異なるfamilyの同名recordを短名で同一視しない

- `A<T>::Data` と `B<T>::Data` はfield名・型・構成子署名が一致しても別の宣言である。Bの構成子だけ100を加える例では、C++結果107に対してAの構成子による7を誤生成できた。
- recordを返すmemberでは、元宣言へのmember pointerの型を完全修飾receiver/result/record引数で構成した型とcompilerで照合する。const/noexceptを保持し、probe内の型名や検査keywordのmacro置換も拒否する。返却型と引数型の両方に取り違えの回帰を置く。
- source/TU所有とfield宣言の監査だけでは返却型や引数型の宣言identityを保証できない。有限モデルの成功も型identityの証明の代わりにはならない。


## 2026-11-08: LCAの開始段は表の実在行で制限する

- `bit_width(depth)` は最大行番号ではない。親[0,0,1,1]のdepth=2では2となる一方、doubling(...,n-1=3)は2行しか持たない。実表のsize()-1から降下すればこの範囲外を避けられる。
- 高位段を増やした同等性は、根の親が根・全行が正しい反復表・深さを覆う段数の前提で証明する。有限なrandom比較だけで数学証明の代わりにしない。
- 原本のC++20/llの実型を保ったテストを使う。元class全体のC++自動生成/寿命やsingletonの構築境界は、降下の数学仕様と区別して記録する。


## 2026-11-08: 公開ディレクトリの階層化

- 公開headerとTOMLを分野別に隣接配置し、sourceはlibraryルートからの相対パスとする。登録と検査cacheはrglobでmetadata全件を拾い、部品名は階層を越えて一意に保つ。
- include/test/doc/台帳と配布ZIPを同時に更新する。配置前後のheader hashで本文保持を確認し、相対includeの変更は別に検査する。
- 全件gateで既存変換器と古いモデルのずれを見つけたら、移動前配置からの生成とも比較して原因を分ける。検査を弱めず、全件成功とは報告しない。
- 完全なパス文字列の置換だけでは、`DIRECTORY / 'doubling.hpp'`のような分割されたパスを見落とす。パスの組立も調べ、変異テスト用の一時配置には相対include先の階層を再現する。nested oracle全3区分・native ASan/UBSan・変異テストで新配置を確認した。
