# 作業上の教訓

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
