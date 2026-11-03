# 非 resize 実行結果の戻し込み

`Proofs/CppMoveRestore.lean` は、[move Context](move_context.md) を既存 NState/Frame へ射影して実行した後、実際に変わった vector payload と scalar 状態を Context へ戻す。header・allocation の同一性、immutable grant、寿命世代を維持し、work/peak は実行結果を採用する。scalar だけを戻して vector 更新を捨てる処理を避けるための基盤である。

適用条件は、対象の実行列が既存 `CppNoResizeScope.Allowed` 等で扱える非 resize 操作であること。最終形状の一致は終状態の整合性を検査するもので、途中の resize・破棄・再構築がなかったことの証拠は実行列側で別に示す。実 `NProgram.callFuel` の入力条件・finish と source caller の生成接続は継続する。

## 有限の形状検査と payload

`Shape` は forest、rootWritable、有限 owner 列の buffer signature、baseline を含む。signature は owner/capacity/limit/epoch/要素数であり、payload・work・過去 peak は含めない。`shape_of_sameHeaders` / `sameHeaders_of_shape` は、この有限検査と既存 SameHeaders＋rootWritable 保持の両方向を証明する。

`restoreEntry` は生きた allocation の実 after buffer を取得して flat integer へ復号する。signature と owner、型妥当性を検査し、旧 generation 関数を保持する。nested child を読み飛ばさず拒否する。`restoreEntries` は ID 表を同じ長さ・生存状態で戻し、tombstone と範囲外 ID は復活させない。

`restore` は元の header/view/grant を保ち、実 after の allocation payload/work/peak/base を採用する。表の走査と復号はモデルの ghost 処理であり、C++ の実行仕事量や追加領域へ加算しない。

## 正常条件からの成功

`decode_ready` / `unbox_ready` は型付き integer payload から実復号の成功を導く。`ready_of_sameHeaders` と `restore_of_sameHeaders` は元 OwnsAll、実 after wellFormed、SameHeaders と rootWritable の一致から全 allocation の戻し込み成功を導く。完成済み restore の成功を入力条件には置かない。

`command_restore_ready` は実 `runFuel` と既存 NoResizeRun.run_headers を接続する。元 context の scope 条件・OwnsAll と実 after の wellFormedness が必要であり、それらを任意の source body について自動証明したという主張はしない。

## 保持と全 Frame 一致

`restore_allocation` は全旧 live allocation を実 after payload へ対応させ、型・signature・旧 generation を証明する。`restore_dead` は旧 tombstone と範囲外 ID の非復活を示す。Unique/OwnsAll/AllocationsValid/HeadersLive/GrantBounds を保持し、容量総和・liveSpace・baseline も保つ。

`restore_no_resurrection` は元 AllocationsValid の下で、既に読めなかった要素 grant が復活しないことを証明する。型不正だった payload を外部の状態で修復する場合までこの定理を広げない。

allocation 領域は各 payload の復号と対応から、後続の empty-header placeholder は signature と空 payload の一意性から lookup を一致させる。表長と全 lookup から表全体の等価性を導き、forest、rootWritable、binding、counter を合わせる。

`restore_state` は再射影した Frame.state = 実 after.state を示す。`restore_frame` は after の binding が元射影と同じという条件も加えて Frame 全体の一致を示す。`restore_generations` は全 owner/index の世代関数を保持する。有限例の一致を一般定理の代わりにはしない。

## Context

`restoreContext` は完了後の非 resize call を対象に、元 slot/scope/frame binding/scalar binding/memory 長/baseline の一致を検査する。実 scalar memory と peak を戻し、scalar と vector を合わせた全 work は実 after.work に一致する。

`restoreContext_ready` は正常な形状・型・所有条件と上の metadata から実成功を導く。`restoreContext_project` は元 OwnsAll の下で project(out) = 実 after NState を証明する。local 宣言を含む callee body は call finish で metadata を復元してから接続する。返却 scalar 値も含む実 call adapter と元 caller AST への生成は未完了である。

## 検査と残件

`tests/test_cpp_move_restore.py` は move 後の Context で実 runFuel による 2 要素書込みと scalar 参照更新を実行し、元要素 grant・世代・tombstone、header/grant、全 work/peak と全 Frame/Context 射影を検査する。allocation のない空 vector の size、stale generation、resize・rootWritable/scope/slot/baseline 不一致・nested payload の拒否も確認する。一般終了・保持・非復活・全射影定理を適用し、固定 GCC 13.3 / ASan / UBSan の対応する move 後書込みも有限照合する。

実 callFuel/finish からの metadata と型・形状の一般導出、FieldDecl→caller ObjectRef と実 move 式、move 構築/返却/destructor、allocation/resize/nested/異種 vector と任意混在寿命列、公開 UF の相違解消と他旧ライブラリの検証は残る。

[scalar call完了との接続](move_call_restore.md)は実finishから型・metadataを導き、元の返却値と更新状態を一緒に戻す。元caller ASTと物理call準備領域の一般対応は継続する。
