# move を含む caller の状態投影と引数準備

`Proofs/CppMoveContext.lean` は、[型付き Frame](move_frame.md)と[固定要素書込み](move_write.md)の上に scalar 状態・宣言 slot・scope を持つ Context を置く。同じ整数型の flat vector 群を対象とする接続レイヤーである。全 C++ caller、所有 vector の破棄・返却、class call を含む引数評価まで検証済みとは扱わない。

## scalar と object view

Context の scalar memory/binding は既存 `CppState.State` を使う。`project` は scalar のアドレスと slot を変えず、vector の slot を「要素 grant 履歴長 + object view slot」へ投影する。work、scalarCell、charge の一般対応と、現在の header/allocation を Frame が解決する対応がある。

vector 参照引数の `Borrow` は header ID と要求権限を保存する。引数評価時点の allocation を保存しない。後で `installBorrow` すると同じオブジェクトの現在の領域を解決する。例えば移動前に保存した元オブジェクトの参照は、移動後には空の元オブジェクトを指す。旧要素参照の grant は独立に allocation を指し続ける。readonly view から mutable な借用を取得できない。

`argument_resolve_runs` / `installBorrow_ready` は、この view 設置と投影を既存 `CppNestedCall.resolve` の実成功へ接続する。

## 引数評価と準備

`evalExpression` は実 `NExpr.eval` を実行し、scalar 状態と peak を戻す。既存の式評価の一般定理から、一時 binding を release した実 Frame が元 Frame と一致することを導く。`evalExpression_correspondence` は成功・失敗を含む Option 結果と投影後の状態を対応付ける。

`resolveArgument` / `resolveArguments` は現在の Context を順に受け渡し、scalar 値、scalar アドレス、vector Borrow を保存する。scalar 値では resultType を検査し、scalar 参照では型・権限を確認する。ここで使う NExpr は算術、read、size 等の既存 IR であり、class call/move/assignment を含む C++ 引数式全体の代用ではない。nested/異種 vector 引数の対応も残る。

`prepareSaved` は既評価引数から callee を作る。caller の既存 memory を共有参照用に保持し、実際の caller 宣言 slot 数だけ保守的な宣言・参照領域を予約する。callee の scalar bindings/slots は空から始める。ghost な grant/view 履歴数を予約量に含めない。scalar 値・参照は既存の型検査付き `bindArgument` を使い、vector 参照パラメータは1単位を予約する。

`SavedReady` は値の妥当性、実 scalar cell/type、実 header と権限を要求する。`prepareSaved_ready` はすべての引数が caller でこの条件を満たす場合に、任意リストの実成功、元 heap 不変、callee slot 数が引数数と等しいことを導く。前の bind が元 memory prefix と heap を保持するため、後続引数の条件も保持する。実引数評価から SavedReady と準備成功への一般接続は[引数評価の補題](move_argument_facts.md)に記載する。C++ 式全体や callee body を含む全 call の対応は残る。

## 準備の資源

引数数を m、各引数の memory cell 増分を C、scalar binding 増分を B とする。scalar 値・scalar 参照・vector 参照の (C,B) はそれぞれ (1,1)、(0,1)、(1,0) である。

実 `prepareSaved` 成功について、memory 長は caller memory 長 + caller slot 数 + ΣC、scalar binding 長は ΣB、総 work は caller work + 1 + m、baseline は不変となる。これは準備処理の式であり、先行する引数式評価の work は caller 状態へ既に反映されている。

`prepareSaved_peak` は、準備後の scalar live 領域 L を用いて、peak ≤ max callerPeak (max callerScalarPeak L + heapPeak) を示す。baseline が caller memory 長以下なら、L ≤ caller memory 長 − baseline + caller slot 数 + 2m であり、`prepareSaved_peak_linear` がこれを代入した上界を与える。0引数でも予約直後に peak を観測する。これらは抽象的な領域単位であり ABI bytes や実測値ではない。

## 借用呼出しの終了と残る範囲

`finishBorrowed` は callee scope が caller+1、旧 view/grant prefix の同一性、caller scalar prefix の型と長さ、callee scope に所有 header が残らないことを確認する。その上で caller の slot/binding/scope を復元し、callee による共有 scalar cell の更新を戻す。metadata、alias prefix、cell と scalarCell の一般保持定理がある。

これは所有 vector を callee scope に残さない呼出しの終了 helper である。局所 vector の破棄を省略して終了することはせず、所有 header が残れば拒否する。一般 scope 破棄、返却 vector の移動、通常操作の戻し込み、全 call の意味対応、元クラスの scalar 宣言順と AST overload、allocation/resize/異種 vector/任意混在寿命列、公開 UF の相違解消は引き続き必要である。

`tests/test_cpp_move_context.py` は一般定理適用と有限例で、move をまたぐ Borrow、scalar 値/参照の区別、read/size/算術式、型・権限・添字拒否、準備と scalar 更新の復元、ghost 履歴・baseline・過去 peak を検査する。

[scope 破棄と finishScope](move_destroy.md) に、flat vector の local 所有領域を片付けて finishBorrowed へ渡すモデルを登録した。元 destructor AST、返却 move、callee body 全体との生成接続は引き続き必要である。

[非 resize 結果の戻し込み](move_restore.md)は実 payload/scalar/counter と全 Frame/Context 射影を接続する。実 NProgram.callFuel/finish から必要条件を導く一般 call adapter は引き続き必要である。
