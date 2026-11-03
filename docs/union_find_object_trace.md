# 元ObjectRefに対する任意長UFメソッド列

`Proofs/UfObjectTrace.lean` は[通常UF状態](union_find_object_state.md)を使い、同じ元ObjectRefに全5メソッドを任意の有限回数呼び出す。初期状態の各添字の範囲条件から、実際の呼び出し列の正常終了・結果状態・各返却値の意味を導く。完成済みの中間状態や各callの成功は前提にしない。

## 実行と前提

`Operation` はroot/same/size/unite/groupsと自然数の添字を持つ。`Operation.Valid` は添字が実vector長未満であることを表す。元StateのValidが保証する長さ上限と合わせ、添字literalがi32に収まることを導く。既存の任意pure引数式を扱うstep定理は引き続き利用でき、この列では値が決まったliteralを使う。

`expand` はObjectRefのvector slotと宣言順のcounter/size scalar slotsから実引数を作る。scalar slotsが2個でない場合は拒否する。`invoke` は元の生成NProgramと共通のcompact callFuelを使い、引数展開失敗やエンジンの失敗もOutcomeとして保持する。`run` はfuel付きの列を左から実行し、実際のContextを次のcallへ渡す。

`execute` は各Operationが初期vector長に対してValidであるとき、全列が正常終了するfuel列・結果列・最終Stateを構成する。各stepでsize fieldを保持し、結果Stateのsize=vector長から次の添字条件を導く。初期Stateのデータを中間stateへ流用しない。空列も扱い、返却列の長さは操作列の長さに一致する。

## 意味と仕事量の履歴

`Step` は実callの正常終了、size保持、実結果payloadとcounter値についての`Effect`、実prepareArgumentsと仕事量の上界を持つ。`History` は各時点のStateとStepを順番に保持する。`execute` の結果にはこの履歴も含む。

- root: 返却rootと元payloadから実結果payloadへのCompressed。
- same: 2回のCompressed、返却値と元payload上のConnectedの対応。
- size: 返却値が元payload上の成分要素数であることとCompressed。
- unite: 2回のCompressed、実uniteVec、返却root、結合前のConnected、countAfterによる実counter更新。
- groups: 元counter値の返却とpayload/counterの保持。

`bodyWork` は元step定理の上界をその時点のrankに適用する。rootは91*rank(a)+81、sameは91*rank(a)+91*rank(b)+181、sizeは91*rank(a)+101、uniteは91*rank(a)+91*rank(b)+343、groupsは3である。Stepは実prepared Contextを持ち、work(out) ≤ work(prepared)+bodyWorkを保証する。[準備費用を含む列全体の仕事量](union_find_object_trace_work.md)へ接続した。列全体の償却計算量の証明にはrank履歴の追加合成が必要である。既存stepの全peak/memory/payload postは元の定理に残る。

## 検査と残件

`tests/test_uf_object_trace.py` は全5種類を含む列、任意の自然数回のroot、2成分からのuniteを含む列、空列、不正ObjectRef形を確認する。groups/size履歴から返却値の意味を取り出す一般証明も型検査する。元C++と既存native照合は維持する。

元caller/constructorからの初期State構成、返却値に依存して選択する操作列、caller ASTの評価順/副作用、copy/move/return/destructorと混在する寿命列、割当/resize/nested/異種vector、列全体のpeak上界・償却、公開UF相違と他旧ライブラリのverifyは残る。この定理だけで元UFの公開条件が揃ったとは扱わない。
