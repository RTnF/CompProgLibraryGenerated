# 非resize scalar callのContext戻し込み

`Proofs/CppMoveCallRestore.lean` は既存の `NProgram.callFuel` の完了結果を[move Context](move_context.md)へ戻す。実vector更新、scalar参照更新、scalar返却値を一緒に保持する。[戻し込みの一般射影証明](move_restore.md)を使い、再射影した全NStateが実callの終状態に一致する。

## 実行器

`eligible` はscalar resultと `CppNoResizeScope.Allowed` のbodyだけを許可する。`restoreCallFuel` は適格でないprogramをfaultにし、適格なcallでは元callFuelのfault/exhaustedをそのまま返す。成功時には実afterをrestoreContextで戻し、元のRetを返す。最終shape一致だけを途中resize不存在の証拠には使わない。

元heapのOwnsAllとscope条件は定理の前提である。source callerのASTから任意のprogramを生成してこの実行器へ渡す接続は未完了。

## 正常終了との接続

`retire_valid` は実retireScope成功時のguardからwellFormedを導く。`finish_valid` と `call_valid` はscalar callの実prepare/body/finishを分解し、最終wellFormedを導く。

`call_restore_ready` はscalar result、Allowed、元contexts/OwnsAllと実call成功から戻し込み成功と全射影一致を導く。最終wellFormed、各binding、slot、scope、memory長、baselineの一致を別の後条件として仮定しない。metadataは既存call_headersから得る。

`call_restore_terminates` は元callのTerminatesを高levelへの戻し込みと接続する。任意bodyの終了をこの定理だけで証明するものではなく、アルゴリズムごとの正常条件からの終了証明を使用する。

`restoreCallFuel_ready` は実高level実行器の成功を、`restoreCallFuel_sound` は高level実行器の成功から実low-level callと返却値の完全一致を証明する。`call_restore_result` も元の返却値をそのまま保存する。

## 旧UFへの適用

`tests/test_cpp_move_call_restore.py` は旧APIを保つ候補 `experiments/verification/data_structure/union_find.hpp` の生成済みmethodモデルを用いる。class move代入後にsameを呼び、経路圧縮で変わったallocationとmove前の要素grant、旧世代、scalarを戻す。代入先の旧allocationへの参照は失効したままとする。

有限callだけでなく、元の正常条件からのUfFieldsSame.same_callを適用して終了を得てからcall_restore_terminatesへ接続する。root/size/unite/num_groupsのmove後callも照合する。moved-fromの_n/countは保持され、空vectorへの不正なrootはfaultになる。scalarを0へ書き換えてUFの不変条件を満たしたことにはしない。

一般callの参照更新/返却、fuel不足、空move元へのwrite、対象外のresize/unitを検査する。固定GCC13.3/ASan/UBSanで元候補classのmove、5method、moved-fromのgetter、再代入、self move後のgetterと再初期化を有限照合する。

## 資源と残件

この実行器は既存callFuelの実counterを戻す。既存NestedCall.prepareは射影frame.bindingsの個数を予約量に含むため、immutable grant履歴をghostとするContextの物理stack上界へは未接続である。既存counterとの一致を新たな物理資源証明とは扱わない。

FieldDecl→ObjectRef、実caller AST/評価順、Contextのcall準備と物理資源、move構築/返却/destructorの一般生成、allocation/resize/nested/異種vector、任意混在寿命列は残る。公開UFの既存違反と全旧ライブラリの検証も未完了。

[Contextで準備するcall経路](move_prepared_call.md)を追加した。ghost grant履歴を予約せず、正常bodyの結果からfinish成功と戻し込みを構成する。各methodのbody証明・全資源と元caller生成への一般接続は継続する。
