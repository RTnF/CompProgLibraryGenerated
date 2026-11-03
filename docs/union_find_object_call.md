# 元ObjectRefからのUF正常call

`Proofs/UfObjectCall.lean` は、[元ObjectRefの正常field配置](move_object_receiver.md)とheap・式・UFの条件から、呼び出し準備とメソッド本体の正常終了を一般に構成する。対象は元candidateのrootとnum_groupsであり、元C++のAPI・型・入力範囲を変更しない。

## 共通の実呼び出し準備

`arguments` はreceiverのvector/counter/size fieldとpure外部式列から元methodの引数列を作る。`prepare` は元ObjectRefのReceiver、pure式の型/denote条件、監査済みparameter列との一致、元heapのreadable/Unique/OwnsAll/AllocationsValid、limitとscope条件から実resolve→prepare→compact→QS/FWを構成する。

完成済みresolve/prepare/compactやQS/FWを入力にしない。counterの元cell/型妥当性とsize fieldの読取りはReceiverから導く。返すQSは元fieldsに対応する正確なmemory/bindings/slotsであり、callee bufferと元currentBufferの一致も返す。

## rootとgetter

`root_call` は元currentBufferの内容に対するForestとrank、型内の長さ、0以上で長さ内の添字、size field=vector長、pure添字式の意味上の評価結果を要求する。共通prepareを構成した後、既存の元root正常call証明を適用し、返却root、Compressed、更新Forest、実停止を導く。

結果には実prepared/initial stateとFW、および既存のwork≤prepared work+91×rank(a)+81、caller scalar memory保持、baselineを差し引くscalar/heap/合成peak上界、更新bufferのpayloadをすべて残す。存在するが任意に大きい予算を選ぶ形に置き換えない。式評価と準備の費用は実prepared stateに記録され、元callerからの全費用・償却計算量への一般接続は残る。

`counter_call` は同じ正常ObjectRef/heap条件から実getterの停止、元counter値返却、全scalar memory/payload保持と既存work/peak上界を導く。Forestやsize field=vector長を要求しない。moved-fromの空vectorでも元size/counterを維持してgetterを実行する。

scalar baselineが実準備prefix内であることと、元projected scopeがcaller scope以下であることは元状態の正常条件として要求する。全caller/constructorからこれらが保たれる一般証明とは区別する。

[same/size/uniteのObjectRef正常call](union_find_object_methods.md)も同じ共通prepareへ接続した。全5methodの既存意味・資源postを保持する。

## 生成wrapperへの接続と残件

`tests/test_uf_object_call.py` は元move代入の実返却ObjectRefと元sourceのReceiverへ一般root/getter定理を適用する。再生成したsource methodのarguments_of_fieldsとcall_of_argumentsを使い、算術2+1を添字に取るroot wrapperの正常終了/圧縮と、moved-from getter wrapperの元count1返却まで接続する。成功済み本体や完成済み実引数評価をテストの入力にしない。元C++は変更せず、既存native照合を維持する。

元caller ASTからのreceiver/正常配置と評価順・副作用の一般構成、償却証明・任意混在寿命列、constructor/copy/move/return/destructor、割当/resize/nested/異種vector、公開UF相違と他旧ライブラリは未完了である。
