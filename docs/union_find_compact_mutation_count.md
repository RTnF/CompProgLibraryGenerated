# 旧UF unite・num_groupsのContext call証明

`UfCompactUniteBody/Call` と `UfCompactCounterBody/Call` は、元candidateの生成済みbodyを[callee binding整理を使うcall](move_call_bindings.md)へ接続する。[root](union_find_compact_root.md)・[same/size](union_find_compact_queries.md)と同じContext準備・実body・finish・戻し込みを使用する。

## unite

正常条件は元配列とgroups/rankのValid、counterの型付きcell、範囲内のa/b、元field値に対応するQS、実vectorのFW、権限・baseline・scopeとcaller prefix、実prepare/compactである。body_correct→soundWから2回のCompressed、uniteVecと返却uniteX、新rankでのValidとcountAfter、元Connectedとの根の一致判定、実停止を導く。

unite_callは実call停止、最終Contextのvector payloadと統合結果の一致、最終scalar memoryとupdatedMemoryの一致を証明する。既に同じ成分ならcounterを保持し、異なればcounterだけgroups−1にする。updated_types/updated_lengthは元counterの型から更新後memoryの型prefixと長さを導く。最終fits/types・finish/restore成功を入力仮定にはしない。

body workは初期work＋91×rank(a)＋91×rank(b)＋342以下、call後は準備後work＋91×rank(a)＋91×rank(b)＋343以下である。body scalar上界はmax(max初期scalarPeak初期peak)(prefix長＋100−scalarBaseline)。heap上界はrootと共通のbaselineを差し引く式であり、合成peakを実run_growsとfinish countersへ接続する。

## num_groups

counter_body/counter_callは任意の型妥当なi32 groupsとcounter cell、QS/FW、prefix・scope等の条件から、元groupsの返却・実停止、scalar memoryとvector payloadの保持を導く。Forest/Weights/Validやn=vector長を要求しないため、getter自体はmoved-fromや空vectorにも適用できる。元クラスのValidがあれば、既存のValid.countから返却値が根の個数に等しいことを導ける。

body workは初期work＋2以下、call後は準備後work＋3以下。scalar上界はmax(max初期scalarPeak初期peak)(prefix長＋6−scalarBaseline)であり、heap/合成peakも既存のsharp上界へ接続する。引数準備のwork/peakは既存prepareArguments_resourcesを使用する。

moved-fromの_n/countを0へ変更して正常条件を満たしたことにはしない。root等の要素アクセスmethodには、それぞれの配列・範囲・クラス不変条件が必要である。

## 検査と残件

`test_uf_compact_mutation_count.py` はclass move後の一般unite_callを適用し、連結例でcounter保持、別成分[-2,0,-2,2]のunite(3,1)で返却2・payload[2,0,-4,2]・counter2→1を確認する。旧要素grantの読取りと旧代入先参照の失効維持、他scalarの保持も照合する。

counter_callの一般定理、Validからの根の個数の解釈、通常・moved-from・空vector、INT_MIN/INT_MAXの返却と全scalar保持、燃料0をkernel確認する。元candidateのC++動作は既存のGCC13.3/ASan/UBSan検査で照合する。

これで候補の5methodをこのcall経路で個別に扱えるが、元caller ASTからFieldDecl/ObjectRef/prepare/QS/FWを自動生成する接続、償却証明・任意混在列、構築/返却/destructor、割当/resize/nested/異種vector、公開UFの既存相違解消と他旧ライブラリは残る。全experimentsのverify完了とはしない。

[FieldDeclからのreceiver生成](context_method_receiver.md)は元5methodのFieldDecl/型/参照modeを監査し、ObjectRefからこのContext callへ引数を生成する。元caller ASTと正常クラス状態からの一般構成は継続する。
