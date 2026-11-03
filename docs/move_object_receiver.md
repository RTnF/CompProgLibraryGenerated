# ObjectRefの元field配置と生成methodの実引数評価

`Proofs/CppMoveObjectReceiver.lean` は、元callerのslot・binding・memoryとObjectRefのfield順から、[実receiver引数評価](move_receiver_resolve.md)の条件を構成する。`verifier/context_method_ir.py` は同一TUで監査したschemaに基づき、この証明への転送定理を生成する。元C++のAPIや入力範囲は変更しない。

## 元配置からのfield読取り

`Field` はcaller中のslot/index/address/writable/valueと、scalarSlot・binding・memory・型妥当性の条件を持つ。`Field.cell` はこれらから実scalarCell読取り成功を導く。完成済みscalarCellをFieldの前提に入れない。

`Receiver` は1vectorと2scalarという対象profileのObjectRefを表す。scalarSlotsがcounter/sizeの宣言順slotであること、元vector slot/view/headerの対応、counterとvector viewの書込み権限を持つ。`Receiver.capture` と `Receiver.resolve` はこれら元配置条件と外部pure scalar式のReadyから、実vector captureと実receiver引数評価を構成する。

このReceiverは任意クラスのconstructor不変条件やUFのStrongを置き換えない。元callerからObjectRefとfield配置を導く一般接続、source lifetimeに基づくfield同一性は別途必要である。move後の空vectorでもsize/counterの元値はそのまま扱う。

## 同一TU schemaからの定理生成

全対象methodに `arguments_of_fields` を生成する。ObjectRef.scalarSlotsが監査済み宣言順のslot列であることと外部引数数から、実adapter成功と展開済み引数列を導く。scalar参照/値渡し、元型、vector権限は既存の同一TU監査結果に従う。mixed型や可変参照aliasに対応した既存の引数区分を変えない。

schemaが次の構造に一致する場合は `resolve_of_receiver` も生成する。

- writable vector 1個。
- vector要素と同型のwritable scalar参照field 1個と、同型のscalar値field 1個。
- 同型のscalar値外部引数列。

クラス名やfield名で選ばず、schemaの型・権限・参照modeを検査する。外部mutable参照等によりfieldがすべて参照化されたprofileには、この専用定理を生成しない。対象外でも既存のmethod生成・実行と一般のarguments_of_fieldsは維持する。

生成された `resolve_of_receiver` は任意caller/ObjectRef/Receiverと型妥当なpure式意味条件・arityから、実adapter成功と実resolve成功を導く。完成済み展開引数やresolveを入力にしない。保存引数のheader/address/size値も元Receiverへ対応する。既存のcall_of_argumentsは生成wrapperを同じprogram/展開引数の実Context callへ転送する。

[元ObjectRefからのUF正常root/getter call](union_find_object_call.md)を接続した。元配置とheap/式/UF条件から実prepare/compact/QS/FWと正常callを構成し、既存work/peak上界を保つ。

## 検査と残件

`tests/test_cpp_move_object_receiver.py` は元move代入の実返却ObjectRefからReceiverを構成し、生成された元UF全5methodの定理へ適用する。元sourceの空vectorと_n=4/count1でもgetter形の実resolveを構成する。別名クラスからの定理生成・Lean型検査、vector権限/field型/参照mode/外部参照の変異によるprofile不一致も確認する。

既存 `test_context_method_ir.py` のmixed型・mutable-ref alias/const getter・不正入力/source変更拒否とnative ASan/UBSan照合を維持する。元caller ASTのcallee/receiver/引数評価順と副作用、constructor/copy/move/return/destructorからの配置条件構成、正常callと償却・任意混在寿命列への一般接続、割当/resize/nested/異種vector、公開UF相違と他旧ライブラリは残る。
