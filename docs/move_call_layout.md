# 呼び出し後の配置・heap条件と同じObjectRefの再利用

`Proofs/CppMoveCallLayout.lean` は、成功した非resizeのContext callから、元callerの配置とheap条件を引き継ぐ。更新された実memoryのfield値から同じObjectRefのReceiverを再構成し、[元ObjectRef正常call](union_find_object_methods.md)を次の状態へ接続するための部品である。

## 成功callの効果

`call_restored` / `call_objects` は実 `CppMoveCallBindings.callFuel` の成功から、実行器が行った `restoreContext` / object restoreを取り出す。fault・fuel不足・break・finish/restore失敗を成功扱いしない。

`restore_layout` / `call_layout` は次の元配置を保持する。

- caller slots、scope、scalar bindings、scalar baseline、memory長。
- vector header、immutable grant、object viewの各表。
- allocation表長とheap baseline。

scalarの値やvector payload、work/peakが不変とは主張しない。更新された値と費用は実結果から得る。

`call_allocationsValid` は実restoreが確認した各allocationの型妥当性を取り出す。`call_unique` / `call_ownsAll` は元の所有条件を引き継ぐ。`restore_readable` / `call_readable` は実allocationのowner・limit・型妥当性とsignature保持から元headerのreadableを保つ。`call_contexts` は投影forestと元scopeの保持から元scope条件を保つ。

`Layout.prefix_length` / `baseline_fits` により、結果stateでも実準備prefixの長さとscalar baselineの条件を使える。これらは完了callの効果定理であり、成功runを入力に取る。正常終了を導く定理の前提へ成功runを戻すものではなく、既存の正常終了定理が構成した実runへ適用する。

## 結果fieldの再構成

`Field.update` / `Receiver.update` は元配置とLayout、結果memoryに実在するcounter/size cellとその型妥当性から、結果stateにおける同じObjectRefのReceiverを構成する。Contextを書き換える処理ではない。vector view/headerは元の表と対応を引き継ぐ。

counter/size両方の実cellを要求するため、field aliasによる値の変化や、任意クラスのconstructor/Strongを無条件に仮定しない。型が妥当であることも、結果の値そのものに対して要求する。

[結果currentBufferとpayloadの対応](move_call_payload.md)を追加し、uniteのUF Validを実結果dataへ引き継いで次rootの正常終了へ接続した。

## 検査と残件

`tests/test_cpp_move_call_layout.py` は元ObjectRefの一般unite定理から、別成分の実counter2→1・他scalar不変を導く。実成功へcall_layoutを適用し、更新後memoryから同じObjectRefのReceiverを構成して次getterの実引数評価へ接続する。

さらに所有/型/readable/scope/baselineを結果stateへ引き継ぎ、次の一般counter_callを適用する。unite→getterの両方の正常終了、getter返却1とmemory保持を導く。成功済みgetter本体や固定fuel計算を前提にしない。元C++は変更せず、既存native照合を維持する。

結果vector payload/UF Validを全methodの次の状態へ対応させる一般不変条件、元caller/constructorからのObjectRef正常配置、償却/任意混在寿命列、caller ASTと評価順/副作用、copy/move/return/destructor、割当/resize/nested/異種vector、公開UF相違と他旧ライブラリは未完了である。
