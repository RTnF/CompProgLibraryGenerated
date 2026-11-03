# 元UF receiverからのcallee変数配置

`Proofs/CppMoveReceiverLayout.lean` は、借用vector、scalar field参照、同じ型の値引数列というreceiver profileから、実際のContext呼び出し準備とcallee binding整理を構成する。元UFの `_ps`、`_num_groups`、`_n` と外部値引数がこの形になる。元C++のAPIや型を変更するものではない。

## 型付き値とfield参照

`bind_values` は任意長の型妥当な値列について `bindSavedAll` の成功を導く。memoryに型付きcellを追加し、bindingのaddressは追加前のmemory長から、slotのscalar indexは追加前のbinding長から連続して配置する。元objects、scope、scalar baselineを保つ。memory長とbinding長が異なる状態でも同じ式が成り立つ。

`prepare_receiver` は元headerの存在と参照権限、元memory内の型妥当なcounter cell、値列の型妥当性から `prepareSaved` の成功を構成する。呼び出し準備の成功や完成後の形を前提にしない。

元callerを `s`、型付き値列を `values` とすると、memory prefixは次の3部分からなる。

1. 元callerのscalar memory。
2. 元callerの実slot数だけの参照・宣言領域用placeholder。
3. 借用vector parameter用placeholder 1個。

これを `P = receiverPrefix s` とすると、準備後のmemoryは `P ++ cells ty values`、bindingはcounterの元addressを先頭に `P.length` からの連続address、slotは新しいvector view、scalar 0、scalar 1以降の値引数となる。callee scopeは元scope+1、scalar baselineは元のままである。immutable grant/view履歴の個数をcallerの実slot数へ加算しない。

vectorの借用は新しいviewを追加し、元heapと既存viewsを保つ。readonly vector/counter権限もそのまま維持する。move後の空vectorでも元scalar fieldを0へ正規化しない。

## 実引数評価とcallee整理

`prepareArguments_receiver` は実 `resolveArguments` の結果がこのreceiver profileになることを入力条件にする。既存の `resolveArguments_stable` を使って、評価前のheader/counter条件とmemory prefixを評価後へ引き継ぎ、実 `prepareArguments` の成功と同じ変数配置を導く。実引数評価そのものの成功を一般に自動証明する定理ではない。

`compact_receiver` はprepared contextの追加viewとslotの形から、実 `CppMoveCallBindings.compact` の成功を構成する。callee vector bindingを1個に整理し、scalar slot順序・全memory・全scalar binding・baseline・scopeを保つ `QuotientFrame.QS` を導く。frameのstateも保持する。frameのwellFormedやUF固有の `FW`、成分不変条件をslotの形だけから主張しない。

呼び出し準備の資源上界には既存の `CppMoveArgumentFacts.prepareArguments_resources` 等を使用できる。本モジュールは停止成功と正確な配置の接続を追加し、旧UFの償却計算量全体の接続は残す。

[元UFのfields/QS/FW構成](union_find_receiver_layout.md)では、元heapの正常条件からこのprofileのvector証明条件までを接続する。実引数評価の一般成功やcaller全体の自動生成は別段階である。

## 検査と残件

`tests/test_cpp_move_receiver_layout.py` はmemory長3/binding長1の差、同じ値を独立cellへ配置すること、readonly権限、空値列、元scope/baselineを確認する。move後の元UF全5methodについて実引数評価結果を確かめ、一般のprepare定理を適用する。rootではprepareとcompactの実成功およびQSを一般定理から構成する。不正header/address/型/値域/書込み権限の拒否と、moved-fromの空vectorに残るscalar値も検査する。

[同一TU receiver生成](context_method_receiver.md)で選ぶObjectRefとこの配置定理の一般接続、元caller ASTのcallee/receiver/引数評価順と副作用、UF固有FWの自動構成、償却証明と任意混在寿命列は残る。構築・返却・destructor、割当/resize/nested/異種vector、公開UFの元sourceとの相違、他の旧ライブラリも未完了である。
