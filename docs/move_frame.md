# move の view と型付き Frame の接続

`Proofs/CppMoveViews.lean`、`CppMoveFrame.lean`、`CppMoveSpace.lean` は、[move 構築](move_headers.md)・[move 代入](move_assignment.md)の header/allocation モデルを既存の型付き `CppFrameCopyAssign.TrackedFrame` へ投影する。対象は同じ整数型を持つ flat vector 群である。元クラスの AST から任意 caller の実行までを接続する検証は未完了であり、元 union_find の公開昇格条件を満たしたとは扱わない。

## オブジェクトの view と要素参照

object view は header ID と書込み権限を持つ。別の view slot が同じ header を指す場合も自己 move と判定する。const view を追加しても header の最大権限や取得済み mutable 要素参照は変えない。readonly view からの move、writable な要素参照取得は拒否する。const rvalue が copy overload を選ぶ C++ の規則は別途 AST/caller 側で扱う必要がある。

要素参照の grant は allocation ID・epoch・要素世代・取得時の権限を保存する。object view の再解決で要素 grant を書き換えない。capture の一般定理は単一 grant の追加、既存 grant の読取り、全 object view の解決、header/allocation と資源記録の保持を示す。

`materialize` は既存の要素 grant を Frame binding の先頭に保ち、その後ろへ現在の object view の binding を置く。Frame の一時的な view binding から取得した参照を永続参照として外へ持ち出してはいけない。永続化する capture は上位 grant 台帳へ登録し、再投影後もその同一性を維持する。caller prepare/finish がこの義務を満たす一般証明は残る。

## 投影と一般証明

live allocation の ID と payload を保ち、scope は現在の owning header から得る。空 header は allocation 表の後ろに容量0の補助 buffer として置く。これは空 vector の header を表し、要素領域を追加するものではない。補助 ID、tombstone、view/grant 台帳を C++ の使用領域へ加算しない。

- `materialize_ready`: supported な整数型と、入力の全 live allocation の owner 一致・buffer 妥当性から投影 Frame の整合性を導く。
- `materialize_read`: 存在する grant の owner が元 allocation 表長内である場合、`OwnsAll` と型・buffer 条件の下で Frame と元 heap の読取り結果が一致する。epoch・世代・添字の拒否を含む Option 全体の対応である。
- `materialize_dead_read`: 表長内の退役済み allocation を Frame でも拒否する。空 header の補助 ID で旧領域を復活させない。
- `materialize_view_ready`: 元 view の解決・可読性、`Unique` / `OwnsAll`、型・buffer 条件から現在の buffer と実 Frame.resolve 成功を導く。権限と scope を保持し、空 header も扱う。

root maximum は取得済み mutable 要素参照を const の移動先で無効にしないよう true とし、新規 object アクセスは view と header の双方で制限する。任意の低水準 binding を外から偽造してよいという意味ではない。

## 使用領域

`materialize_liveSpace` は `Unique` / `OwnsAll` / `HeadersLive` の下で、投影 Frame と元 heap の liveSpace が一致することを示す。`HeadersLive` は各 header が指す allocation の実在を要求する。領域を持つ header と live allocation の単射全射、空 header との分割、容量総和から証明する。各 header を1単位、各 allocation の容量を一度だけ数える。

移動構築・代入は `HeadersLive` を保持する。代入の保持には `Unique` が必要である。view 経由の move の一般定理は正常条件からの成功、所有不変条件、既存の work/peak/base 記録と局所的な資源式へ接続する。資源の単位は抽象モデルのものであり、命令数や実測値ではない。全 caller の式評価と stack、破棄を含む総予算は未完了である。

## 検査と残る範囲

`tests/test_cpp_move_frame.py` は一般定理の適用と有限モデルで、mutable/readonly aliases、別名経由の自己 move、空/const の移動先、既存 grant の read/write、旧 target の参照失効、世代不一致、Frame 整合性と liveSpace 一致を確認する。元 C++ の有限照合は既存の move header/assignment テストにある。有限例を一般的な write 対応の証明とは扱わない。

[固定要素書込みの戻し込み](move_write.md)は別途接続した。通常操作の結果の戻し込み、NState/caller prepare/finish、異種 vector、再確保・破棄との任意混在列、クラス scalar の宣言順処理、実 AST の overload 選択、全 caller 資源、元 union_find と公開版の相違解消は残る。元の API・入力範囲・機能を狭めて代替することはしない。
