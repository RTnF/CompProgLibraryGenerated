# move 後の要素書込みと Frame の戻し込み

`Proofs/CppMoveWrite.lean` は、[型付き Frame 投影](move_frame.md)について、捕捉済み整数要素参照への固定書込みを接続する。`restoreWrite` は既存の `CppFrameCopyAssign.write` を実行し、実際の buffer と資源記録を元 heap へ戻す。`writeEvent` は元 heap のデータ書込みに、同じ1イベントの資源予算を付ける。

## 全結果の対応

`restoreWrite_eq_event` は任意の grant ID と書込み値について、両実行の Option 結果が一致することを証明する。前提は supported な同一整数型、`AllocationsValid`、`Unique`、`OwnsAll`、`HeadersLive`、`GrantBounds` である。元 heap の整合性から Frame の整合性と commit 成功を導き、結果 Frame の正常性や実行成功を前提として置かない。

`GrantBounds` は、既存 grant の owner ID が allocation 表長内にあることを要求する。退役した tombstone は許す。capture で取得する参照についてこの条件を生成し、move 構築・代入と固定書込みで保持する一般証明がある。任意に偽造した参照を有効と扱う条件ではない。

対応は成功だけでなく、未知 grant、readonly grant、退役 allocation、古い世代・epoch、添字や値の拒否を含む。const の移動先が領域を所有していても、以前取得した mutable 要素 grant の権限は失われない。

`box_write` は型付き primitive と元 `writeRef` の buffer・仕事量・peak の対応を示す。`decode` / `unbox` は integer payload だけを戻し、child vector を含む値を拒否する。往復の一般証明により、復号の際に要素や metadata を落とさない。

## 書込み後の状態と資源

`writeEvent_success` は実成功から元 grant、live allocation、primitive 実行、実出力の対応を取り出す。一般定理は型・buffer 妥当性、一意所有、全 live allocation の所有者、header が指す allocation の実在、grant ID 範囲を保持する。他の allocation は同じ tracked 値のまま残り、header・view・grant 台帳を変更しない。要素世代関数も保持する。

`writeEvent_resources` は liveSpace と baseSpace を保持し、仕事量を1増やし、peak を `max oldPeak (oldLiveSpace + 1 - baseSpace)` にする。`restoreWrite_eq_event` により実 Frame 書込みにも同じ結果が対応する。これはモデルの1書込みイベントであり、caller の添字・値の式評価や stack 全体の予算ではない。

## 検査と残る範囲

`tests/test_cpp_move_write.py` は、const 移動先に対する既存 mutable grant、readonly/退役/値範囲/未知 grant/child payload の拒否、更新結果と work/peak/liveSpace を検査する。任意 ID・値の一般対応を初期状態・move 後・書込み後へ適用し、capture による ID 範囲保持、他 allocation 保持、書込み後の Frame 整合性と資源定理も確認する。有限例の実成功は kernel で検証し、native の証明迂回を使わない。

対応は同じ整数型の flat vector 群に対する固定要素書込みである。NState/caller prepare/finish、一般の通常操作の戻し込み、allocation・resize・scope 破棄との任意混在列、異種 vector、クラス scalar の宣言順、実 AST の overload 選択、全 caller 資源は残る。元 union_find の公開版との差異を解消したとは扱わない。
