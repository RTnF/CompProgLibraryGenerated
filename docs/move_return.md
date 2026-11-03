# 所有 vector の返却 move

`Proofs/CppMoveReturn.lean` は [Context](move_context.md) の callee から caller への所有 vector 返却を定義する。現行の同一整数型 flat vector モデルにおいて、返却先を caller scope に先に構築し、callee の local を [逆構築順で破棄](move_destroy.md) してから caller の scalar 状態を復元する。

元 return AST・callee body 全体・暗黙 class move の scalar 宣言順との生成接続は未完了である。const rvalue の copy fallback、NRVO、nested/異種 vector、ユーザー定義 destructor や例外巻戻しも別途必要であり、元ライブラリの機能を削ってこの範囲に限定しない。

## 終了と寿命

`returnOwned` は実 `CppMoveViews.construct` を使って返却 destination を caller.scope に追加し、`finishScope` で callee.scope の所有物を破棄する。move 元の header は元の scope に空のまま残り、その scope が callee なら破棄される。caller 側のオブジェクトから move した場合は空の header が caller 側に残る。

`returnOwned_ready` は元 source の resolve・書込み権限、caller/callee scope、view/grant prefix、scalar memory の型と長さ、Unique/ReadableHeaders から実返却の成功を導く。完成した返却の成功を入力条件には置かない。

`constructed_readable` は move 後の可読性を保持する。`destroyList_keeps` / `finishScope_keeps` は別 scope の header を保持する。`returnOwned_target` は実成功時の返却 view が解決でき、その header が元 source の allocation/limit を持ち、caller scope と指定権限で生きていることを示す。

`returnOwned_invariants` は Unique、ReadableHeaders、OwnsAll、AllocationsValid、GrantBounds、HeadersLive を全体で保持する。`returnOwned_no_resurrection` は既に無効な捕捉済み要素参照が復活しないことを示す。const destination の object view と、元に捕捉した writable 要素 grant の権限は区別して保持する。

## 資源上界

`scopeBudget_constructed` は、caller scope へ move した後の callee 破棄予算が元の callee 予算を超えないことを示す。新 destination は閉じる scope に属さず、空になった元 header の費用は旧要素数 + 1 以下である。

`returnOwned_resources` は次を証明する。

- work out ≤ work callee + 元 callee の scopeBudget + 2。追加 2 は move と caller scalar 復元の各 1。
- heap liveSpace out ≤ 元 liveSpace + 1。増加は返却 destination header 一個分で、格納領域は転送する。
- heap baseline を保持し、heap peak out ≤ H。ただし H = max 元 heap peak (元 liveSpace + 1 − baseline)。
- 復元 scalar peak は S = max (max caller scalar peak callee scalar peak) (scalarLive caller)。
- Context peak out ≤ max (max caller peak callee peak) (S + H)。

これらはモデル上の work/領域予算であり、実測命令数や Lean の台帳領域ではない。ghost grant/view/tombstone の個数は C++ の追加領域へ計上しない。固定 STL 契約と意味対応の信頼境界は既存方針に従い、新しい公理は追加しない。

## 検査

`tests/test_cpp_move_return.py` は実 local からの返却、const destination、元要素 grant の読み書き保持、scalar 参照更新、無効参照、空と予約済み空、別 local の破棄、caller から借用した vector の返却、過去 peak と baseline を検査し、一般終了・target・不変条件・資源・非復活定理を適用する。

固定 GCC 13.3 / C++17 / ASan / UBSan と `-fno-elide-constructors` では、明示 move 返却後の要素参照と const destination、空/予約済み空、borrow 元オブジェクトの独立性、元 UnionFind 候補を local から返した後の操作を有限照合する。これらの例から任意 class caller の意味対応が完成したとはしない。[暗黙 destructor 監査](class_destroy.md) の宣言計画と実 body/return の生成接続を続ける。
