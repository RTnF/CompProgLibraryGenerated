# class move 代入の実行器と監査結果からの生成

`Proofs/CppMoveClass.lean` は [Context](move_context.md) 上で、vector move 代入、宣言順の scalar 代入、代入先参照の返却を実行する。`verifier/class_move.py` の `emit_class_move_assignment` は、元の暗黙 move operator= を再監査してこの実行器の Profile と呼出しを生成する。対象は現在の監査が受理する一つの scalar vector と後続 scalar フィールドである。

元 caller の FieldDecl と ObjectRef slot の対応、実 move 代入式からの生成は引き続き必要である。元クラス全体の検証完了とは扱わず、未対応 layout や機能は experiments に残して対応する。

## scalar 代入の意味対応

`scalarFields` は既存 `CppClassAssign.assignFields` を `project` 上で実行し、実 scalar memory と peak を Context へ戻す。`project_scalarFields` と `scalarFields_correspondence` は失敗を含む全 Option の一致を示す。vector heap、view、slot、scope、scalar binding と memory 長は変わらない。

各フィールドはその段階の source を読み、target へ書く。`[3,8]` に対する `a=b; b=a;` は `[8,8]` になり、全 source 値を先に保存する実行器へ置き換えない。`scalarFields_ready` は型・参照・権限を述べる既存 Ready から実成功を導く。

## class move

`assignClass` は ObjectRef の vector slot から現在の object view を取得し、実 `CppMoveViews.assign` を行う。その後 scalarFields を宣言順に実行し、return this の work 1 を課金して元 target の ObjectRef を返す。

`assignClass_ready` は元の vector view/書込み権限/可読性/limit/Unique と元 scalar Ready から全体の成功を導く。完成した class move の成功を前提には置かない。vector move は scalar の slot を変えないため、`project_scalarSlot` を使って Ready を移送する。

`assignClass_invariants` は heap の Unique/OwnsAll/AllocationsValid/GrantBounds/HeadersLive を保持する。`assignClass_no_resurrection` は既に無効な要素 grant が復活しないことを示す。`assignClass_metadata` は result=target、slot/scope/scalar binding/memory 長の保持を示す。

自己 move は固定 GCC の vector primitive に従って格納領域を退役させる。scalar の自己代入は値を保持する。元 UF の `_n` と count を証明の都合で 0 に変更しない。moved-from receiver に UF Strong が自動保持されるとは扱わず、その後の method ごとの安全条件や再代入による復元を別途接続する。

## work と領域

`assignClass_resources` は実解決された元 target header に対して、work out = work in + 旧 target 要素数 + 2 × scalar field 数 + 2 を証明する。vector primitive と参照返却の各 1、scalar 読書きの各 2 を含む抽象 work である。

liveSpace out + 旧 target 容量 = liveSpace in、baseline 保持、heap peak = max 旧 heap peak (旧 liveSpace + 1 − baseline) を示す。`assignClass_peak` は scalar peak ≤ S、および Context peak ≤ max 旧 Context peak (S + H) を示す。S = max 旧 scalar peak (旧 scalarLive + 1)、H は上の heap peak である。ghost view/grant/tombstone の数を C++ の追加領域へ計上しない。

固定 STL と C++→モデルの意味対応は既存の信頼境界に従い、新しい公理は追加しない。これらの work は実測命令数ではない。

## 監査からの生成

`emit_class_move_assignment` は source hash を監査の前後で照合し、同一 TU の元 FieldDecl、元 rvalue source、this、標準 vector callee、scalar の読書きと順序、target 参照返却を監査する。field 名を規則の選択に使わず、型と権限の Profile、元 field 名の順序、source hash、直接評価器呼出しと result_target 定理を生成する。AST ID は同じ監査内の証拠に使い、生成名へ埋め込まない。

監査 coverage は引き続き member_identity_only であり、FieldDecl を実 caller slot に結び付ける義務を残す。const rvalue の copy fallback、move 構築、他 layout/異種 vector、実 body/返却/destructor と通常操作・resize/割当の任意混在列への接続も継続する。

## 検査

`tests/test_class_move_ir.py` は scalar 全 Option 対応と元 Ready からの終了、不変条件・非復活・work/peak、自己/非自己 move、元 UF の生成 Profile と実呼出し、source 不変と監査中変更の拒否、namespace 検査、混在型の境界値を確認する。unsigned 32-bit 最大値、signed 64-bit 最小値、bool を Lean と固定 GCC 13.3 / ASan / UBSan で照合する。元 AST の slot 配置を一般に検証済みとはしない。
