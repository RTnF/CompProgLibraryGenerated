# 暗黙コピー代入の AST 監査と評価器 profile の生成

`verifier/class_assign.py` は、元ヘッダーの暗黙コピー代入を固定 Clang で実体化し、同じ TU の宣言 ID から、既存の `CppClassAssign` 評価器に渡す profile を生成する。クラス名や `_ps` などのフィールド名で変換規則を選ばない。この単独 profile 生成の coverage は `member_identity_only`。実 caller は `class_call_ir` の明示的な `assignment=True` モードで接続する。

## 実体化と同一性

`vector_stl.translation_unit` に既定 false の `copy_assignment` を追加した。true のときは `target=source` を使う別の witness で copy operator= だけを使用させる。コピー構築を必要としないため、copy constructor が deleted でも、代入が可能なクラスを調べられる。既定のコピー構築 witness は変更せず、const フィールドがあるコピー可能クラスを一律に代入不能として拒否しない。

元 source の実パス、内容 hash、同じ dump の識別子、qualified class、FieldDecl、属性・継承・destructor 等の共通検査は `class_copy.audit_class_fields` を使う。record や標準宣言を他の TU から混ぜたもの、source 内容が変わったものは拒否する。

operator= は使用済みの暗黙 defaulted 宣言で、const class& の元パラメータと class& の戻り型を持つことを要求する。body はフィールドごとの処理を宣言順に持ち、最後に lvalue の `*this` を返す。明示的に定義／default／delete された代入、move、追加の処理や別の返値を同じ形として黙って受理しない。

## メンバーと標準 vector

最初の vector 代入は、暗黙本体に現れる CXXMemberCallExpr として検査する。代入先は `this` の対応 FieldDecl、元は元パラメータの同じ FieldDecl であることを確認する。残りは型付き scalar の BinaryOperator `=` と、対応 source フィールドの LValueToRValue load であることを確認する。宣言 ID、型、const/mutable、value category、arrow、this の型、元パラメータの ID を検査する。

標準 vector の operator= は、同じ TU の callee ID と TemplateInstantiationPattern で特定する。既存の pristine primary・out-of-line 定義・allocator・使用済み helper の特殊化監査を通す。追加した operator= の監査は明示的なモードでのみ使い、固定幅 scalar／標準 allocator／const vector& のコピー代入に限定する。move operator= や vector<bool>、ユーザー特殊化をコピー代入として扱わない。通常の vector lowering で operator= を受理する範囲は広げていない。

標準 vector の意味・容量・参照・資源は既存の[コピー代入契約](vector_copy_assignment.md)を使う。標準ライブラリ全体の C++ 本体を新たに Lean へ変換したという主張ではない。

## 生成物と証明の接続範囲

`emit_class_assignment` は source hash、フィールド順、型付き Profile、assign/trackedAssign の実評価器呼出し、ghost データ射影定理を生成する。stable な生成名に Clang の一時的な宣言 ID を埋め込まず、ID は監査の証拠として扱う。監査前後で source の内容が変わった場合も拒否する。

候補 UnionFind から生成した profile は既存の `UfClassCopyBridge.profile` と定義的に一致し、任意 NState/ObjectRef に対して新評価器への呼出しと一致することをテストする。単独 profile 生成だけでクラス全体の代入を検証済みとは扱わない。

## 検査

`tests/test_class_assign_ir.py` は候補の実宣言、フィールド順、標準 callee と生成 Lean を検査する。this、source parameter、source/destination field、順番、cast、opcode、return、使用済み／暗黙 flag、戻り型、callee ID、標準特殊化、別 TU、source hash を変えたものの拒否を確認する。

名前を変えた mutable vector、unsigned int/long/bool の混在、copy constructor が deleted でも代入可能な型、const フィールドでは既存の copy-only が使えることも確認する。元と候補の UnionFind は n=0/1/2/4/17 の特殊メンバー操作を固定 GCC/UBSan で照合する。この有限照合を move の一般証明としない。継承、ユーザー destructor、参照／volatile／bitfield、nested vector、vector<bool>、明示的代入など、未対応の意味を必要とする形は拒否する。

## 実 caller の生成

`lower_class_callers` / `emit_class_callers` の `assignment=True` は同じ TU の監査済み代入宣言 ID と FieldDecl ID を使用する。構築子 export と receiver の vector/scalar slot は元の型・権限・mutable・宣言順に対応する。既定の copy-only 経路は維持する。コピー構築を実際に使う場合だけ追加で copy constructor を監査し、削除された構築子は実行 stage を作らない。

完全な代入式、連鎖代入、代入結果へのメソッド呼出し、代入結果からのローカルコピー構築を生成する。C++17 の operator 記法は右辺→左辺、明示的 member call は receiver→引数の順に再帰的に評価し、結果の ObjectRef は代入先とする。条件・複合 scalar 式・class reference の free caller 戻り値など、未対応の形は拒否する。

生成される `CallerCommand.assignObject` は `assignClass` を直接実行する。`caller_assign` は評価器の実成功と caller の同じ出力状態を対応させ、`caller_assign_tracked` は任意の初期 ghost 世代に対する追跡付き遷移へ持ち上げる。保存済み外部参照は引き続き tracked reference で扱う。scalar reference 引数と、その場で取得する vector 参照を外部の保存済み参照と混同しない。

`tests/test_class_assignment_callers.py` は実際に生成した Lean を実行し、固定 GCC/UBSan と照合する。自己代入、readonly 元、連鎖、両記法の異なる評価順、代入先メソッド、コピー構築、void caller、構築子削除、宣言 ID や const の変異拒否を検査する。有限照合とこの実行器対応だけで任意 caller 全体の終了・資源証明を完了したとは扱わない。move、混在 lifetime 操作列、任意 caller の一般的な正しさ・資源、公開版の差異解消と他の旧ライブラリの検証は未完了である。
