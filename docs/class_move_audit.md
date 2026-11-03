# 暗黙 move 構築・代入の AST 監査

`verifier/class_move.py` は、同じ TU に実体化した元クラスの暗黙 move メンバーを宣言 ID で監査する。現在の coverage は `member_identity_only`。move 代入の Profile と実行器呼出しは [class move 代入](class_move_assignment.md) へ接続した。元 caller の field-slot と実代入式、move 構築の生成接続は継続する。この監査や有限 native 検査だけで move を一般に検証済みとは扱わない。

## 実体化と同一性

`materialize_move(..., kind)` は `construct` または `assign` を指定する。`vector_stl.translation_unit` の `move_kind` は、元ヘッダーを include し、その操作だけを使う専用 witness をコンパイルする。copy witness と混ぜず、構築監査に代入可能性を要求しない。const スカラーがあって move 構築できるが代入できない型を区別する。既定の copy-only / copy-assignment witness は維持する。

共通の `audit_class_fields` が元 source のパス・内容 hash、dump、qualified class、FieldDecl、属性・継承・destructor 等を確認する。move は使用済み暗黙 defaulted 宣言で、元クラスの非 const `Class&&` パラメータを持つことを要求する。ユーザー定義・明示 default/delete を暗黙本体として扱わない。

元フィールドは xvalue MemberExpr → CXXStaticCastExpr NoOp xvalue → 元 ParmVarDecl の lvalue という実 AST を検査する。FieldDecl ID、元パラメータ ID、型、cast、value category、this、arrow、宣言順を照合する。class/field の名前で意味を選ばない。

構築子は各フィールドの CXXCtorInitializer と空 body を要求する。vector は使用済みの標準 move 構築子、残りのスカラーは対応する xvalue フィールドからの LValueToRValue 初期化である。const スカラーの構築は許し、生成 metadata の writable を false にする。代入は vector の CXXMemberCallExpr、宣言順の scalar BinaryOperator `=`、最後の lvalue `*this` 返却を要求する。

## 標準 vector と受理範囲

vector callee は同じ dump の実宣言 ID、TemplateInstantiationPattern、既存の pristine primary / out-of-line / helper / allocator の監査で確認する。`audit_vector_nodes` の `move_assignment=True` だけが scalar / std allocator / 非 const vector&& の move operator= を受け入れる。copy-assignment モードとの同時指定は拒否する。既定の vector lowering で operator= を新たに受理する変更は行っていない。

対象は最初の非 const scalar vector と、その後の固定幅 scalar フィールド。move 構築の const scalar、mutable フィールド、クラス名・フィールド名・整数型が異なる形を確認する。const vector のメンバーコピー fallback、nested vector、vector<bool>、参照・volatile・bitfield、継承・属性・ユーザー destructor、明示特殊メンバー等の未対応形は拒否し、完了した範囲へ数えない。const rvalue がクラスの copy を選ぶ呼出しは、実選択された copy 宣言の監査・生成へ接続する別義務である。

## 検査と残る接続

`tests/test_class_move_audit.py` は両 move メンバーの正例、元フィールド・cast・パラメータ・順番・型・使用/暗黙 flag・標準 callee・代入先・戻り値の変異、別 TU / source、標準の使用済み flag / 特殊化の拒否、型や名前が違うクラスと const scalar を検査する。copy-only と copy-assignment の既存経路も確認する。

固定 GCC / UBSan の有限検査では、元の要素参照が移動先の要素を指すこと、vector オブジェクト参照の同一性、移動元への再書込み、move 構築、固定実装の自己 move、UnionFind の移動後スカラーとコピー再代入を確認する。破棄済みの参照を読まない。これらは Lean の一般的な lifetime 証明ではない。

実行モデルでは vector オブジェクト/header と allocation の同一性を分ける必要がある。元要素参照を保持し、旧代入先の要素参照を無効化し、後の移動で復活させない。immutable grant、object の別名参照、scope、型・最大権限、baseline/peak と旧要素の破棄仕事量を保つ必要がある。現行 `Frame` の binding を書き換えたり、`State.transfer` をそのまま C++ move として扱う接続は行っていない。固定実装の自己 move を copy 自己代入の恒等操作として扱わない。
