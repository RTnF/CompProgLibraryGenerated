# Scalar getter の実呼出しと資源

`Proofs/CppScalarGetterCall.lean` は scalarOnly な式を返す生成 NProgram について、入力の式の意味から実行終了、caller への復元、値保持と資源上界を構成する。成功した本体・finish・call を前提にしない。heap の型付き正常性、scope、元 memory prefix は明示した条件である。

`body_good` は任意の scalarOnly 式と有効な denotation に対し、fuel 2 で return を終え、Core、仕事量、scalar/全体 peak、storage 保持を保証する。既存の scalar 評価と `Good.charge/trans` を再利用する。`call_resources` は prepare/compact の実結果から finish/restore を構成し、元 scalar memory、すべての owner の payload lookup、仕事量と 3 peak を保証する。`call_from_prepared` はその射影である。

## 引数順の構成

`Proofs/CppMoveValueReceiver.lean` は vector 参照、scalar 値、scalar 参照の順を扱う。元の header と scalar cell、参照権限から、左から右の評価、prepare、compact と callee の配置を構成する。値を一度捕捉した後も、counter の参照は元の実アドレスを指す。値と counter が異なる場合や、元 vector が move 後の空状態でも、counter を vector 長で置き換えない。

prepare 後の memory 長は元の memory 長 + caller の slot 数 + 2、scalar binding は 2 個となる。caller の slot 数は既存の宣言・参照を保持する保守的な prefix の計数であり、C++ の新しい vector 要素の割当ではない。scalar 値式の node 数を m とすると、準備の仕事量は元 + m + 6 以下。フィールド変数なら m=1 である。

## 旧 getNum への接続

[旧 DisjointSet の getNum](disjoint_set_getter.md) の元 FieldDecl と生成 body へ接続する。`Proofs/DisjointSetGetterCall.lean` の `call_resources` は元 field/header/capability と typed heap/scope 条件から prepare を構成し、実 getNum 呼出しの返却・復元までを導く。連結成分の数学的不変条件や `_n = vector 長` を追加しない。

caller s の scalarLive を L、slot 数を K、scalar memory 長を M、base を C、scalar peak を P とする（自然数の減算は切詰め）。

- B = max P (max (L+3) ((M+K+6-C)+6))。
- H = max（元 heap peak）（元 project の liveSpace - baseSpace）。
- 実行後の scalar peak ≤ B、heap peak = H、全体 peak ≤ max（元の全体 peak）(B+H)。
- B ≤ max P (L+K+12)、仕事量 ≤ 元+10。

B は保存値としての `_n`、counter、vector 要素数に依存しない。K を含む caller prefix の保守的計数を隠して、任意 Context に対する追加領域 12 と断定しない。heap peak の式は、もともと存在する liveSpace の計数も含む。入力の peak が既存 liveSpace を下回る Context では、その既存量を観測して正規化する。peak の増加を新しい vector 割当とは解釈しない。単位はモデルの抽象領域であり、実機の byte 数・実測値ではない。

`tests/test_disjoint_set_getter_call.py` は一般 scalar return、通常/空/moved-from の fuel2 呼出しと、元 field 条件からの一般資源定理の適用を検査する。`_n` が readonly でも値捕捉でき、counter 参照の権限を広げないことも確認する。元 C++ の move 後の値保持は既存 `test_context_method_selection.py` の UBSan 経路で別に確認する。

元 constructor・recursive root 等の残り API、任意 caller AST の receiver 評価や寿命混在の全体証明は残る。既存公開 UnionFind の相違解消や全 experiments の完了とは区別する。
