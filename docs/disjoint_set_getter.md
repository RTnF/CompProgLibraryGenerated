# 旧 DisjointSet の getNum

対象は `experiments/library3/cpp/Graph/UnionFind.hpp` の元クラス `DisjointSet` と、その non-const メソッド `int getNum()`。公開 `UnionFind` への型 alias は追加せず、元ソースを変更せずに検証する。クラス全体の検証は未完了である。

## 用途と条件

初期化された `num_groups` の値を返す。整数値が型の範囲内であることと、モデルの対応する scalar cell が読めることを本体証明の条件とする。数学的な連結成分数として解釈するには、別途 Union-Find 全体の不変条件が必要になる。コピーや move 後の値について、`_n` や vector 長からカウンタを再計算しない。

## 元ソースからの生成

`verifier/context_method_ir.py` に `method_names=['getNum']` を指定し、同一 Clang TU の元 FieldDecl と使用済み暗黙 copy の各初期化対象・型・順序を監査する。生成物は `Proofs/Generated/DisjointSetMethods.lean`。元フィールド順 `[_n,ps,num_groups]` に対して、合成引数だけ `[ps,_n,num_groups]` とし、置換 `[1,0,2]` を記録する。ObjectRef の scalarSlots は元の scalar 宣言順 `[_n,num_groups]` のままである。

全メソッドから書込みと外部可変参照の alias を解析した後、選択メソッドと到達する依存だけを変換する。生成 Lean に選択対象・全対象・依存・部分 coverage を明記する。元の recursive root を変換できたとは扱わない。

## 本体証明と検査

`Proofs/DisjointSetGetter.lean` の `body_correct` は、任意の有効な counter cell、`_n`、vector、fuel に対して、元ソースから生成した本体の実評価が保存値を返し、scalar fields と vector を保持することを証明する。既存の共通評価補題を利用する。モデルの本体仕事量は 2、peak は元 prefix の cell 数 + 6、vector allocation は 0。C++ 本体の時間と追加領域はいずれも O(1)。元 field 条件からの引数準備・実呼出し・復元と総資源は `Proofs/DisjointSetGetterCall.lean` の `call_resources` へ接続した。typed heap/scope と field の参照権限を条件として、fuel2 の終了、全 scalar memory・全 owner の payload lookup 保持、仕事量≤元+10、scalar/heap/全体 peak の上界を構成する。保存値の `_n` と vector 長の一致は要求しない。詳しい計数は [共通 scalar getter call](scalar_getter_call.md) を参照する。

`tests/test_context_method_selection.py` は生成物との完全一致、一般本体定理、通常・空・moved-from の Context 呼出し、元 C++ の UBSan 実行を検査する。copy に加えて std::move 構築・move 代入後の移動元/先の getNum 値も確認する。C++ ケースは `tests/imports/disjoint_set_getter.cpp`、Lean ケースは `tests/lean/disjoint_set_getter.lean`。通常ケースでは `_n` とカウンタに異なる値を置き、フィールドの取り違えを検出する。

## 元のソースからの変更と残件

元 C++ の機能・型・入力範囲の変更はない。合成関数の引数順を並べ替える処理だけを変換器に追加した。`tests/test_disjoint_set_getter_call.py` で元 field からの 3 peak 定理の実適用、readonly size field、counter の権限不足拒否も検査する。

元 constructor、recursive root、unite/same/size、任意 caller AST、コピーや寿命を含む全操作列、公開版の相違解消は未完了。getNum の部分検証を、旧クラス全体または全 experiments の検証完了とは扱わない。
