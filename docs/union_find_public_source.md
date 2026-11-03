# 公開切替候補の Union-Find ソースと呼出し証明

`tests/imports/union_find_public_compat.hpp` は、元の別フィールド
`_ps` / `_num_groups` / `_n`、通常メソッドの経路圧縮、両構成子を保ち、
公開版にある const query も overload として残す隔離 fixture である。
**`library/union_find.hpp` はまだ番兵表現のままで、切替は行っていない。**

`Proofs/Generated/UnionFindPublicCompat.lean` はこの fixture 全体から
`context_class_ir` により生成する。`tests/test_context_class_ir.py` は
ソース SHA・公開宣言の bridge 検査と生成全文比較を行う。
生成対象から漏れる宣言を拒否する範囲は
[クラス生成経路](context_class_converter.md)を参照する。

`Proofs/UfPublicSource.lean` の `Proofs.UfPublicSource` は、生成された
実際の receiver 引数写像と `callFuel` / constructor export を証明対象にする。
通常 5 program、const 3 program、両構成子と copy profile は既存の
証明対象と `rfl` 一致する。非公開 readonly helper の本体対応も示す。

`Mutable.root_call` / `same_call` / `size_call` / `unite_call` /
`counter_call` は、元 receiver の field・view・header と純粋な引数式の条件から、
生成 wrapper の正常終了と従来の全 postcondition を導く。
経路圧縮、成分の判定・大きさ、カウンタ更新、元メモリの扱いと
work / scalar・heap・全体の 3 peak を保持する。資源式は従来どおり
prepared / initial と caller を明示する一般式であり、任意 caller に対する
追加領域を数値定数だけで表すものではない。

`Readonly.size_call` / `same_call` / `counter_call` は const wrapper について、
返却意味、caller-only 資源式、全 owner の payload・全既存参照の read・元 scalar
メモリ・receiver 値の保持を導く。元の成功 call・prepare・body を追加の前提に
置かない。[readonly の保持](union_find_read_values.md)と
[caller-only の計数](union_find_read_call.md)をそのまま実 wrapper へ接続する。
const query の `_n` は親配列長への固定を要求せず、実ソースの配列長 guard を使う。

読み取り専用 query の対数上界には、森であることに加えて結合履歴を使う。
`Historical.descent_forest` は、有効な UF 不変条件と親へ厳密に増える
historical rank `rho` から、`log2 n - rho i` を下降 rank とする森を構成する。
既存の historical rank 上界により親への遷移で下降し、この rank は `log2 n`
以下になる。`Readonly.size_log_call` / `same_log_call` は実 wrapper の正常終了、
意味・保持・3 peak を同時に保ち、次の work 上界を得る。

| 呼出し | 元 caller からの work 増分の上界 |
| --- | --- |
| const `size(a)` | `a` の式 nodes + `16 * log2 n + 49` |
| const `same(a,b)` | 両式の nodes + `32 * log2 n + 84` |
| const `num_groups()` | `10`（一般の `counter_call`） |

ここで `n` は実親配列の要素数で、一般の森だけから対数高さを仮定しない。
size の結果は実成分の要素数、same の結果は Connected と同値である。

`Constructors.construct_sized_resources` / `construct_default_resources` は、
同じソースから生成した両構成子の実 export と、構築後の有効な通常操作列を
既存の構成・不変条件・償却証明へ接続する。構成子の正常終了、初期親配列、
操作列の返却数・意味、カウンタ・要素数の不変条件、既存 alpha 尺度での
全 work と 3 peak を保持する。sized 構成子は `0 ≤ n < 2^31` の範囲を扱い、
番兵のために `n + 1` の確保を要求しない。

これらは生成済みの通常/const メソッドと構成子の条件付き一般証明である。
任意の元 caller AST、implicit copy/move assignment・move construction、
scope 終了・任意の寿命混在列、通常/const を自由に混在した列全体の合成は
未完了である。copy profile の一致だけをこれらの完了と扱わない。
const / nonconst の同名 overload を併存させるため、無型の
`auto p = &UnionFind::same` 等には型指定が必要になる点も残る。
公開モデル/一次 proof の切替と既存公開定理の保持、他の旧ライブラリの検証も
引き続き作業対象であり、棚卸しの完了 flag は変更しない。
