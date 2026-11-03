# UnionFind の readonly receiver からの実呼出し

`Proofs/UfReadCall.lean` は公開切替用 fixture の const size／same／num_groups を、元 receiver の field／view／header 条件から、実引数評価、prepare、compact、本体実行、finish、restore まで接続する。成功した call・本体・prepare を入力条件にしない。公開ヘッダーはまだ置き換えない。

`Proofs/CppMoveReceiverPermissions.lean` は counter 参照の要求権限を Bool と含意条件で扱う。mutable 参照には元 binding の書込み権限が必要で、readonly 参照には要求しない。既存の mutable theorem や AST 変換器は変更していない。`ReadReceiver` の元 Field と解決可能な view／header から readonly vector と counter 参照を捕捉し、`_n` と引数は新しい値コピーとして配置する。元 readonly binding を writable に変更しない。

`prepare_read_frame` は元の読み取り可能 header、所有者の一意性・被覆、型付き allocation、limit、scope 条件から、実 prepare／compact と QS／FW を構成する。`Proofs/UfReadPrograms.lean` は const 3 メソッドの全 NProgram と callee 配置を定義する。正規 AST 変換器が生成した実 program 全体と引数写像との一致をテストする。namespace や型が異なる旧 DisjointSet を、この program の無条件 alias にしない。

`Proofs/UfReadBody.lean` は [const query 本体](union_find_read_queries.md) の実行証明を `runFuel` の正常終了へ持ち上げる。readonly な vector に対して、書込み権限を要求する補題を適用しない。本体の停止、返却、元 scalar prefix と親配列の保持、仕事量、scalar／heap／全体 peak を保証する。`finish_call` は型付き結果・prefix・scope 条件から実 finish／restore を構成する。

## 入力条件と結果

size／same の引数式は型付きの scalarOnly な意味を持ち、添字は実配列の範囲内とする。親配列は `Forest vec rank`、長さは 2^31 未満。size はさらに `Weights` を要求し、INT_MIN の不正な符号反転を除外する。`_n` の保存値と実配列長の一致は前提にしない。

- `size_call` は到達根 r の負の重み w に対して −w を返す。
- `same_call` は元配列での両到達根の一致を返す。
- `counter_call` は格納値を返す。空の moved-from vector でも `_n`／counter を配列長で置き換えない。
- 元 scalar memory 全体を復元し、対象の親配列を保持する。

`Proofs/UfReadPrepareBudget.lean` は元 caller だけを使う式へ引数評価・prepare の仕事量と peak を合成する。size の引数式の node 数を m、same の 2 式の合計を m とすると、呼出し全体の仕事量は次の上界を持つ。

- size: work(caller)+m+16·rank(a)+49。
- same: work(caller)+m+16·rank(a)+16·rank(b)+84。
- getter: work(caller)+10。

size はさらに、`UfClassInvariant.Valid` の条件下で返却値が成分の要素数に等しいことを保証する。same は返却する根の一致と `Connected` の同値を保証する。保持した配列の owner は元 receiver の buffer の owner と明示的に一致させ、無関係な owner の存在だけを示す postcondition にしない。

## 元 caller に基づく領域上界

caller を c、引数式の合計 node 数を m、scalar memory 長を M、slot 数を K、scalar base を C、receiverPrefix(c) の長さを P とする。減算は自然数の切詰め。

- B = max(max(c.scalarPeak, scalarLive(c)+m+3), (M+K+10−C)+10)。
- U = max(B, P+48−C)。
- H = max(project(c).heapPeak, project(c).liveSpace+1−project(c).baseSpace)。
- 出力 scalarPeak ≤ U、heapPeak ≤ H、totalPeak ≤ max(c.totalPeak, U+H)。
- U ≤ max(c.scalarPeak, scalarLive(c)+m+K+49)。

getter は m=0。3 メソッドともパラメータ数が 5 以下であることを使う。scalar の上界に heap の大きさや履歴 totalPeak を混ぜない。実 scalarBudget の式が heap peak と totalPeak の変更に依存しないことも検査する。

本体を持ち上げる `UfReadBody.execute` では、履歴 totalPeak を補助 Cq の heap 用 budget に保持する。実際の heap 上界は別の `CppStoragePeak` 証明から得て、全体 peak にだけ `max initial.peak` を明示的に残す。scalar の上界へ履歴 totalPeak を移す方法を避けている。

K は既存 caller の宣言・参照を保持する保守的な prefix の計数であり、C++ の vector 要素の新規割当ではない。上界を任意 caller の固定追加領域 49 と断定しない。H は既存 liveSpace の観測も含み、増加を新しい vector 割当と解釈しない。単位はモデルの抽象領域であり、byte 数・実測値ではない。rank の上界なしに対数時間や償却時間とも断定しない。

## 検査と残件

`tests/test_uf_read_call.py` は const 3 program 全体・元 FieldDecl に基づく引数写像の AST 生成一致を検査する。header の最大権限を任意 Bool とし、view と全 scalar bindings を readonly にした具体例から全前提を構成して 3 呼出し定理を適用する。実 callFuel による返却・元 memory／header／view 保持も確認する。空 header／`_n=4`／counter=1 の moved-from 配置では、readonly prepare と実 getter 呼出し、mutable 権限要求の拒否を確認する。

候補 C++ は変更せず、native ASan/UBSan は既存の検査経路を保持する。全 owner の payload・既存参照と異なる live scope の保持は [全 payload・参照の保持](union_find_read_values.md) へ接続した。任意 caller AST、scope 終了・copy export 等を含む寿命全体、公開 UF の切替、元 DisjointSet の残り API、全 experiments の完了は未達である。
