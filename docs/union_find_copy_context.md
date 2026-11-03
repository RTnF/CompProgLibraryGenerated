# Union-Find の copy 結果を Context へ接続する

`Proofs/UfCopyContext.lean` は読み取り専用の元 receiver から実際の
`CppClassCopy.copyClass` の成功を構成し、その結果を再びメソッド呼出しに
使える `Context` へ export する。元配列は source object の view/header から
解決し、呼出し元が別の配列を渡す入口にはしない。

`source_profile` / `source_copy` は、コピー先の constness に応じた profile と
実コピーが、監査済み fixture から生成した
`UnionFindPublicCompatInstance.Construction.copy` / `copyConst` に一致することを示す。
生成全文の検査は `test_context_class_ir.py` が行う。ソースからモデルへの
意味対応と標準 vector copy の契約は [信頼方針](trust_policy.md)に従う。

元 `_num_groups` と `_n` は別々の値のままコピーする。`_n` を配列長へ
置き換えないため、配列が空になった moved-from オブジェクトの値も保持する。
コピー先の view/header と 2 scalar bindings の権限はコピー先の constness
から決まり、元が readonly でも mutable なコピー先を構成できる。
新しい buffer は同じ items/limit を持ち、capacity は要素数、epoch は 0 になる。

`UfCopyContextPreserve` は元 field の slot/index/address・値・権限、元
view/header と receiver を保持する。元の可変 UF 状態も同じ親配列・rank・
counter・要素数を持つ状態へ復元する。空の header は materialize 時の
形式的 owner 番号が新しい allocation によって変わり得るため、無条件に
owner 同一を要求せず、items/capacity/limit/epoch の保持を示す。
既存 grant の read 保持には、元 grant と元 allocation 内の owner という条件を使う。

`UfCopyNewState.new_state` は、有効な UF 不変条件と `_n = 配列長` の元データから、
mutable コピー先の可変 UF 状態を構成する。2 scalar addresses の分離、
新 heap の readable/Unique/OwnsAll/AllocationsValid、limit、baseline と scope を
同時に保証し、その後の通常メソッドの一般定理へ接続できる。
raw copy や moved-from getter にこの強い `_n = 配列長` 条件を追加しない。

`UfCopyReadReady.ready` はコピー先が mutable/const のどちらでも、読み取り用
receiver、値と権限、新 heap の不変条件、baseline と scope 条件を構成する。
`UfCopyCounterCall.counter` は元 receiver の条件から実 copy とコピー先の
生成済み const `num_groups()` 呼出しの正常終了を同時に導く。返却値は元の
counter で、copy と getter の合計 work 増分は `配列長 + 14` 以下になる。
getter はコピー直後の全 payload/read/scalar/receiver を保持し、追加資源は
`UfReadPrepareBudget.Resources` の caller-only 3 peak 条件を満たす。
コピー自体の 3 peak は下表の式による。成功 copy/call、UF 不変条件や
`_n = 配列長` を追加前提としないため、moved-from 元にも適用できる。

`UfCopyReadQueries.size` / `same` は同じ元状態から実 copy とコピー先の
生成済み const query の正常終了を同時に構成する。親配列の Forest、範囲内の
引数、size では根の重み条件を用い、到達する根・成分サイズまたは連結性を
返却値へ接続する。引数式の型・値は実際のコピー先 Context で検査する。
成功 copy/call や `_n = 配列長` を前提に追加しない。各 query 後には全 payload、
既存 read、scalar memory、receiver を保持し、query 自体の caller-only 3 peak を保証する。

`n` をコピーする配列長、`E` を引数式の nodes、`r` を下降 rank とすると、
copy と query の合計 work 増分は次の式以下になる。

| 操作 | 一般の Forest | 有効 UF と History を併用した系 |
| --- | --- | --- |
| const size(a) | `n + E + 16*r(a) + 53` | `n + E + 16*log2(n) + 53` |
| const same(a,b) | `n + Ea + Eb + 16*r(a) + 16*r(b) + 88` | `n + Ea + Eb + 32*log2(n) + 88` |

対数上界の `size_log` / `same_log` は UF 不変条件と履歴から、
`log2(n) - rho(i)` を下降 rank にする既存定理を用いる。一般の Forest だけで
木の高さを対数と仮定しない。`size_log` は実際の成分の要素数との一致も返す。

元 receiver・readable header と型の合う fields、Unique/OwnsAll/AllocationsValid
などの元状態の条件からコピーを構成し、コピー成功を追加前提にしない。
HeadersLive を併用すると、新 heap の不変条件と次の資源式を得る。
`n` は実際にコピーする配列の要素数である。

| 項目 | 保証 |
| --- | --- |
| work 増分 | `n + 4` |
| scalar memory / bindings | 2 件ずつ追加、元 prefix と base を保持 |
| heap 常駐増分 | `n + 1` |
| scalar peak | `S = max 元SP (元scalarLive + 4)` 以下 |
| heap peak | `H = max 元HP (元heapLive + n + 2 - 元baseSpace)` |
| 全体 peak | `max 元total (S + H)` 以下 |

これらは既存評価器の抽象単位であり、実測 bytes や実測時間ではない。
常駐増分 `n+1` と一時 peak の `n+2` を区別する。

`test_uf_copy_context.py` は複数 owner・readonly source・mutable/const target、
capacity 9/要素数 4、epoch 5 の元 buffer と独立したコピー、`_n=99` の保持を
検査する。実 generated const size、コピー先の unite と元/別 owner の保持、
const コピー先への書込み拒否を確認する。header allocation がない moved-from
状態でも、両コピー先の getter と元の値・ghost owner の扱いを確認する。
一般の copy→getter 定理も、複数 owner と moved-from の両例で任意のコピー先権限に適用する。
一般の size/same 定理は任意の元/先権限と caller の変数引数で適用し、同一成分・
別成分・同じ要素の generated call と、元/別 owner/コピー先の値・capacity・epoch 保持を検査する。
const same の C++ 比較と、コピー先を unite した後も const コピーが別成分を保つことも確認する。
同じ C++ fixture の copy・const copy・move 後 copy を固定 GCC の ASan/UBSan で
比較する。private fields の検査にはテスト専用の `-fno-access-control` を使い、
fixture 本体や公開ヘッダーを書き換えない。

任意の元 caller AST、copy/move assignment、move construction の一般生成、
scope 終了と任意の寿命混在列、コピー後の全操作列の資源合成は未完了である。
公開ヘッダーの番兵表現と非圧縮 API の切替もまだ行っていない。
本件を他の旧ライブラリやクラス全体の検証完了とは扱わない。
