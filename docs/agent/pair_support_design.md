# pair / vector<struct> 対応の設計メモ（2026-11-10、着手前の調査）

目的: `vector<pair<A,B>>` を引数・戻り値・局所変数に持つ原本（`interval_union`、`search_util::counts`、`sort_util::arg_sort`、`element_count`、`char_count`）を、公開側でも元のAPIのまま検証する。公開側が2本のvectorに分けている違反（`docs/experiments_status.md`）を解消する。

## 現状（調査結果）

- `verifier/` に `pair` の対応は無い。対応済みの `vector` 操作は `size/reserve/operator[]/begin/end/assign/emplace_back/push_back/erase`（`verifier/vector_stl.py` の `OPERATIONS`）で、要素は整数か入れ子vector。
- Lean 側の要素型は `Proofs.CppVectorOwnership.Element`（`integer ty | vector element`）、戻り値は `ResultKind`（`scalar | vector | unit`、`Proofs/CppNestedCall.lean`）。メモリモデルと証明の塔（Fenwick、MultiVec、Beats 等）が `Element` の場合分けに依存する。
- `std::sort` は契約公理 `Proofs.StlContracts.sort_comparisons_bound`（比較回数上限のみ）が登録済み。結果が整列済みの置換であるという契約は未登録。

## 設計案（要判断）

1. 要素型の拡張: `Element.record (fields : List Ty)`（`pair<A,B>` は2 field）。`Element` に依存する全補題の場合分けを増やすため影響が大きい。代案は変換器内の SoA 変換（2本の整数vectorに分け、戻り値は2本）。ただし C++ 側の `vector<pair>` と Lean 側の2本の対応を呼出し定理で明示する必要があり、`ResultKind` にも複数vector返却が要る。
2. 操作の追加: `emplace_back(a, b)`、`back().second` の読み書き/増分、`empty()`、範囲for＋構造化束縛 `auto &&[l, r]`、`v[i].first/second`、`pair` の `operator<`（辞書順）。
3. `std::sort(v.begin(), v.end())`: 契約公理を「結果は入力の置換で、辞書順に整列済み」に拡張して登録（信頼方針の契約区分）。時間は `O(n log n)` の比較回数上限（既存契約）。
4. 戻り値: `vector<pair<A,B>>` の値返しの callFuel 結果と、呼出し側へのexport定理。

## 最初の検証対象

`experiments/library/cpp/array/search_util.hpp` の `counts`（ソートなし、`pair<T,int>`）から始め、次に `interval_union_inclusive`（ソートの契約が要る）。いずれも公開側の2本vector版（`library/interval/interval_union.hpp`）を原本の形へ戻す。

## 判断が要る点

- 1 の案（`Element.record` か SoA）。
- ソート契約の範囲（置換＋整列済みを公理にする）。`docs/trust_policy.md` の契約区分で登録し、証明済みと区別する。

## 方式の決定と段階計画（2026-11-10、「続行」の指示を受けて）

方式: 同じ型の `pair<T,T>` は、既存の入れ子 vector（`Element.vector (integer T)`、行が2本）として Lean にモデル化する（`ResultKind`/`Element` の変更は不要）。行0が `first`、行1が `second`。型が違う `pair<T,int>`（`counts`、`element_count`）は、この方式では要素型が合わないため後回しにし、`Element` の拡張か別方式を後で決める。

実測した最初の失敗: `long long first_sum(const std::vector<std::pair<long long,long long>> &v)`（`v[i].first` の読み取りのみ）を `nested_ir.lower_source` に通すと `verifier/vector_stl.py` の `audit_vector_nodes` が `member call must resolve to a pinned std::vector instance` で拒否する。`std::pair<A,A>` の vector が、監査対象の `std::vector` インスタンスとして認められていない。

段階:
1. 監査（`vector_stl.py`）: `std::vector<std::pair<T,T>>` と `std::pair` の `first/second` メンバー参照を、同一翻訳単位の宣言IDで固定して認める。
2. IR（`nested_ir.py`）: `v[i].first/second` の読み、`emplace_back(a, b)`（2行へ追加）、`back()`、`empty()`、範囲for＋構造化束縛、`pair` の辞書順 `operator<`。
3. 並べ替え: `std::sort` を `pair` の vector（2行）へ。結果が置換かつ辞書順に整列済みであることのモデルと、比較回数の既存契約。
4. 呼出し定理: 2行の入出力（行の長さが等しいことを前提）。
5. `interval_union_inclusive` の原本形を公開し、`Proofs/IntervalUnion*.lean` の既存の証明を再利用して結果を証明する。

各段階はローカルコミットとして積み、`interval_union.hpp` が全体で完了した時点で、全件ゲートとチェックリストの更新を行う。
