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
