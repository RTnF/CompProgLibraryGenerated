# interval

`cp::Interval` は `long long` の半開区間 `[start, end)` で、空の区間かどうかの旗 `is_n` を持つ（3 フィールド `s`, `e`, `is_n`）。元は `experiments/library/cpp/interval/interval.hpp` の `Interval<T>`。

元のソースからの変更:

- クラステンプレートの型パラメータ `T` は元のまま残した（検証した具体化は `Interval<long long>`。`template struct Interval<long long>;` で明示的に具体化している）。アクセサ（`start`, `end`, `is_null`, `length`）は `const` にした。
- 既定の `operator<=>`（`= default`）は C++17 では書けないため、同じ順序（`(s, e, is_n)` の辞書順）を返す `==`, `!=`, `<`, `>`, `<=`, `>=` の 6 演算子を明示的に定義した。各演算子は `*this` を使わず、6 フィールドの比較だけの単一の `return` 式である（`bool` は `false < true`）。入出力演算子（`operator>>`, `operator<<`）は含めていない（標準入出力は証明の対象外とする方針、2026-10-12）。
- `intersection` の `std::max` / `std::min` は、`if` 文による比較に書き換えた。

変換器は 3 フィールドのスカラークラスを `verifier/class_split.py` でフィールドごとの関数に分ける。この部品のために、コンストラクタ本体の文（`assert`）と、`return` が複数ある（`if` の中の `return Interval();` と最後の `return Interval(ns, ne);`）クラスを返すメソッドに対応させた。生成される関数は次の 13 個である（アクセサ・`intersection` の 7 つと、比較演算子 6 つ）。

- `Interval_start`, `Interval_end`, `Interval_is_null`: 対応するフィールドを返す。
- `Interval_length`: `e - s`。前提は差が `long long` に収まること。
- `Interval_intersection_s`, `Interval_intersection_e`, `Interval_intersection_is_n`: `intersection` の結果の 3 フィールド。重ならないとき（`b.s >= e || s >= b.e`）は空の区間 `[0, 0)`（`is_n = true`）、重なるときは `[max(s, b.s), min(e, b.e))`。コンストラクタの `assert(start_ <= end_)` は検査として扱う。

- `Interval_eq`, `Interval_ne`, `Interval_lt`, `Interval_gt`, `Interval_le`, `Interval_ge`: 2 つの区間の 6 フィールドから比較結果（0/1）を返す。

証明する内容（`Proofs/IntervalCall.lean`、一般の入力について）:

- 補助: 参照引数 3 個と 6 個の呼び出しの準備（`prep_refs3`, `prep_refs6`）、`stage_assign`（比較して代入する分岐の一般形）、`inter_exec`（`intersection` の本体の実行）。
- `interval_start_correct`, `interval_end_correct`, `interval_is_null_correct`, `interval_length_correct`。
- `interval_intersection_s_correct`, `interval_intersection_e_correct`, `interval_intersection_is_n_correct`: 前提は、2 つの区間がどちらも `s <= e` を満たすこと（このとき `assert` は失敗しない）。結果は上記の値。
- `interval_cmp_correct`（単一の `return` 式を持つ 6 フィールド本体の共通の呼び出し定理）と `interval_eq_correct`, `interval_ne_correct`, `interval_lt_correct`, `interval_gt_correct`, `interval_le_correct`, `interval_ge_correct`: 任意の 2 区間（`s64` 2 個と `bool` 1 個ずつ）について、結果が `(s, e, is_n)` の辞書順の比較に等しい。前提は呼出し状態の整合のみで、仕事量は定数（≤ 140）、呼び出し側の状態は変化しない。
- 時間は定数、追加領域は局所変数 2 個。呼び出し側の状態は変化しない。

定理に含めていないこと: コンストラクタ `Interval(start, end)` 単独の検証（フィールドの代入だけで、`assert` は `intersection` の中で検査として証明している）、`assert` が失敗する入力（`s > e` の区間）での異常終了。C++ のテストは `tests/interval.cpp` で、値の組を総当たりして独立した参照（`max`/`min`）と比較する。
