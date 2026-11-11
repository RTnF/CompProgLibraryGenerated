# cumulative_sum

`cp::CumulativeSum<T>`（1 次元）と `cp::CumulativeSum2D<T>`（2 次元）の累積和。元の `experiments/library/cpp/array/cumulative_sum.hpp` の 2 つのクラスそのもので、構築後は更新できない。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `CumulativeSum(v)` | `v` の累積和 | O(n) |
| `sum(a)` | `v[0, a)` の和（`0 <= a <= n`） | O(1) |
| `sum(a, b)` | `v[a, b)` の和（`0 <= a <= b <= n`） | O(1) |
| `CumulativeSum2D(v)` | `n × m` の配列 `v` の 2 次元累積和（`n, m >= 1`、全行の長さが `m`） | O(nm) |
| `sum(a, b)` | `[0, a) × [0, b)` の和（`0 <= a <= n`、`0 <= b <= m`） | O(1) |
| `sum(a1, b1, a2, b2)` | `[a1, a2) × [b1, b2)` の和 | O(1) |

前提は表のとおり（`assert` で確認する）。`T` が整数型なら途中の和が `T` に収まること。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/CumulativeSum.lean` を生成する。`Proofs/Cpp/CumulativeSum.lean` が、任意の可換加法モノイド `T`（区間の和は可換群）について次を証明する。

- `init_spec`: 1 次元の構築は `Rep`（`cs[k]` が先頭 `k` 個の和）を満たす。tick 数は `2 n + 2`。
- `sum_spec`、`sum_range_spec`: 前提のもとで結果は先頭 `a` 個の和、`v[a, b)` の和。オブジェクトは変わらない。1 tick。
- `init2_spec`: 2 次元の構築の後、全行 `i <= n` について `cs[i][j] = rect v i j`（`[0, i) × [0, j)` の和）。tick 数は `5 n + 3 n m + 1` 以下。3 段階のループ（行ごとの累積、列方向の加算）の不変条件は `RowPre`/`RowRect` で、1 反復は `rowpush_step`、`rowstart_step`、`colacc_step`。
- `sum2_spec`、`sum2_range_spec`: 結果は `rect v a b`、および 4 つの長方形の包除。

差分テスト（`tests/diff/cumulative_sum.py`、`T = long long` と `T = int`）と C++ のテスト（`tests/cumulative_sum.cpp`、`double` を含む）で翻訳と実装を確かめる。

## 元のソースからの変更

`std::` 修飾と名前空間のみ（2026-11-12 に元の形に戻した。それまでの公開版は検証の都合で書き換えていた）。
