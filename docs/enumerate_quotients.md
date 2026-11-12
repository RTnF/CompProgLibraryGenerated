# enumerate_quotients

`cp::enumerate_quotients(std::uint64_t n)` は、正の整数 x に対する ⌊n/x⌋ の取りうる正の値を昇順に返す。`n = 0` では空の vector を返す。

- 前提: `1 <= n <= 2^64 - 2^32`（対象範囲。ヘッダにも明記）。実装は初期上限を `2^32` にしてあるので、範囲の外（`n = 0` を含む）でも動作し、`enumerate_quotients_spec` はこの範囲に限らず `uint64_t` の全値について証明されている（範囲の外を契約とはしない）。結果は約 2√n 個の `uint64_t` を持つので、呼び出し側のメモリが足りることが必要。
- 結果: 返る列は狭義単調増加で、その要素は ⌊n/x⌋ (x ≥ 1) が取る正の値と過不足なく一致する。
- 方法: `K(K+1) ≥ n` を満たす最小の `K ≥ 1` を二分探索（初期上限 2^32、反復は高々 32 回）で求め、`1..⌊n/K⌋` と `⌊n/i⌋` (i = K−1..1) を順に追加する。
- 時間: O(√n)（探索 O(log) と要素数に比例する 2 つのループ）。追加領域: 結果 vector の `⌊n/K⌋ + K − 1` 要素と局所変数のみ。
- 旧実装の上限 `4294967295` は n が 2^64 − 2^32 を超えると K を取り損ねる。対象範囲を `n <= 2^64 - 2^32` と定めた上で、上限を `4294967296` にして範囲の外でも誤らないようにしてある。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/EnumerateQuotients.lean` を生成する。`Proofs/Cpp/EnumerateQuotients.lean` の `enumerate_quotients_spec` は全ての `n : UInt64` について、返る列（の各要素の `toNat`）が狭義単調増加で、その要素が ⌊n/x⌋ (x ≥ 1) の正の値と過不足なく一致し、tick 数が `t0 + 42 + 6 * Nat.sqrt n` 以下であることを示す。

- 二分探索の不変条件は `ng < ok <= 2^32`、`n <= ok(ok+1)`、`ng = 0 ∨ ng(ng+1) < n` と、残りの反復回数 `bitWidth (ok - ng - 1)` による tick の上限。`k < 2^32` なので `k * (k + 1)` は 2^64 を法とせず数学的な積に一致する（`mid_toNat`）。終了時の性質が `KOK`。
- 2 つの追加ループは旧来の `Proofs/EnumerateQuotientsMath.lean` の `firstPart`（`firstPart_succ`）と `secondPart` の先頭部分（`secondPart_take_succ`）で書き、結果は `qlist n K` に一致する。`i + 1` が桁あふれしないことは `KOK` から出る（`p_small`）。
- 結果の性質は `qlist_spec`、要素数 `⌊n/K⌋ + K − 1 <= 2√n + 2` は `size_bound`。

差分テスト（`tests/diff/enumerate_quotients.py`）と C++ のテストで翻訳と実装を確かめる。

C++ のテストは `tests/enumerate_quotients.cpp` で、n ≤ 3000 の全件を総当たりの集合と比較し、大きな n（最大 2^42）では昇順・到達可能性・完全性を除算の恒等式で独立に確認する。

## 元のソースからの変更

元の `experiments/library/cpp/number_theory/enumerate_quotients.hpp` のグローバル関数 `vector<ull> enumerate_quotients(ull n)` に対し、公開版は名前空間 `cp` の `std::vector<std::uint64_t> cp::enumerate_quotients(std::uint64_t n)` である（`ull` と `uint64_t` は LP64 で同じ型）。変更は次のとおりで、いずれも元と同じ入力に同じ結果を返す。

- `(k * (k + 1) >= n ? ok : ng) = k;`（条件演算子の左辺値への代入）を `if / else` に書き換えた。
- 探索の局所変数 `ull k` をループ内の `const` 初期化付き変数にした（元はループ外の未初期化宣言で、毎回代入してから読む）。
- 結果の `vector` に `reserve(p + ok - 1)` を付けた（要素数は結果と同じ。値には影響しない）。
- 探索の初期上限を `4294967295` から `4294967296` にした。`n > 2^64 - 2^32` では元は `K` を取り損ねて誤った列を返す不具合で、`docs/agent/fixes.md` に記録済み。対象範囲 `1 <= n <= 2^64 - 2^32` では結果は元と一致する。

`tests/enumerate_quotients.cpp` の `check_against_original` が、元のヘッダー（`::enumerate_quotients`）と公開版を `n <= 3000` の全件、`n < 2^44` の乱択と境界値で比較し、結果が一致することを確認する。
