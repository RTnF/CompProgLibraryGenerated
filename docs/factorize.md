# factorize

`cp::factorize(n)` は 64 bit 整数 `n` の素因数分解（ポラードのロー法）で、`experiments/library/cpp/number_theory/factorize.hpp` の `factorize`・`factorize_count`・`divisors` に対応する。依存部品は `gcd_u64` と `is_prime`。

| 関数 | 内容 | 前提 |
| --- | --- | --- |
| `factorize(n)` | `n` の素因数を重複込みで昇順に並べた列 | `n >= 1` |
| `factorize_count(n)` | 相異なる素因数 `p` と指数 `e` の組 `(p, e)` を `p` の昇順に並べた列 | `n >= 1` |
| `divisors(n)` | `n` の約数の昇順の列 | `n >= 1` |
| `factorize_unsorted(n)` | 元の `in::factorize`（並べ替える前の素因数の列） | `n >= 1` |
| `factorize_rho(m, c, n)` | `x ↦ x^2 + c (mod n)` の歩みとフロイドの周期検出で `m` の約数 `1 < d < m` を探す。見つからずに歩みが閉じたら `0` | `n >= 3`、`m >= 2` |
| `factorize_f(x, c, n)` | `(x^2 + c) mod n`（128 bit の積） | `n >= 1` |
| `divisors_dfs(factor, div, f, i)` | 組 `i, i + 1, …` の指数を選ぶ積 `f * p_i^{j_i} * …` を `div` の末尾へ追加する（元の再帰ラムダ） | `0 <= i < factor.size()`、各指数 `0 < e < 64`、各 `p >= 1`、`f >= 1`、`f * Π_{l >= i} p_l^{e_l} < 2^64` |

- 素因数分解は、2 で割り切れる間割り、残りが素数（`is_prime`）ならそれを加え、そうでなければ `c = 1, 2, 3` の順にロー法で約数 `r` を探して `r` と `n / r` を再帰的に分解する。3 回とも失敗したら奇数による試し割りに切り替える。
- `n = 1` では `factorize` と `factorize_count` は空列、`divisors` は `{1}` を返す。
- 計算量: どの `n` でも `O(n)` を証明した（tick 数は `Kc * n` 以下、`Kc = 162230`）。ロー法の歩みは最悪で `n` 歩かかりうるので、期待計算量 `O(n^{1/4})` は証明していない。`divisors` は `O(n)` を証明した（約数の個数を `D` として、実際は `O(D log D)` と分解の時間）。追加領域は結果の長さと再帰の深さ（`O(log n)`）。

元のソースからの変更:
- ラムダ `f`・`rho`・再帰ラムダ `dfs` を関数 `factorize_f`・`factorize_rho`・`divisors_dfs` にし、`in::factorize` を `factorize_unsorted` にした。`rho` が捕捉していた `n` は引数として渡す（呼び出しは `factorize_rho(n, i, n)`）。`dfs` が捕捉していた `factor`・`div` は引数で渡し、`num_factor` は `factor.size()` から求める。
- `std::gcd` を `gcd_u64`（ユークリッドの互除法、計算量を証明済み）に、`factor.insert(factor.end(), …)` を `push_back` のループに、`emplace_back(2)` を `push_back(2)` に、`return {1}` を `std::vector<std::uint64_t>(1, 1)` に書き換えた（変換器の対応範囲に合わせるため。結果は同じ）。
- `factorize_count` は `array/search_util.hpp` の `counts` を呼ばず、同じ規則（空または末尾の値と異なれば `(v, 1)` を追加、同じなら個数を 1 増やす）をその場に書いた。依存部品のテンプレート `counts` を変換器が扱えないため。
- 試し割りの条件 `i * i <= n` を `i <= n / i` にした。`i * i` が折り返さない限り同じ真偽になる。元の実装で折り返しは起こらない。試し割りに入るのは合成数の `n` だけで、合成数は `2^32` 未満の因数を持ち、`i` がそこに達すると `n` が割られて小さくなるため、`i` が `2^32` を超える前にループが終わる。証明で折り返しを扱わずに済ませるための書き換えである。
- 型は元の `ull`（`small_template.hpp` の `std::uint64_t`）に合わせて `std::uint64_t` とし、名前空間 `cp` に置いた。
- 元と同じ入力に同じ結果を返すことを、`tests/factorize.cpp` で元の実装の写しと照合して確認している（`n = 1..3000` の総当たり、乱数、大きな半素数と素数冪）。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/Factorize.lean` を生成する（自己再帰は燃料つきの `_rec`）。証明は `Proofs/Cpp/Factorize.lean`、数学側は `Proofs/Math/FactorizeMath.lean`。
- `rho_spec`: 返り値は `0` か `m` の約数 `1 < d < m`。tick 数は `2 + 136 n` 以下（停止を含む）。歩み `a_i = F^[i] 2` の値は `n` 未満なので、鳩の巣原理で `1 <= i <= n` に `a_i = a_{2i}` がある（`floyd_meets`）。ループの状態 `(x, y)` が歩みの何番目かを `firstIdx` で測り、測度を `n - firstIdx` とした。`a_i = a_{2i}` なら `gcd(0, m) = m ≠ 1` なのでそこで止まる。
- `unsorted_rec_spec`: 燃料に関する帰納法。積が `n`、各要素が 2 以上、`MRWitnessSet` のもとで各要素が素数、tick 数が `Kc * n` 以下。再帰する約数 `r` と `n / r` は奇数の真の約数なので 3 以上で、深さは `log_3 n` 以下になる。試し割りの不変条件は「`[2, i)` に `n` の約数がない」（`NoSmall`）。割った `i` は素数で、最後に残る `n > 1` は `n < i * i` から素数になる。費用は `C0 + C·n + Kc·(r + n/r) <= Kc·n`（`cost_rec`、`r, n/r >= 3`）。
- `factorize_spec`: 上に加えて昇順（`std::sort` の契約）。`factorize_count_spec`: 結果は昇順の素因数列の連長圧縮（`Proofs/Cpp/Lib/Rle.lean` の `rle`）。
- `dfs_spec`: 結果は `div` に純粋関数 `gen`（`f * p_i^{j_i} * …` を辞書式順に並べた列）を連結したもの。`p` の最後の更新 `p_i^{e_i+1}` は折り返してよい（使われない）。
- `divisors_spec`: 各要素は `n` を割り切り、列は昇順。`MRWitnessSet` のもとでは `n` のすべての約数がちょうど 1 回ずつ現れる（`gen_complete`・`gen_nodup`。素因数分解の一意性を、素数 `p ∤ m` に対する `d ∣ p^e m ⇒ d = p^j d'`、`d' ∣ m` で示す）。
- 素数であること（と約数の完全性）は `is_prime` と同じ前提 `MRWitnessSet` のもとで示す（`docs/is_prime.md`）。前提なしでも、積が `n` であることと、約数がすべて `n` を割り切ることは成り立つ。
