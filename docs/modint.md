# modint

`cp::ModInt<m>` は法 `m` の剰余整数である。値は常に `[0, m)` に正規化して保持する。元の `experiments/library/cpp/modint/modint.hpp` から、クラス本体の主要な演算を取り出した。

元のソースからの変更（検証できる形にするために書き換えた）:

- 負の値を受けるコンストラクタを `long long` 1 本にし、`(v % m + m) % m` で正規化する。元の `v < 0 ? v % m + m : v % m` は、`v` が `m` の負の倍数のときに結果が `m` になり、不変条件 `x < m` を壊していた（例: `ModInt(-m)`）。`tests/modint.cpp` がこの場合を含む。
- `pow` の指数を `unsigned long long` にした。負の指数は `pow` に続けて逆元を取る形になる。
- 二項演算子 `+ - *` は、元のフレンド関数（`ModInt(a) += b`）と同じ結果を返す関数テンプレート（`template <unsigned int m> ModInt<m> operator+(ModInt<m> a, ModInt<m> b)`、本体は `ModInt<m> r = a; r += b; return r;`）にした。引数は元の `const ModInt &` でなく値渡し（スカラー 1 つなので同じ意味。値渡しにすると呼び出しが値の引数になり、証明は呼び出し側のセルの別名を気にしなくてよい）。二項演算子 `/` は `template <unsigned int m> ModInt<m> operator/(ModInt<m> a, const ModInt<m> &b) { a /= b; return a; }`（第 1 引数は値渡し、第 2 引数は元と同じ const 参照。`a /= b` のインライン展開で、複合代入 `/=` と同じプログラムになる）にした。入出力演算子、`operator()` を使うヘルパ（`fac`、`C`、`init`）、SFINAE の変換コンストラクタは対象外（台帳の違反一覧）。
- `operator++/--` の条件演算子を `if` に、複合代入を使わない形に書き換えた。

扱う構文: `verifier/class_lowering.py` が、スカラーのフィールドをちょうど 1 つ持つクラスを、そのフィールドの型の値として消去する。メソッドは第 1 引数を参照とする関数になり、コンストラクタは引数から値を返す関数になり、`this->x` と `*this` は消える。`verifier/inline_ast.py` はメソッド間の呼び出しをインライン展開し、複合代入を通常の代入に直す。明示的なインスタンス化（`template class ModInt<998244353u>;` と `ModInt<1000000007u>`）の AST から、各インスタンスの関数を取り出す。テンプレート引数 `m` は、生成される Lean では先頭の `Nat` 引数として一般の `m` で表され、各インスタンスは `«ModInt_X» 998244353` のように適用した形になる。生成器は、各インスタンスが一般形に `m` の値を代入したものと一致することを確認する。

証明する内容（`Proofs/ModIntComponent.lean` が定理を再掲する。本体は `Proofs/ModIntCall.lean` と `Proofs/ModIntOps.lean`）: 前提を満たす全入力について、呼び出しの結果、停止、未定義動作の不在、呼び出し側の対象セルの更新、仕事量と追加領域の上界。

- `ModInt_add_assign`: `2 <= m <= 2^31`、`x, y < m`。結果と更新後の値は `(x + y) % m`。`x += x` のように 2 つの参照が同じセルを指す場合も含む。
- `ModInt_sub_assign`: 同じ前提。結果は `(x + m - y) % m`。
- `ModInt_mul_assign`: `2 <= m < 2^32`。結果は `x * y % m`（途中の 64 bit の積は桁あふれしない）。
- `ModInt_increment` / `ModInt_decrement`: `(x + 1) % m` と `(x + m - 1) % m`。
- `ModInt_sub_unary`: 単項の負号。`x = 0` なら 0、そうでなければ `m - x`。
- `ModInt_eq` / `ModInt_ne`、`ModInt_get`、`ModInt_new0`（既定コンストラクタ）。
- `ModInt_new1`: `long long v` から `v % m`（`Int.emod`、常に `[0, m)`）。`long long` の全値について。
- `ModInt_inv`: 前提 `x != 0`（`assert`、検査として扱う）。結果は `x ^ (m - 2) % m`。`Proofs/Fermat.lean` の `IsPrime` と `fermat` により、`m` が素数なら `x * 結果 % m = 1`（`inv_correct_prime`）。`m` が素数でない場合の結果は `x ^ (m - 2) % m` のままで、逆元とは限らない。
- `ModInt_div_assign`（`x /= y`、元の `*this *= y.inv()`。`ModInt z = y.inv(); *this *= z;` と書き、`inv` と `*=` はインライン展開される）: 前提 `2 <= m < 2^32`、`x, y < m`、`y != 0`（`inv` の `assert`）。結果と更新後の `x` は `x * (y ^ (m - 2) % m) % m`。`m` が素数なら、`div_value_prime` により、その値に `y` を掛けて `m` で割った余りは `x` に戻る（逆元との積）。`inv` の本体を 1 つずらした番号で再利用するため、`Proofs/ShiftState.lean` の「変数番号を 1 つずらした実行が元の実行の写しになる」補題 `pexec_sh` と、連続の末尾に続きを付ける補題 `pexec_snoc` を使った。
- 二項演算子 `operator+`・`operator-`・`operator*`（`Proofs/ModIntOps.lean` の `operator_add_correct` など。2 つの法 `998244353`・`1000000007` の具体化は `Proofs/ModIntOps.lean` の `operator_add_ModInt_998244353U_correct` など）: `2 <= m <= 2^31`、両方の引数が `[0, m)` のとき、結果は `(x + y) % m`、`(x + m - y) % m`、`x * y % m`。呼び出し側のオブジェクトを変えない（引数は値渡し）。仕事量は引数の式の節の数 + 80 以下。
- 二項演算子 `operator/`（`Proofs/ModIntOps.lean` の `operator_div_correct` と、2 つの法の `operator_div_ModInt_998244353U_correct` など）: `2 <= m < 2^32`、`x, y < m`、`y != 0`（`inv` の `assert`）のとき、結果は `x * (y ^ (m - 2) % m) % m`（`m` が素数なら商。`ModInt_div_assign` と同じ式）。`a` は値渡し、`b` は呼び出し側のセルを指す const 参照で、呼び出し側のセルは変わらない。
- `ModInt_pow`: `x ^ n % m`。`n` は `unsigned long long` の全値で、ループは最大 64 回、仕事量は 6000 以下。

定理は一般の `m` で証明していて、`mint = ModInt<998244353>` と `mint17 = ModInt<1000000007>` の生成されたプログラムは、その `m` を代入したものとして同一である。

定理に含めていないこと: `m > 2^31` での `+=` と `-=`（32 bit の途中値が桁あふれするため、前提で除外している）、登録した 2 つ以外の `m` の AST との一致、呼び出し側のオブジェクトの内容が変化しないこと（個数、使用領域、仕事量、スコープは保存を証明している）。C++ のテストは `tests/modint.cpp` で、128 bit の剰余と別実装の累乗を独立した基準にして、負の倍数や境界値、別名の演算（`c += c`）、乱数を照合する。


2026-11-08: 変換器が未使用の戻り値も評価するようになった変更に合わせ、生成モデル11定義と一般証明を更新した。`return *this` などのscalar erasure後のret captureをIRの宣言セルとして保持する（C++へ新しいcopy constructorを挿入する変更ではない）。加減乗では結果を捕捉した追加セルもcalleeの全状態に含め、除算では入れ子のret captureを1回/2回の共通補題で扱う。callerに返す値と元メモリの仕様は維持する。

累乗ループ内の追加セルは元のblock scope終了時に除去される。任意prefixのtyped readが追加セルに影響されないこと、capture回数nに対する状態・仕事量2*n+2・need上界、loopからの退役を一般証明する。既存の数値上界（ループ70work、全体の既存上界など）には余裕があるため、追加評価を含めた証明でも値を増やしていない。C++ヘッダーと前提条件・結果の仕様は変更しない。最新の独立kernel/bridge/全件検査は[引き継ぎ](agent/handoff.md)を参照。

2026-11-09: 旧ソースを別領域で再構築し、旧監査記録の2481宣言を再現した。公開34定理の型は、本体形状を示す等式1件を除いて同一である。生成モデル11定義・累乗補助2定義・本体等式1件の変更と、ret capture用5定義の追加だけを監査記録へ反映した。内部補題の正確なcallee状態には追加セルを含めるが、呼出し結果・入力条件・時間と領域の既存数値上界は維持している。
