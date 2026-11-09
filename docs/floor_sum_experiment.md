# floor_sum の仕様と検証

元の `experiments/library/cpp/number_theory/floor_sum.hpp` は保持する。共通変換器から生成した `Proofs/Generated/FloorSumUnsigned.lean` の全文を `tools/check_floor_sum_model.py` で照合する。部品名やハッシュで手書きモデルを選ばず、元の文・式・型から生成する。このモデルと全入力の関数全体の証明を公開検証に登録する。公開正本は `library/number_theory/floor_sum_unsigned.hpp`、API は `cp::floor_sum_unsigned` である。元実装と公開実装は共通変換器から同一の Lean モデルを生成する。signed 版の公開正本は `library/number_theory/floor_sum.hpp`、API は `cp::floor_sum` で、後述の明示したコンパイラ契約下で同じ生成経路を使う。

## 対象とする仕様

整数入力 `0 ≤ n < 2^32`、`1 ≤ m < 2^32`、`0 ≤ a,b < 2^64` に対して、`sum(i=0..n-1, floor((a*i+b)/m))` を `2^64` の剰余として返す仕様を証明対象にする。入力範囲を無制限に広げない。法0では C++ にゼロ除算があり、実行テストでは使わない。結果の積や累積は符号なしの剰余演算であり、自然数の無制限の積・和のままではモデルと一致しない。

元の unsigned 関数のコメントには入力上限がなく、signed 呼び出し側にだけ `n,m < 2^32` の条件がある。unsigned 関数でも条件を明示する必要がある。`n=4294967297,m=1,a=1,b=0` では、元の C++ と生成モデルの結果は `2147483648` であり、数学的な和の64 bit 剰余 `9223372039002259456` と一致しない。`n*(n-1)` が除算前にラップするためである。この入力を UBSan 付き C++ と生成 Lean で再現し、自然数の計算で差が生じることも Lean の `unrestricted_triangle_counterexample` で証明する。元ソースを変更せず、証明対象の前提条件として追跡する。

## 補助証明

`Proofs/FloorSumArithmetic.lean` は以下を扱う。

- `triangular_product_bound`: `n < 2^32` なら自然数の `n*(n-1) < 2^64`。
- `triangle_intermediate_exact`: unsigned の `n-1` と積のラップを明示しても、上記範囲では除算後の値が自然数の三角数に一致する。`n=0` の減算のラップも扱う。
- `normalized_y_bound`: `n,m < 2^32` と `a,b < m` なら `a*n+b < 2^64`。
- `normalized_transition`: 続行時には `0 < a < m`、次の `n=(a*n+b)/m` は現在の n 以下、次の b は現在の m 未満。
- `reduction_preserves_domain`: a,b を m の剰余へ正規化して続行する段階で、次の法と n は入力上限を維持し、法は正で厳密に減少する。
- `rounds`: 自然数での正規化と縮約だけを行う補助再帰。法を停止測度として Lean の停止検査を通す。法0は補助定義を全域にするため0回と定義する。
- `rounds_bound`: この補助再帰の反復回数は `m+1` 以下。
- `two_reductions_halve_modulus`: `0 < r < m` なら次の剰余 `m % r` は `m/2` 以下。
- `rounds_bound_pow` / `rounds_bound_log`: `m < 2^k` なら反復回数は `2*k` 以下、一般には `2*(log₂(m)+1)` 以下。
- `rounds_bound_input`: 対象の32 bit入力範囲で補助再帰は64回以下。
- `directSum` / `indexSum`: 自然数による直接の和の仕様と添字の和。各項は `(a*i+b)/m`。
- `term_normalization` / `directSum_normalization`: a,b の商を取り出すと、残りの和は a,b を剰余に置き換えた和に一致する。
- `double_indexSum` / `indexSum_eq_triangle` / `directSum_normalization_triangle`: 添字の和は `n*(n-1)/2`、したがって取り出す項は元の C++ の三角数と n の係数に一致する。
- `directSum_stop`: `a*n+b < m` なら残りの和は0。
- `directSum_normalization_modulo`: 商による取り出しの等式を `2^64` の剰余へ適用した形。
- `normalizedAns` / `normalization_preserves_accumulated_sum`: 自然数で正規化後の ans を定義し、ans と残りの和の合計の64 bit剰余が保存される。生成状態の ans 更新との対応は別の証明義務である。

これらは入力領域と停止測度を準備する定理である。後述の FloorSumRound で生成状態モデルの反復と while 全体へ接続した。補助再帰の停止だけを C++ の停止証明とはせず、実際の状態評価と十分な実行枠を別に証明する。関数全体の呼び出し・初期化・return の接続は未完了である。

## 縮約の和と数学側の反復

`Proofs/FloorSumReciprocity.lean` に有限和・格子点の補助証明を追加した。各商を、長方形内で `m*(j+1) ≤ a*i+b` を満たす格子点の数として数える。和の順序の交換と添字の反転を証明し、反転後の不等式が `a*(i+1) ≤ m*j+(a*n+b)%m` と一致することを示す。

`directSum_reciprocity` は `0 < m`、`0 < a`、`b < m` の条件で、次を証明する。

```text
directSum m a b n
  = directSum a m ((a*n+b)%m) ((a*n+b)/m)
```

`mathRun` は商を取り出す正規化、上記の縮約、64 bit 剰余の ans を使う数学側の反復で、法を測度として停止検査を通す。`mathRun_correct` は任意の自然数 n,a,b,ans と正の法 m について、返却値が `(ans + directSum m a b n) % 2^64` になることを証明する。`mathRun_result_bound` で返却値が64 bit範囲内にあることも確認する。

数学側では中間の自然数を無制限に扱うため、C++ の幅制約や入力上限を除いた全入力での等価性を主張しない。生成状態モデルの反復と while 全体への対応は後述の FloorSumRound で証明した。関数呼び出し全体への接続、signed版は未完了である。特に上限を外した反例では mathRun は数学的な和を返すが、元の C++ は異なる値を返す。

## 生成状態モデルとの接続

`Proofs/FloorSumState.lean` は、元の C++ から生成した定義の部分式・部分文を構造で取り出す。`guardA_shape`、`guardB_shape`、`yExpression_shape`、`normalizeA_shape`、`normalizeB_shape`、`declareY_shape` は生成した実際の定義に対する等式であり、別のアルゴリズムを検証対象として置かない。

型の範囲内の入力について、`a >= m` と `b >= m` の比較結果・式の仕事量3を証明した。n,m の32 bit上限と a,b の正規化条件の下で、`a*n+b` はラップせず、自然数の値と一致し、式の仕事量は5である。`frameState` に任意の呼び出し側メモリを含め、これらの式を状態評価へ接続した。呼び出し側のセルは評価で参照しない。

`normalizeA_skip`、`normalizeB_skip`、`normalized_branches_skip` は、a,b が m 未満の場合に生成した分岐が正常終了し、メモリと束縛を保ち、仕事量を各4・合計8だけ増やし、観測した追加領域を `max(元の peak,13)` にすることを証明する。`declareY_runs` は生成した y の宣言と後続の skip を実行し、y のセル・束縛を追加し、仕事量6・追加領域 `max(元の peak,17)` になることを扱う。これらの費用は共通モデルの抽象単位であり、実測時間や Lean のヒープ使用量ではない。

`stopCheck_breaks` と `stopCheck_continues` は、y を含む状態で停止条件が真・偽の場合の状態と制御を証明する。真の場合は仕事量5を追加して break を伝え、偽の場合は仕事量4を追加して続行する。どちらも評価時の追加領域は `max(元の peak,15)` であり、メモリと束縛を保つ。

`iteration_stop` は n,m の32 bit上限、a,b が m 未満、ans の64 bit範囲、`a*n+b < m` を前提に、実際の生成した反復本体全体が正常終了して break を返すことを証明する。任意の呼び出し側メモリで n,m,a,b,ans を保持し、局所 y のセルと束縛をスコープから破棄する。仕事量は19増え、追加領域は `max(元の peak,17)` になる。`outerLoop_stop` は同じ条件で生成した while まで接続し、仕事量21、同じ追加領域で正常終了し、break の印がループ外に残らないことを証明する。

`Proofs/FloorSumReduction.lean` は続行時の商・剰余による n,b の代入と m,a の交換を扱う。`quotient_shape`、`remainder_shape`、`afterStop_shape` で生成定義の部分式・後続文の形を照合する。`afterStop_runs` は64 bit範囲の全入力と正の m、任意の呼び出し側メモリについて、後続文が `n=y/m, m=a, a=m, b=y%m` に更新し、ans と y を保つことを証明する。この文の仕事量は14で、観測した追加領域は `max(元の peak,15)` になる。

`iteration_continue` は n,m の32 bit上限、正の m、a,b が m 未満、ans の64 bit範囲、`m ≤ a*n+b` の条件で、生成した反復本体全体が正常終了して続行することを証明する。y のセルと束縛を破棄し、呼び出し側メモリと ans を保持する。仕事量は32増え、追加領域は `max(元の peak,17)` になる。`outerLoop_continue` は while の条件評価も含め、仕事量34を加えた更新後の状態で、同じ生成した while を残りの実行枠で評価する等式を証明する。この等式は次の反復との接続であり、単独ではループ全体の終了を主張しない。

停止・続行の上記2経路で正規化済みの入力の1反復を扱った。続行後の a は元の m となるため、次の反復では正規化分岐が真になる。`Proofs/FloorSumNormalization.lean` では b の正規化を生成モデルへ接続した。`bAnsExpression_shape`、`bRemExpression_shape`、`yesB_shape` で実際の生成した式・真の分岐の形を照合する。乗算を64 bitへ丸めた後に ans を加算して丸める評価が、自然数の `(ans+n*(b/m))%2^64` と一致することを証明した。中間の積が64 bitを超える入力も対象に含む。

`normalizeB_runs` は n,m,a,b,ans が64 bit範囲、m が正の場合に、任意の呼び出し側メモリで実際の b の正規化分岐が正常終了し、b を `b%m`、ans を `bAns=(ans+n*(b/m))%2^64` に更新することを証明する。n,m,a と呼び出し側メモリは保持し、セル数・束縛も保つ。真の場合の仕事量は16、観測した追加領域は `max(元の peak,17)`。偽の場合は商が0なので ans と b を保ち、仕事量4・追加領域 `max(元の peak,13)` になる。`bAns_bound` により更新後の ans の64 bit範囲も維持する。

`Proofs/FloorSumANormalization.lean` では a の正規化を生成モデルへ接続した。三角数の式は生成した a の ans 更新式から取り出し、`triangleExpression_shape` で符号なしの減算・乗算と2による除算、その整数リテラルの変換も照合する。`triangle_eval` は n<2^32 の全入力で評価結果が自然数の `triangle(n)` に一致することを証明する。n=0では減算が2^64−1へラップするが積が0になる。n>0では除算前の積が64 bit範囲内であることを用いる。

`normalizeA_runs` は n<2^32、他の値が64 bit範囲、mが正の場合に、任意の呼び出し側メモリで a の正規化分岐を真・偽の両方で扱う。a は `a%m`、ans は `aAns=(ans+triangle(n)*(a/m))%2^64` となる。後半の乗算・加算のラップを含み、n,m,b と呼び出し側メモリ、セル数・束縛を保持する。真の場合の仕事量は24・追加領域は `max(元の peak,25)`、偽の場合は仕事量4・追加領域は `max(元の peak,13)` になる。

`normalizations_runs` は実際の a,b の正規化文を順に実行し、更新された ans が数学側の `normalizedAns` と一致することを証明する。どちらの条件分岐でも a,b は法の剰余、ans は64 bit範囲の値となる。2分岐合計の仕事量は40以下、追加領域は `max(元の peak,25)` 以下。各分岐とその連結に加え、後述の FloorSumRound で正規化から停止・縮約への連結と while 全体の結果・停止・計算量を証明した。関数全体への接続は後述の FloorSumCall で証明した。signed版は未完了である。

`tests/test_floor_sum_state.py` は元ソースから生成した定義でこの証明が通ることを確認し、元 C++ の `>=` を `>` にする2変更、y の `+` を `-` にする変更、停止の `<` を `<=` にする変更、break を ans の加算に置き換える変更、while の条件を false にする変更、n の商と b の剰余を入れ替える各変更、swap の対象を変える変更、b の正規化で乗算を加算にする変更、商を剰余にする変更、b の `%=` を `/=` にする変更、三角数の減算を加算にする変更、除数を3にする変更、aの商の乗算を2による除算より先にする変更、aの `%=` を `/=` にする変更から再生成したモデルでは証明が失敗することを確認する。

## 一般の反復と while 全体

`Proofs/FloorSumRound.lean` は元ソースの生成モデルについて、未正規化の a,b の正規化を停止・縮約の後続文へ連結する。`afterNormalization` は実際の生成した反復から取り出した部分文であり、`afterNormalization_shape` と既存の `iteration_shape` でその構造を照合する。

`iteration_stop_general` と `iteration_continue_general` は対象の n,m,a,b,ans と任意の呼び出し側メモリで、実際の1反復の更新結果、正常終了と break の有無、スコープの破棄を扱う。`outerLoop_stop_general` と `outerLoop_continue_general` は while の条件評価を含み、停止時の仕事量は53以下、続行時は66以下。追加領域は元の peak と25の最大値以下になる。

`loop_correct` は法についての強い帰納法で、生成した while の正常終了する実行枠が存在し、最終 ans が数学側の `mathRun` に一致することを証明する。続行時には次の法が正で厳密に減少し、n,m の32 bit範囲と a,b,ans の64 bit範囲が維持される。最終の n,m,a,b も型の範囲内で、呼び出し側のセルを保つ。元の仕事量を除く増分は `66*rounds` 以下、十分な実行枠は `13*rounds` 以下、追加領域は `max(元の peak,25)` 以下である。

`loop_uniform_correct` は同じ実際の while を実行枠832で評価し、最終 ans が `(元のans + directSum m a b n)%2^64` であることを証明する。仕事量の増分は4,224以下、さらに `132*(log₂(m)+1)` 以下。実行枠と費用は共通モデルの抽象単位であり、実測時間ではない。有限ケースのテストを停止証明に置き換えたのではなく、法の減少から全入力の実行枠の存在と上界を証明し、成功した実行の枠を増やしても結果が変わらない共通定理を用いて固定枠へ接続した。

## 関数全体の呼び出し

`Proofs/FloorSumCall.lean` は生成した関数本体から初期化と return の文を取り出し、その形と全体の構造を等式で照合する。`parameters_bound` と `initAns_runs` は、任意の呼び出し側メモリで4引数を値として束縛し、ans を0で初期化して実際の while の開始状態を作ることを証明する。呼び出し側のセルは読み書きしないため、呼び出し側のセルに型範囲の前提を課さない。

`floor_sum_unsigned_correct` は `0 ≤ n < 2^32`、`1 ≤ m < 2^32`、`0 ≤ a,b < 2^64` の全入力について、生成した関数呼び出しが実行枠836で正常終了し、直接の和 `directSum m a b n` の64 bit剰余を返すことを証明する。初期化、return、関数スコープの破棄と呼び出し側メモリの復元も含む。fault・exhausted ではなく finished に到達する等式と `floor_sum_unsigned_terminates` の成功する実行枠の存在により、停止と状態モデル上の未定義動作の不在を扱う。

引数束縛・初期化・返却を含む抽象仕事量は4,229以下、さらに `5+132*(log₂(m)+1)` 以下。追加領域は25以下で、入力値と呼び出し側メモリの大きさによらない。仕事量と領域は共通モデルの抽象単位であり、実測値ではない。公開ヘッダと登録は整備済みで、同じ生成モデルとこの全入力証明を検証対象とする。signed版は未完了である。初期値を1へ変える変更、返す変数をnへ変える変更、返す値に1を足す変更も、元 C++ から再生成したモデルで証明を拒否する回帰検査に加える。

## 検証

`tests/test_scalar_swap_ir.py` の従来の1,082ケースに加え、閉じた数式から期待値を求める7境界ケース、Fibonacci数を使う2入力、上記の範囲外反例を確認する。最大の有効 n,m、最大の a,b、法1、n=0 と n=1を含む。期待値の計算では Euclid 型のループを使わず、数十億の項を列挙する必要もない。元の C++ はテンプレート先行 include と UBSan で実行し、生成モデルの終了・結果・呼び出し側メモリを比較する。従来の1,082ケースでは直接の和の Lean 仕様と mathRun も Python の独立計算と比較する。境界ケースと Fibonacci 入力では mathRun の結果も比較し、上限を外した反例で元の C++ と数学側の反復が異なることを確認する。Fibonacci 入力はそれぞれ補助再帰の45回・46回の反復を通る。期待値には互いに素な a,m について、i と m-i の組の各商の和が a-1になることから得る閉じた式 `(m-1)*(a-1)/2` を使う。この2入力で生成モデルの仕事量・領域の上界も確認するが、有限ケースを全入力証明や実測性能とはしない。

```sh
python3 tools/check_floor_sum_model.py
python3 tests/test_scalar_swap_ir.py
python3 tests/test_floor_sum_state.py
python3 tools/check_public.py
```

## 公開部品と元実装の対応

公開版は `ull` を `std::uint64_t`、グローバル名を `cp::floor_sum_unsigned`、交換を `std::swap` にし、ヘッダ単体で必要な標準ヘッダを include する。関数を inline として複数翻訳単位から利用できるようにした。元の明示的なキャストは同型の代入なので省略する。整数幅・符号、式・制御と状態更新は変更せず、元実装と公開版の生成した Lean 定義の全文一致を各検証で確認する。関数名・ソースハッシュでアルゴリズムを選ぶ変換器は追加しない。

`tests/floor_sum_unsigned.cpp` は13種類のn、12種類のm、25種類ずつのa,bの全97,500組、400境界組、固定シードの10,000組を128 bit整数による直接和と比較する。最大入力で法1・係数0・係数が法と同じ場合の3組、および n=m,b=0 で `((a-1)*(m-1)+gcd(a,m)-1)/2` を用いる12組も確認する。この式は i と m-i の組を使う床関数の和から得られ、実装の Euclid 反復を参照しない。合計107,915組を通常実行と ASan/UBSan で確認する。元 C++ の比較は既存の `tests/test_scalar_swap_ir.py` で続ける。テンプレート先行 include、全部品同時 include、ヘッダだけの ZIP からのコンパイルも検査する。公式問題データや制限が未設定なので実測性能は示さない。

## signed 版の仕様準備と境界調査

元の `floor_sum` は n,m の32 bit上限を assert で確認し、負の a,b を safe_mod で非負にし、その補正を unsigned の ans から引いて unsigned 版を呼ぶ。最後の unsigned から signed への変換も扱う必要がある。`n=2,m=1,a=0,b=INT64_MAX` の数学的な和は18,446,744,073,709,551,614で signed 64 bitには入らず、この環境の GCC 13.3.0 / C++17 では -2 を返す。n,m の既存の前提だけで数学的な整数の和をそのまま返すとは主張できない。実装依存の変換の参考として [GCC の整数変換の説明](https://gcc.gnu.org/onlinedocs/gcc/Integers-implementation.html) を確認した。この文書の C の説明を C++17 の移植性保証とはせず、元 C++ の観測結果と区別する。

`Proofs/FloorSumSignedArithmetic.lean` の signedSum は整数の除算による直接の和を定義する。正の法で負の係数を含む全整数入力について、商の補正 `triangle(n)*(a/m)+n*(b/m)` と、a,b の非負剰余を使った既存の直接和へ分解することを証明した。`coefficient_correction` は `(a%m-a)/m=-(a/m)` を扱う。`signedDecode64` は数学的な整数を2^64の剰余へ丸めて signed 範囲に復号する仕様であり、値が signed 64 bit範囲内なら元の整数と一致し、常にその範囲内であることを証明する。上記の範囲外例の数学的な値と復号後 -2 も Lean で証明する。共通評価器の変換方針をこの補助仕様で置き換えてはいない。

`tests/imports/floor_sum_signed.cpp` は元 C++ を保持して74,610組を比較する。n=0..10、m=1..10、a,b=-12..12の68,750組、型の最小・最大を含む784組、固定シードの5,000組、最大 n と法1の閉形式49組、n=mと最大・Fibonacciの法で添字を組にする閉形式27組である。後の27組は `((a-1)*(m-1)+gcd(|a|,m)-1)/2` を128 bitで計算し、INT64_MINの絶対値を unsigned の剰余演算で作る。128 bitの独立した直接和を用い、負の除算は切り捨てる。期待値の signed 復号には範囲外の unsigned-to-signed キャストを使わない。通常実行と ASan/UBSan で、数学的な和が signed 範囲内の74,402組と範囲外の208組が一致した。これは有限ケースの確認で、元 signed 関数全体の証明ではない。

```sh
python3 tools/check_import_floor_sum_signed.py
```

元 signed 関数の2個の標準 assert は共通変換器で認識する。条件の短絡評価とリテラルの1ll<<32を扱い、偽の条件は明示的なチェック失敗とする。共通変換器には同じ AST に定義がある値引数の直接呼び出しを追加した。元ソースで floor_sum だけを抽出すると safe_mod が含まれず、その呼び出しを拒否する。`--direct-file` による全翻訳単位からの入力ファイル選択を追加し、元ヘッダの3関数を同じ AST で取得して[実験用の全体モデル](../experiments/verification/number/floor_sum_signed_model.lean)を生成・照合する。unsigned から signed への範囲外変換には引き続き対応が必要である。停止・安全性・結果・費用を生成した signed 関数全体へ接続する証明、公開候補の契約と登録は未完了で、台帳は Lean 証明済み・公開済みと扱わない。

`tests/test_direct_file_ast.py` は同じ AST での3関数の接続、既存 safe_mod・unsigned モデルとの一致、signed の小規模な非負の結果と元 C++ の UBSan 実行、assert の失敗を確認する。負の数学的結果 -2 と数学的な範囲外の正の結果を元 C++ が -2 に復号する2ケースについて、現状の検査付き signed 変換は fault になることも明示している。この checked モデルの成功ケースだけでは signed 全体の変換対応を完了と扱わない。下記の対象変換モデルで共通変換対応を追加し、台帳の lean_proved・published は false を保持する。


## 対象変換を使う signed 関数全体のモデル

既定の checked モデルを保持した上で、GCC 13.3.0 / x86_64 Linux / C++17 / LP64 の signed 変換契約を明示した[別の実験モデル](../experiments/verification/number/floor_sum_signed_gcc_model.lean)を追加した。共通変換器は対象と ABI を照合し、表現範囲外になり得る変換に targetCast を生成する。signed の算術そのものをラップさせない。safe_mod と unsigned の既存モデルは同じであり、最後の unsigned-to-signed 変換と負の係数を正規化した値の signed への格納を、同じ一般の変換規則で扱う。[変換の契約と証明](scalar_converter.md#対象コンパイラの-signed-整数変換)を参照する。

`tests/test_target_cast_ir.py` は n=0..4、m=1..5、a,b=-2..2の625組、signed 型の最小・最大値を含む60組、最大 n と法1の閉形式4組、計689組の直接和・閉形式を独立した整数で計算して signed 復号し、生成した関数全体と UBSan 付き元 C++ を比較する。以前の負の結果 -2 と範囲外の正の数学的な結果を -2 へ復号する例も成功する。assert の失敗も検査する。台帳の signed 宣言は対象変換契約下の共通変換対応を完了とするが、関数全体の結果・停止・安全性・費用・領域の全入力証明と公開は未完了である。

## signed 版の公開仕様と全入力証明

公開正本 `library/number_theory/floor_sum.hpp` は `safe_mod.hpp` と `floor_sum_unsigned.hpp` を include する。元のグローバル関数を cp 名前空間へ移し、ll/ull を std::int64_t/std::uint64_t に置き換え、inline を付ける。計算と assert は元のまま保持する。呼び出し先も同じ AST に含め、3関数すべてが元ヘッダと同一の `Proofs/Generated/FloorSumSigned.lean` を生成する。メタデータの公開宣言には include で見える2依存関数も含め、依存部品を登録する。

入力は `0 ≤ n < 2^32`、`0 < m < 2^32`、a,b は signed64 の全範囲。`signedSum m a b n` は数学的な床関数による総和である。`FloorSumSignedSpecification.call_correct` は任意の caller メモリについて、生成プログラムが燃料846で正常終了し、その総和を2^64の剰余から signed64 に復号した値を返すことを証明する。caller メモリを保持し、fault/exhausted に到達しない。`call_exact_if_representable` は総和が signed64 に入る場合の厳密な一致を示す。仕事量は4378以下かつ154+132*(log₂(m)+1)以下、追加領域は35以下で、時間O(log m)、追加領域O(1)となる。これは固定幅の抽象操作・セル数の費用であり、実測時間ではない。

範囲外の unsigned-to-signed 変換は C++17 の実装依存である。`signed_conversion = "gcc13.3-lp64-twos-complement"` をメタデータで明示し、GCC 13.3.0 / x86_64 Linux / C++17 / LP64 を検査する共通規則を適用する。checked が既定であり、プロファイルが変われば生成モデルの全文照合で拒否する。signed 算術のオーバーフローを許可する設定ではない。別コンパイラでの範囲外結果の移植性は主張しない。

`tests/floor_sum.cpp` は元実装の独立128 bit参照と同じ74,610入力（表現可能74,402、範囲外208）を公開APIへ適用する。通常実行、ASan/UBSan、テンプレート先行 include、全部品の同時 include を検査する。`tests/test_signed_floor_sum_proofs.py` は元ソースのモデル全文、91入力の数学的計算・生成モデル・C++ の一致、全入力証明の適用、callerの保持、燃料不足・不正入力の拒否、再生成した本体に対する4種類の改変拒否を扱う。公式問題・制限が未設定なので性能測定は未実施である。

## 元のソースからの変更

公開版（`library/number_theory/safe_mod.hpp`、`floor_sum_unsigned.hpp`、`floor_sum.hpp`）は、元の `experiments/library/cpp/number_theory/floor_sum.hpp` の3関数（`safe_mod`、`floor_sum_unsigned`、`floor_sum`）をそれぞれ1部品にしたもので、アルゴリズム・式・assert は元のままである。変更は次の3点だけで、いずれも元と同じ入力に同じ結果を返す。

- 名前空間 `cp` に入れ、`ll`/`ull` を `std::int64_t`/`std::uint64_t`（LP64 では同じ型）に書いた。`inline` を付けた。
- `floor_sum_unsigned` の `n = (ull)(y_max / m); b = (ull)(y_max % m);` の冗長な `(ull)` を外した（同じ型）。
- `floor_sum_unsigned` の事前条件 `n < 2^32`、`0 < m < 2^32` をヘッダーに明記した（元は signed 版のみ assert）。

元ヘッダーと公開実装は、共通変換器から同一の Lean モデルを生成することを `tools/check_floor_sum_model.py` と公開 bridge 検査（`FloorSumUnsigned`/`FloorSumSigned`/`SafeMod`）が毎回確認する。

