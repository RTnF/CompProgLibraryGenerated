# monoid

`cp::MonoidMul<T>`、`cp::MonoidMax<T>`、`cp::MonoidMin<T>` は、1 つの `T` の値 `x` を持つ単位元つきの結合的演算である。セグメント木などで使う。元の `experiments/library/cpp/algebraic_structure/monoid.hpp` から作った。

元のソースからの変更:

- namespaceを`cp`へ移し、既定の`ll`は同じ型の`long long`で記述する。型パラメータTとpublic field xを保持する。
- 原本のhidden friend、`e()`への委譲構築、max/minの値コピーとADLを保持する。元で使えるraw値への暗黙変換と、コピー代入できないTも受け付ける。
- 以前の公開版のqualified `cp::op`も関数テンプレートとして残す。そのLL具体化内の型だけのwitnessでhidden friend本体を具体化する。runtime分岐や型の制約は加えない。
- `std::min/max`へのlocal using宣言は名前探索だけに使い、Clangが解決した呼出しを同じTUの宣言ID・primary・bodyで照合して変換する。対応構文と信頼境界は[標準操作の扱い](scalar_stl_contracts.md)を参照する。

2026-11-06に、公開版がhidden friendの暗黙変換を失い、Max/Minへコピー代入の要件を追加していた不具合を修正した。原本は変更していない。[修正記録](agent/fixes.md)を参照する。CPPの汎用APIを保つことと、任意Tの形式検証が完了することを区別し、Lean検証はLL具体化に限る。

前提と結果（`Proofs/MonoidCall.lean`、一般の入力について証明）:

- `*_default_correct`（既定コンストラクタ）: 引数なしで `1`、`-2^63`、`2^63 - 1` を返す。
- `*_e_correct`（静的メンバー `e()`）: 引数なしで `1`、`-2^63`、`2^63 - 1` を返す。
- `*_new_correct`（`long long` から作る）: 引数の値をそのまま返す。
- `mul_op_correct`: 前提は `x`, `y`, `x * y` が `long long` に収まること（符号付き桁あふれは契約の外）。結果は `x * y`。
- `max_op_correct` / `min_op_correct`: 全 `long long` の組に対して `if x < y then y else x`（`Max`）と `if y < x then y else x`（`Min`）。いずれも前提なし。
- 時間と追加領域は定数。opの生成本体は最大4個のスカラー局所値を持つ。呼出し準備と式の一時領域を含む上界は、Mulのopで`ScalarPost2 0 70`、Max/Minのopで`ScalarPost2 0 100`、既定構築とeで`ScalarPost2 0 70`。値構築は引数式のノード数に応じた仕事量と定数追加領域を含む。

hidden friendのLL生成モデルとqualified opの生成モデルが全NProgramで一致することも証明する。callerの元スカラーメモリを保持し、引数が同じセルを指す場合も含む。完全なC++ object/lifetimeを検証したとはしない。

定理に含めていないこと: 結合律や単位元の法則そのもの（long longのC++テストで確認する）、任意Tや浮動小数の形式検証。原本どおり`MonoidMax<T>::e()`は`numeric_limits<T>::min()`であり、浮動小数では最も負の値ではない。任意Tについてこの値がmaxの単位元になるとは主張しない。C++ のテストは `tests/monoid.cpp` で、`std::max`/`std::min` と `__builtin_mul_overflow` を独立した基準として、極値を含む全組と乱数の結合律を確認する。
