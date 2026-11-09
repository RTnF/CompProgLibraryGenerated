# group

`cp::GroupSum<T>`、`cp::GroupMul<T>` は 1 つの値 `_x` を持つ群（加法と乗法）、`cp::GroupAffine<T>` は 2 つの値 `_a`, `_b` を持つアフィン写像 `y = a * x + b` の群である。元の `experiments/library/cpp/algebraic_structure/group.hpp` と同じ 3 つのクラスを 1 つのヘッダーにまとめている（以前は `GroupAffine` を `affine` として別の部品にしていたが、元のヘッダーに合わせて統合した）。それぞれ構成子、単位元（既定構成子と静的メンバー `e()`）、`op(a, b)`、`inv()` を持ち、`GroupSum`/`GroupMul` は `x()`、`GroupAffine` は `a()`、`b()`、`apply(x)` を持つ。`GroupAffine` の `op(p, q)` は p を先に適用する合成で、`op(p, q).apply(x) == q.apply(p.apply(x))`。

元のソースからの変更（2026-11-05に元の暗黙変換と構築形式を復元。正本追加後の全件検証は進行中）:

- クラステンプレートの型パラメータ `T` を保ち、検証する具体化は整数型の `long long` と `int` とする（2026-11-09に `int` を追加。`double` など浮動小数の `T` は浮動小数の検証基盤が整うまで未検証）。元の非テンプレートhidden friendを残し、`op(GroupSum<long long>(2), 3LL)` と逆順、`GroupMul`の混在引数、Affineへ変換できる型も受け付ける。既存のqualified `cp::op`用の関数テンプレートも維持する。
- namespace関数のLL具体化に、型宣言とstatic_assertだけのwitnessを置く。関数ポインタを非型テンプレート引数にして元のfriend本文もClangで具体化し、共通変換器で検証対象へ取り込む。他の `T` では分岐を破棄するため、新しい型の制約や実行時の操作を加えない。LLのfriend4モデルはnamespace版とプログラム全体が一致し、既存の一般定理をそのまま適用できる。
- 3クラスの既定構成子を元と同じ `e()` への委譲へ戻し、暗黙returnとAffineの波括弧returnも戻した。汎用型で観測できたコピー回数と構築順の差を解消する。`tests/group.cpp`で暗黙変換・変換proxy・local型を検査し、`tests/test_scalar_class_delegation.py`で原本と公開版を同じ条件でコンパイルしてAffineの構築event列を比較する。
- `GroupAffine::apply` は元と同じ `const T &x` で受け、引数のコピーを増やさない。
- `GroupMul` のコンストラクタの `assert(x != 0)` は残した（検査として扱う）。変換器は初期化式と本体の状態変更の順序を検査する。単一fieldで保存が必要な場合は初期値を局所fieldへ保持してから本体を実行する。詳しい対応範囲は `docs/scalar_converter.md` を参照する。

旧`library3`も対応元に含めた以前の統合では、異なるAPIを持つ旧Group/Mappingを同一のクラス群として扱っていた。public field・異型Uの値渡しapply・ide/compose・逆元の演算の定義は未復元であり、この縮小は未解消の規則違反として台帳に残す。末尾の「library3旧版との未解消差」を参照する。

`GroupMul::inv()` は元と同じ `return 1 / _x`（群への暗黙変換）で、`long long` では整数除算である。元のコードは浮動小数の `T` を想定しており、`long long` では `_x` が 1 または -1 のときだけ真の逆元になる。それ以外の値では `1 / _x` が 0 になり、コンストラクタの `assert` が失敗する。定理は成功する場合（`_x = 1` または `-1`）だけを扱う。`GroupAffine::inv()` も同様に `(1 / _a, -_b / _a)`（C++ の切り捨て除算）で、`_a` が 1 または -1 のときだけ真の逆元になる。

証明する内容（`Proofs/GroupCall.lean`、一般の入力について。すべて `T = long long`）:

- `groupsum_new_correct` / `groupmul_new_correct`（値から作る）: 値をそのまま返す。`GroupMul` は値が 0 でないこと（`assert`）が前提。
- `groupsum_default_correct` / `groupmul_default_correct`: 0 と 1 を返す。`groupsum_e_correct` / `groupmul_e_correct`（静的メンバー `e()`）: 同じく 0 と 1。
- `groupsum_x_correct` / `groupmul_x_correct`（`x()`）: `_x` を返す。
- `groupsum_op_correct`: 前提は `x + y` が `long long` に収まること。結果は `x + y`。
- `groupmul_op_correct`: 前提は `x * y` が収まり、0 でないこと（`assert`）。結果は `x * y`。
- `groupsum_inv_correct`: 前提は `-x` が収まること（`x != LLONG_MIN`）。結果は `-x`。
- `groupmul_inv_correct`: 前提は `x = 1` または `x = -1`。結果は `x`。
- `GroupAffine`: `affine_a_correct` / `affine_b_correct`（`a()`、`b()`）、`affine_e_a_correct` / `affine_e_b_correct`（`e()` の 2 つの値 1 と 0）、`affine_apply_correct`（前提は `a * x` と `a * x + b` が収まること。結果は `a * x + b`）、`affine_compose_a_correct`（`op` の `a`、前提は `p.a * q.a` が収まること）、`affine_compose_b_correct`（`op` の `b`、前提は `p.b * q.a` と `p.b * q.a + q.b` が収まること。結果は `p.b * q.a + q.b`）、`affine_inv_a_correct`（`1 / a`、前提は `a != 0`）、`affine_inv_b_correct`（`-b / a`、前提は `a != 0`、`-b` と商が収まること）。
- `affine_new_a_correct` / `affine_new_b_correct`は値からの構築の2fieldを、`affine_default_a_correct` / `affine_default_b_correct`は既定構築の1/0を証明する。引数の型に合う純粋式とその評価値、整数範囲、callerの有効性を前提に、結果・終了・元メモリとframeの保持・定数のwork/peak上界を扱う。
- 変換器は2field以上のスカラークラスをfieldごとの関数へ分ける。新しい委譲構築経路では値/既定構成子も生成する。現在扱う委譲はtrivial copy/move/dtor、空body、引数なし静的factoryの単一return、全fieldが整数literalと許可されたcastからなるものに限る。他fieldの副作用や失敗を落とさないよう、算術・副作用・独自copy/dtor等を拒否する。任意のC++ object/lifetime ASTの検証ではなく、LL具体化のfield投影についての定理である。
- 時間は定数、追加領域は局所変数 3 個以下。呼び出し側の状態は変化しない（個数、使用領域、仕事量、スコープの保存を証明している）。

定理に含めていないこと: 群の法則（結合律、逆元の法則）そのもの（C++ のテストで確認している）、`assert` が失敗する入力での異常終了、符号付きオーバーフローが起きる入力の挙動（契約の対象外）、`T` が `long long` 以外のときの検証。C++ のテストは `tests/group.cpp` で、`__builtin_add_overflow`/`__builtin_mul_overflow` を独立した基準として、極値を含む全組と、アフィン写像の合成・適用・逆元（`T = int`、`double` の具体化も含む）を確認する。


## applyの元の参照APIへの復元（2026-10-15）

公開側に残っていた値渡しのapplyを元のconst T&へ戻した。単なる整数の出力一致だけでは、コピーが観測できるTで元と同じ挙動を保証できないためである。型T、構成子、他の演算、戻り値は維持する。

共通生成モデルはa/b/xをすべて読み取り専用参照として受ける。affine_apply_correctも第三引数を既存callerセルへの参照に変更し、a*xとa*x+bがlong longの範囲内という元の算術条件を保ったまま結果・停止・状態保存・定数のwork/追加領域上界を証明する。参照が同じセルを指す場合も許し、入力値をコピーするcalleeセルは作らない。モデルの一時引数はcaller側でセルとして用意した状態で扱う。

C++テストはメンバー関数の型のstatic_assertと、コピー回数を数える型で引数コピーが0回であることを確認する。Leanテストは一般定理の適用、3参照の読み取り専用binding、receiverとの別名/全引数の別名/順序変更、callerメモリの保存を確認する。これらのC++型テストを、組込み整数以外のTのLean証明済みとはしない。

## 元API復元の検証経路（2026-11-05）

生成モデルは29件。既存の2既定構築モデルは、元の委譲で実行する一時セルとassertを含む命令列へ変わるため、前提・結果・既存のScalarPost2 0 70上界を保って証明を更新した。他の既存19モデルとfriend4モデルは既存プログラムと一致し、新しいAffine既定構築2モデルもe()のfieldモデルと一致する。Affineの値構築では共通の2値引数の準備補題を使う。旧53定理の前提・結論は維持する。

共有回帰は、compile-time宣言の削除後も通常ifを残すこと、VLA・runtime init/body・false assert・属性の拒否、委譲構築のcleanup/独自copy/dtor拒否を検査する。別名・namespace・定数変更・3field・混在整数幅の生成例、未使用fieldのゼロ除算を含む不正なfactory、再帰factoryも扱う。生成した構成子の具体例と一般の構成子定理・friendプログラム一致を、固定nanodaの通常stack/2threadsでも検査する。全件ゲートの最新結果はhandoffを参照する。

## library3旧版との未解消差

ここで復元したAPIは `experiments/library/cpp/algebraic_structure/group.hpp` のもの。`library3` のGroupはpublic field `x/a/b` を持ち、MappingのAffineはpublic field `a/b`、`ide/compose`、値渡しの `template<class U> U apply(U)` を持つ。現行のgetterと `const T& apply` だけで同じAPIとはしない。異型引数0.5での適用結果とGroupSum<double>の逆元の0の符号にも差がある。詳細と実比較は `docs/experiments_findings.md` を参照する。旧版を含む全体の統合・検証は継続中。


## 整数型の具体化セット（2026-11-09）

`GroupSum`/`GroupMul`/`GroupAffine` の `int` 具体化（`template class ...<int>` と `op` の明示具体化）を追加した。生成モデルは `long long` 版と型幅（32 bit）と、`return 0` のような整数リテラルが `long long` では `cast` を挟み `int` では挟まない点だけが異なる。`Proofs/GroupCall.lean` の名前空間 `Proofs.GroupCallInt` に、`long long` 版と同じ全定理（`x`/`e`/既定構築/値構築/`op`/`inv`/`apply`/hidden friend の一致）を `i32` で証明した。前提は各演算の結果が `int` に収まること（`GroupMul::inv` は `x = 1, -1` のとき）で、`long long` 版と同じ。`tests/group.cpp` の `check_int_instances` が `int` を直接計算と照合する。
