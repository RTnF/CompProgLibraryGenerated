# group

`cp::GroupSum<T>`、`cp::GroupMul<T>` は 1 つの値 `_x` を持つ群（加法と乗法）、`cp::GroupAffine<T>` は 2 つの値 `_a`, `_b` を持つアフィン写像 `y = a * x + b` の群である。元の `experiments/library/cpp/algebraic_structure/group.hpp` と同じ 3 つのクラスを 1 つのヘッダーにまとめている（以前は `GroupAffine` を `affine` として別の部品にしていたが、元のヘッダーに合わせて統合した）。それぞれ構成子、単位元（既定構成子と静的メンバー `e()`）、`op(a, b)`、`inv()` を持ち、`GroupSum`/`GroupMul` は `x()`、`GroupAffine` は `a()`、`b()`、`apply(x)` を持つ。`GroupAffine` の `op(p, q)` は p を先に適用する合成で、`op(p, q).apply(x) == q.apply(p.apply(x))`。

元のソースからの変更（検証できる形にするために書き換えた。機能は減らしていない）:

- クラステンプレート `template <class T = ll>` の型パラメータ `T` は元のまま残した。検証した具体化は `T = long long`（`template class GroupSum<long long>;` などで明示的に具体化している）。
- `op` は、フレンド関数ではなく、そのクラスのインスタンスのフレンドである関数テンプレートにした（クラステンプレートの中で定義したフレンド関数は使われるまで具体化されず、具体化した型についての検証ができないため）。実引数依存の名前探索で見つかるので、`op(a, b)` の呼び出しは元のままである。
- 既定構成子は、元の `e()` への委譲ではなく、単位元を直接書く（`e()` も元のまま持つ）。戻り値は明示的な構成子の呼び出しで書く。`GroupAffine::apply` は元と同じ `const T &x` で受け、引数のコピーを増やさない。
- `GroupMul` のコンストラクタの `assert(x != 0)` は残した（検査として扱う）。変換器にコンストラクタ本体の文を許す拡張を入れた（本体の文は戻り値の計算の前に実行される）。

`GroupMul::inv()` は `GroupMul(1 / _x)` で、`long long` では整数除算である。元のコードは浮動小数の `T` を想定しており、`long long` では `_x` が 1 または -1 のときだけ真の逆元になる。それ以外の値では `1 / _x` が 0 になり、コンストラクタの `assert` が失敗する。定理は成功する場合（`_x = 1` または `-1`）だけを扱う。`GroupAffine::inv()` も同様に `(1 / _a, -_b / _a)`（C++ の切り捨て除算）で、`_a` が 1 または -1 のときだけ真の逆元になる。

証明する内容（`Proofs/GroupCall.lean`、一般の入力について。すべて `T = long long`）:

- `groupsum_new_correct` / `groupmul_new_correct`（値から作る）: 値をそのまま返す。`GroupMul` は値が 0 でないこと（`assert`）が前提。
- `groupsum_default_correct` / `groupmul_default_correct`: 0 と 1 を返す。`groupsum_e_correct` / `groupmul_e_correct`（静的メンバー `e()`）: 同じく 0 と 1。
- `groupsum_x_correct` / `groupmul_x_correct`（`x()`）: `_x` を返す。
- `groupsum_op_correct`: 前提は `x + y` が `long long` に収まること。結果は `x + y`。
- `groupmul_op_correct`: 前提は `x * y` が収まり、0 でないこと（`assert`）。結果は `x * y`。
- `groupsum_inv_correct`: 前提は `-x` が収まること（`x != LLONG_MIN`）。結果は `-x`。
- `groupmul_inv_correct`: 前提は `x = 1` または `x = -1`。結果は `x`。
- `GroupAffine`: `affine_a_correct` / `affine_b_correct`（`a()`、`b()`）、`affine_e_a_correct` / `affine_e_b_correct`（`e()` の 2 つの値 1 と 0）、`affine_apply_correct`（前提は `a * x` と `a * x + b` が収まること。結果は `a * x + b`）、`affine_compose_a_correct`（`op` の `a`、前提は `p.a * q.a` が収まること）、`affine_compose_b_correct`（`op` の `b`、前提は `p.b * q.a` と `p.b * q.a + q.b` が収まること。結果は `p.b * q.a + q.b`）、`affine_inv_a_correct`（`1 / a`、前提は `a != 0`）、`affine_inv_b_correct`（`-b / a`、前提は `a != 0`、`-b` と商が収まること）。
- 変換器は 2 フィールド以上のスカラークラスを `verifier/class_split.py` でフィールドごとの関数に分ける。コンストラクタは各フィールドへの代入だけなので関数にならない。
- 時間は定数、追加領域は局所変数 3 個以下。呼び出し側の状態は変化しない（個数、使用領域、仕事量、スコープの保存を証明している）。

定理に含めていないこと: 群の法則（結合律、逆元の法則）そのもの（C++ のテストで確認している）、`assert` が失敗する入力での異常終了、符号付きオーバーフローが起きる入力の挙動（契約の対象外）、`T` が `long long` 以外のときの検証。C++ のテストは `tests/group.cpp` で、`__builtin_add_overflow`/`__builtin_mul_overflow` を独立した基準として、極値を含む全組と、アフィン写像の合成・適用・逆元（`T = int`、`double` の具体化も含む）を確認する。


## applyの元の参照APIへの復元（2026-10-15）

公開側に残っていた値渡しのapplyを元のconst T&へ戻した。単なる整数の出力一致だけでは、コピーが観測できるTで元と同じ挙動を保証できないためである。型T、構成子、他の演算、戻り値は維持する。

共通生成モデルはa/b/xをすべて読み取り専用参照として受ける。affine_apply_correctも第三引数を既存callerセルへの参照に変更し、a*xとa*x+bがlong longの範囲内という元の算術条件を保ったまま結果・停止・状態保存・定数のwork/追加領域上界を証明する。参照が同じセルを指す場合も許し、入力値をコピーするcalleeセルは作らない。モデルの一時引数はcaller側でセルとして用意した状態で扱う。

C++テストはメンバー関数の型のstatic_assertと、コピー回数を数える型で引数コピーが0回であることを確認する。Leanテストは一般定理の適用、3参照の読み取り専用binding、receiverとの別名/全引数の別名/順序変更、callerメモリの保存を確認する。これらのC++型テストを、組込み整数以外のTのLean証明済みとはしない。
