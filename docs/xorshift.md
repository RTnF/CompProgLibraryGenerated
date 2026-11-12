# xorshift

`cp::Xor64` は 64 bit の Xorshift 乱数生成器である。元の `experiments/library/cpp/random/xorshift.hpp` の `Xor64` から、状態更新 `get()` を取り出した。`get_int`、`get_ll`、`get_double`、`get_double(lo, hi)`、`get_normal` は、メソッドからメソッドを呼ぶ（`get()` を this に対して呼ぶ）か、浮動小数点を使うため、まだ変換器の対象外で `experiments/` に残している。コンストラクタ `Xor64(s)` は、引数をそのまま状態にする関数として変換され、`xor64_new_correct` が証明している。

- `get()`: 状態 `s` を `x = s; x ^= x << 7; x ^= x >> 9; s = x` に進め、新しい状態を返す。前提なし（`uint64_t` の全値）。結果は `[0, 2^64)`。状態 0 は 0 のまま（周期を得るには非零の種が必要）。
- 時間と領域: 分岐もループもない定数時間、定数個の局所変数。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がヘッダから `Proofs/Cpp/Gen/Xorshift.lean` を生成する（`unsigned long long` は `UInt64` で、シフトと排他的論理和は C++ と同じく 2^64 を法とする）。`Proofs/Cpp/Xorshift.lean` が次を証明する。

- `init_spec`: `Xor64(s)` の状態は `s`。tick 数 1。
- `get_spec`: `get()` は状態を `xnext s`（`x = s ^ (s << 7); x ^ (x >> 9)`）に進め、それを返す。前提なし（全状態）。tick 数 1。
- `xnext_zero`: 状態 0 は 0 のまま。

定理に含めていないこと: 非零の状態が非零のまま続くこと（C++ のテストで確かめる）、`get_int` など元の他のメソッド。差分テスト（`tests/diff/xorshift.py`）と C++ のテスト `tests/xorshift.cpp`（独立に書いた状態更新との照合、状態 0 の固定点、非零状態の持続）で翻訳と実装を確かめる。
