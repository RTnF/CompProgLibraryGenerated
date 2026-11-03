# bit_width_u64

`cp::bit_width_u64(std::uint64_t)` は C++20 の `std::bit_width` の C++17 向け代替で、値 0 に対して 0、それ以外では 2 進表現の桁数を返す。実装は 2 による除算を繰り返す。返り値は `int` で、`0` から `64` までである。

- 前提: なし（`uint64_t` の全値を受け付ける）。
- 結果: `0 < x` のとき `⌊log2 x⌋ + 1`、`x = 0` のとき `0`。
- 時間: 返す桁数を w として O(w)（ループは w 回）。追加領域は定数（局所変数2個）。

共通の状態生成器（`verifier/state_ir.py`）が C++ の AST から Lean のループ表現を生成し、`Proofs/BitWidthU64.lean` が全 `uint64` 入力について結果・停止・仕事量・追加領域を証明する。仕事量は `9 + 14w`、追加領域の peak は 8 セルである。`Proofs/DoublingCall.lean` の `doubling` 証明は、この証明の `call_bounds` を使って呼出しの結果と費用を得る。

C++ のテストは `tests/bit_width_u64.cpp` で、`__builtin_clzll` を独立した基準として境界値（`2^k − 1`、`2^k`、`2^k + 1`）と乱数を照合する。
