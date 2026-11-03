# doubling の C++17 修復と公開（`library/doubling.hpp`）

原本 `experiments/library/cpp/array/doubling.hpp` は C++20 の `bit_width` を参照し、固定した C++17 環境ではコンパイルできない。原本を保持し、候補を `library/doubling.hpp` に置いた。入力を const 参照とし、添字への int 変換前にサイズ上限を検査する。ライブラリのテンプレートを先に include するテストを用意した。

前提は `kmax > 0`、サイズが INT_MAX 以下、全要素が `[0,n)` 内であること。空配列も許す。行数は kmax のビット幅、行 i の頂点 j は写像の 2^i 回適用である。候補の時間と出力領域は O(n × bit_width(kmax))。vector の割当・添字・所有権・寿命・例外を含む本体の AST 変換と Lean 証明は未完了で、公開済みとは扱わない。

C++17 の `bit_width_u64` はゼロに0を返し、それ以外では2による除算を繰り返す。共通変換器の生成 IR と Lean モデルを保存し、再生成の全文一致を検査する。`Proofs/BitWidthU64.lean` は実際の生成本体について、全 uint64 入力での結果、整数範囲内の実行、停止、caller メモリの保持を証明する。幅 w は64以下で、実行枠80で成功する。抽象仕事量は `9 + 14*w`（最大905）、追加領域は8。これは実測時間やバイト数ではなく共通モデルの単位である。幅の数学的特徴付けも証明し、C++ の signed 加算・unsigned 除算の検査を通す。

`tests/test_bit_width_u64.py` は523入力で Python の bit_length と生成モデル・費用・caller メモリを照合し、改名の不変性を確認する。実行枠不足は exhausted、負値・uint64 範囲超過・引数不足 / 過剰・参照引数は fault として拒否する。除数・増分・条件・返却値の4改変を再生成し、元の全入力証明が拒否されることを確認する。`tools/check_import_doubling.py` は原本の C++17 エラーを再現し、候補を通常実行と ASan/UBSan で検査する。独立した経路・周期の計算と全3,414写像（サイズ0〜5）、各14種類の kmax を照合する。ヘルパーは小整数、全64桁の境界、固定乱数でも検査する。テストはネットワークを禁止して実行する。

読み書き・reserve・容量内追加と参照の再割当無効化に必要な共通モデル基盤を追加した。[vector 操作の契約と未接続部分](vector_contracts.md)を参照する。これは doubling の AST 本体の生成・証明を完了させるものではない。

## 全入力の Lean 証明（2026-10-07）

生成した入れ子 vector の本体（`Proofs/Generated/DoublingNested.lean`、生成器 `verifier/nested_ir.py`）について、`Proofs.DoublingCall.doubling_correct` が全入力の結果・停止・費用を証明する。前提は `CallerOK`（検証済みの呼出し状態に const な根 vector `v` が束縛されている）、全要素が `[0,n)`、`0 < kmax < 2^64`、`n` が INT_MAX 未満。結論は、ある fuel で `NProgram.callFuel` が `finished` になり、返る根の行 k が `tableRow items k`、行数が `bit_width(kmax)`、`v` の buffer が不変、根が呼出し側 scope に移ることである。

費用は `DoublingPost` に記録する。vector 側の追加仕事量は `(w+1)+(n+1)+(w-1)(2n+1)`（w は行数）で、ちょうどこの値に等しい。スカラー側の仕事量は `kexpr` の式の大きさに加えて `(w-1)(60n+200)+100n+1010` 以下、領域の peak は呼出し側の live 領域に `w + n·w + 3` を加えた値以下である。

`DoublingProgram.body_eq` は、Lean の `bodyCmd` が生成物の本体と `rfl` で一致することを示す。生成物を変えるとこの検査が壊れる（`tests/test_doubling_proof.py` に改変の拒否検査がある）。呼出し側の `v` 以外の buffer が不変であることと、前提違反時に必ず fault になることは、この定理にまだ含めていない。
