# safe_mod の仕様と検証

元は `experiments/library/cpp/number_theory/floor_sum.hpp` の `safe_mod`。用途は正の法 `m` に対する代表元を `[0,m)` に正規化すること。入力は LP64 の符号付き64 bit 整数 `x` と `m`、前提は `m > 0`。公開ヘッダ `library/safe_mod.hpp` は本体を保持し、専用名前空間 `cp::` と標準の固定幅整数型を使う。元コードは変更しない。

固定幅整数の演算回数と追加領域は一定である。`safe_mod` は公開登録する。`floor_sum_unsigned` と `floor_sum` 全体も未検証である。

## 生成モデルの全入力証明

`Proofs/Generated/SafeMod.lean` は候補 C++ の型付き AST → 共通 IR → Lean で生成する。`tools/check_safe_mod_proofs.py` が、元ヘッダと候補の IR 一致、および生成 Lean の全文一致を毎回検査する。ハッシュや部品名で意味を選ぶ変換規則は使わない。

`Proofs/SafeModProofs.lean` は、型の範囲内の全 `x,m` と `m > 0`、任意の呼び出し側メモリを対象に次を証明する。

- `quotient_valid`：商が符号付き64 bit に収まる。
- `remainder_valid`：剰余が同じ型に収まる。
- `normalized_remainder`：負の剰余に法を足した値が `Int` の非負剰余と一致する。
- `safe_mod_correct`：実際の生成モデルの実行が正常に終了し、`x % m` と元の呼び出し側メモリを返す。仕事量は負の剰余のとき15、それ以外は11、最大追加領域は8。
- `safe_mod_bounds`：正常終了する結果が存在し、結果は `[0,m)`、メモリは保持、仕事量は15以下、追加領域は8以下。

仕事量は固定幅の算術・読み出し・変換・判定・格納・return の抽象費用である。追加領域は私有セル・束縛・式の一時値を数える保守的な上界で、Lean の実装費用や実測スタックサイズではない。停止は文の木に対する構造的な評価と全入力での正常終了により扱う。型、除数、商、剰余、加算のモデルの検査をすべて通過する。C++ の UB 不在への意味対応は、Clang、LP64 ABI、共通変換規則と整数・状態の契約を信頼境界とする。Lean 定理だけでコンパイラや変換器の正しさを証明したとはしない。

5定理の `#print axioms` は `propext`、`Classical.choice`、`Quot.sound` のみを報告する。未説明の公理や `sorry` は使わない。共有基盤の登録を通して、全公開検証の Lean ビルド・`leanchecker` と CI の公理監査の対象にする。`library/safe_mod.toml` に宣言・モデル・証明・C++ テスト・仕様を登録し、共通 `state_bridge.py` に接続する。

共通の状態変換器は `%=` と `+=` を型付きの読み出し・演算・格納に変換する。元ヘッダの宣言を直接読み、候補からの IR と全文のデータ構造が一致することを確認する。対象宣言を AST filter で選ぶが、意味の変換規則は構文・型に対応する。型別名 `ll` の綴りには依存しない。関数型に Clang の正規化した返却型がない場合には、同じシグネチャの値引数に提供された正規化型で同じ綴りの返却型を解決する。その情報のない返却型別名は引き続き拒否する。

`tests/test_state_ir.py` が、符号付き最小値・最大値を含む7値×正の法5値を Python の剰余と生成 Lean・元 C++・候補 C++ で比較する。テンプレートを先に include し、元ヘッダと候補を同時に include して UBSan で実行する。ゼロ除算のモデルでの拒否と、`%=` を `/=` に変える変更で元の結果を要求する検査が失敗することも確認する。これらの有限ケースは全入力証明を代替しない。

`tests/test_safe_mod_proofs.py` は `%=` を `/=` に、または `+=` を `-=` に変えた C++ からモデルを生成し直し、同じ全入力の証明が失敗することを確認する。ケースだけでなく、実装に接続した全入力定理についての変更検出である。

```sh
python3 tests/test_state_ir.py
python3 tools/check_safe_mod_proofs.py
python3 tests/test_safe_mod_proofs.py
python3 tools/check_public.py
python3 verifier/state_ir.py experiments/library/cpp/number_theory/floor_sum.hpp \
  --include-dir experiments/library/cpp --declaration-filter safe_mod \
  --ir /tmp/safe_mod.json --lean /tmp/safe_mod.lean
```

公開 C++ テストはテンプレートを先に include し、10,050小規模入力、35境界入力、固定シード10,000入力を独立した符号なしの絶対値による参照実装と比較する。通常実行と ASan/UBSan を登録ゲートで実行する。constexpr の利用も確認する。対応する問題と制限が未定なので性能測定は行わず、実測値を主張しない。持ち込みの floor_sum 全体の変換と証明、既存2部品の共通変換への移行と全件台帳の残りは引き続き未完了である。
