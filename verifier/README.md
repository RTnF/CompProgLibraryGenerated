# C++ 検証基盤（新方式）

方式は `docs/redesign_2026-11.md`、翻訳規則と STL の表は `docs/translation.md` を参照する。

- `lean_translate.py`: 固定した Clang の JSON 構文木から、制限構文の C++ テンプレート定義を Lean の関数（`Proofs/Cpp/Gen/*.lean`）へ機械的に翻訳する。意味論は `Proofs/Cpp/Prelude.lean`（`Cpp.M := StateT Nat Option`、tick と非停止）で一度だけ定義する。表にない構文・STL 操作は拒否する。
- `model_bridge.py`: 公開部品（`translation = "lean_model"`）の登録モデルが、公開ヘッダから再生成した Lean と全文一致することを確かめ、差分テストを実行する。
- `diff_harness.py`: C++（ASan/UBSan 付き）と生成 Lean のインタプリタを同じ入力で動かし、出力の一致を要求する。入力は `tests/diff/*.py` の生成スクリプトが作る。
- `clang_ast.py`: 固定した Clang 22.1.4 と GCC 13.3.0 のヘッダで `cp::` の公開宣言を列挙し、TOML の宣言一覧とヘッダ全体の SHA-256 を照合する。
- `support.toml`: 部品に属さない共有の Lean モジュール（`Proofs/Cpp/Prelude.lean`、`Proofs/Cpp/Lib/`、`Proofs/Math/`）、検証器、共有検査、文書の登録。

C++ の文ごとの記号実行による旧方式の変換器（`scalar_ir.py`、`state_ir.py`、`nested_ir.py` など）とその証明は 2026-11-19 に削除した（Git 履歴に残る）。
