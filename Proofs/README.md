# Lean 証明

- `Cpp/Prelude.lean`: 翻訳先の意味論（`docs/translation.md`）。
- `Cpp/Gen/`: `verifier/lean_translate.py` が公開ヘッダから生成したモデル（手で編集しない）。
- `Cpp/<Stem>.lean`: 各公開部品の仕様と証明（結果・停止・計算量のオーダー）。
- `Cpp/Lib/`: 部品に依存しない共有の補題。
- `Math/`: アルゴリズムの純粋な数学（旧方式の証明から、新方式の証明が使う定義と定理だけを残したもの）。
