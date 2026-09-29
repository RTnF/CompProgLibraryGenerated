# Lean 証明

`Generated/MergeSort.lean` は、レビューした Clang 構文木との一致確認後に出力する信頼済みモデルです。`MergeSort.lean` は、整列、順列保存、再帰と添字の境界、モデル上の仕事量 `O(n log n)`、整数要素の保持数 `O(n)` を証明します。`Proofs.lean` からこれらをビルドします。

`Generated/AssociativeArray.lean` は `std::map` 操作の契約に対応するモデルです。`AssociativeArray.lean` は、未設定値、更新、別キーの不変性、操作列の停止、操作回数、名目的な費用と更新回数の上界を示します。C++ への費用・領域の適用条件は各部品の文書に記録します。
