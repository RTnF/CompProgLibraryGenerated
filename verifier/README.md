# C++ 検証基盤

`clang_ast.py` は固定した Clang 22.1.4 と GCC 13.3.0 のヘッダで `cp::` の公開宣言を列挙し、TOML の宣言一覧とヘッダ全体の SHA-256 を照合します。`merge_sort_bridge.py` はさらに `cp::merge_sort` の正規化構文木をレビュー済み SHA-256 と比較します。モデルはソース固有の信頼済み変換として生成されます。C++ の任意のコードを検証する汎用変換器ではありません。ソースを変更したら構文木と意味対応を再レビューする必要があります。

宣言一覧の対応種別は `FunctionDecl`、`TypeAliasDecl`、`CXXRecordDecl`、`EnumDecl`、`VarDecl` に限ります。`cp::` に別の宣言が現れた場合や同名の多重定義が現れた場合は公開判定を止め、bridge と意味対応のレビューを要します。

`associative_array_bridge.py` は公開型別名と二つの公開関数の構文木を確認し、レビューした `associative_array_model.lean.in` から Lean モデルを生成・照合します。`std::map` の意味・計算量契約と C++ からモデルへの対応は信頼前提です。
