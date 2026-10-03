# 公開部品

公開部品は `merge_sort.hpp` と `associative_array.hpp` です。隣接する TOML に依存先、公開宣言、ソース全体のハッシュ、証明、検証器、テスト、測定手順の参照先を記録します。C++ から Lean への変換器は部品ごとの専用実装です。新しい部品は、その部品に対応する検証経路が揃ってから追加します。`python3 tools/check_public.py` は登録部品を全件検証します。

ライブラリ内のテンプレートを先に、依存部品と対象部品を続けて include して使用します。現在は持ち込みコードの `experiments/library/cpp/template/small_template.hpp` を使います。このテンプレート自身の Lean 検証は全件検証計画の対象です。`python3 tools/public.py --include-check merge_sort --output /tmp/merge-sort-included.cpp` で確認用コードを生成し、リポジトリルートを `-I` に指定してコンパイルできます。
