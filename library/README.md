# 公開部品

公開部品は `merge_sort.hpp` と `associative_array.hpp` です。隣接する TOML に依存先、公開宣言、ソース全体のハッシュ、証明、検証器、テスト、測定手順の参照先を記録します。C++ から Lean への変換器は部品ごとの専用実装です。新しい部品は、その部品に対応する検証経路が揃ってから追加します。`python3 tools/check_public.py` は登録部品を全件検証します。

部品は依存先と合わせて `a.cpp` の `solve()` より前に手直しなく貼れる C++ とします。`python3 tools/public.py --assemble merge_sort --output /tmp/merge-sort-pasted.cpp` で貼り付け結果を生成できます。
