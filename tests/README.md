# C++ テスト

`merge_sort.cpp` は長さ 0〜8 の三値入力を網羅し、極値を含む入力と 30 万要素の固定シード乱数入力も確認します。順序と多重集合を別々に検査し、標準ライブラリのソート関数は使いません。各テストはライブラリ内の `small_template.hpp` を最初に include します。CI は依存順の include と、全部品を同時に include した結果もコンパイルします。

`associative_array.cpp` は境界、0 の代入、再代入と固定シードの操作列を確認します。`associative_array_checker.cpp` は Library Checker 形式の入出力確認用です。入出力ケースは `tests/data/` に置き、部品の TOML に登録します。`python3 tools/check_public.py` は全ケースとテンプレートを先に include した結合結果のコンパイルを実行します。

ケースの内容は生成スクリプトまたは専用テキストファイルに置き、TOML と YAML にはファイルの参照先だけを記録します。テストと CI はコンテストサイトと通信しません。 入力は `in/*.txt`、期待出力は `out/*.txt` に統一する。
