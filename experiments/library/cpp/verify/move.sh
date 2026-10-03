#!/bin/bash

# `ac` ディレクトリが存在しない場合は作成
mkdir -p ac

# `*.test.cpp` ファイルをループ処理
for file in *.test.cpp; do
  # PROBLEM の値を取得
  problem_value=$(awk '/^#define PROBLEM/ {
    if ($3 ~ /\\/) {
      getline next_line
      print $3 next_line
    } else {
      print $3
    }
  }' "$file" | tr -d '\\' | tr -d '"' | xargs)
  # echo $problem_value
  
  if [[ $problem_value == *atcoder* ]]; then
    # 新しいファイル名を生成
    new_file="ac/${file%.test.cpp}.test_ac.cpp"
    # ファイルを移動し、リネーム
    mv "$file" "$new_file"
    echo "Moved and renamed: $file -> $new_file"
  fi
done
