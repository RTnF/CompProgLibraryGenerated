# Associative Array 公式ケースの測定手順

[Library Checker Problems の対象ディレクトリ](https://github.com/yosupo06/library-checker-problems/tree/1814c4e5205517e368bb57a8d1127eb961cfeaae/data_structure/associative_array)をコミット `1814c4e5205517e368bb57a8d1127eb961cfeaae` で取得する。公式リポジトリ直下で `python3 generate.py -p associative_array` を実行すると、`info.toml` に登録された 20 ケースの入力と正解出力が生成され、`hash.json` と照合される。

このリポジトリから次を実行する。測定スクリプトは `tests/associative_array_checker.cpp` を `-std=c++17 -O2 -Wall -Wextra -pedantic` でコンパイルし、全公式ケースを各 3 回実行する。各実行の出力を公式正解の SHA-256 と照合し、経過時間と最大 RSS を出力する。

```sh
mkdir -p benchmarks/local
uname -a > benchmarks/local/environment.txt
lscpu >> benchmarks/local/environment.txt
g++ --version >> benchmarks/local/environment.txt
python3 benchmarks/associative_array_official.py /path/to/library-checker-problems --repeats 3 > benchmarks/local/associative_array_official.tsv
```

`benchmarks/local/` は Git の追跡対象外である。測定した環境情報と実測値はそこに保存し、コミットしない。公式ケースの出典と生成法、コンパイル条件、検証方法はこの文書とスクリプトに残す。
