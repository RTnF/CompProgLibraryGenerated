# マージソートの測定手順

## 条件

- 対象: `cp::merge_sort(std::vector<int>)`、30 万要素、2 秒未満を目標。
- 入力: `std::mt19937_64` と `std::uniform_int_distribution<int>(INT_MIN, INT_MAX)`。シードは 20260928 から 20260932。ケースを順に生成・実行し、並列実行なし。
- `input_hash`: 初期値 `1469598103934665603`、各整数を `uint32_t` に変換して XOR し、`1099511628211` を掛ける操作を順に反復。`uint64_t` の剰余演算。
- コンパイルオプション: `-std=c++17 -O2 -Wall -Wextra -pedantic`。
- 計測: `std::chrono::steady_clock` でソート呼び出しのみ。入力生成と結果の非減少チェックは除外。`/usr/bin/time` でプロセス全体の経過時間と最大 RSS を別途取得できる。

## 入力の確認値

| シード | 入力ハッシュ |
| ---: | ---: |
| 20260928 | 1509227979619982748 |
| 20260929 | 10722250734341644101 |
| 20260930 | 3497850409671007560 |
| 20260931 | 16308723788654148747 |
| 20260932 | 17183469859886680923 |

実測値と測定マシンの情報はコミットしない。測定時には、実行環境、コンパイラの版、入力、方法、時間、メモリを `benchmarks/local/` に記録する。

再実行:

```sh
g++ -std=c++17 -O2 -Wall -Wextra -pedantic benchmarks/merge_sort.cpp -o /tmp/merge-sort-bench
/usr/bin/time -f 'wall_seconds=%e max_rss_kb=%M' /tmp/merge-sort-bench
```
