# マージソート実測: 2026-09-29

## 条件

- 対象: `cp::merge_sort(std::vector<int>)`、30 万要素、2 秒未満を目標。
- 入力: `std::mt19937_64` と `std::uniform_int_distribution<int>(INT_MIN, INT_MAX)`。シードは 20260928 から 20260932。ケースを順に生成・実行し、並列実行なし。
- `input_hash`: 初期値 `1469598103934665603`、各整数を `uint32_t` に変換して XOR し、`1099511628211` を掛ける操作を順に反復。`uint64_t` の剰余演算。
- 環境: x86_64、AMD Ryzen 5 5600X、WSL2 Linux `6.6.87.2-microsoft-standard-WSL2`、VM メモリ 15 GiB。
- コンパイラ: GCC 13.3.0、`-std=c++17 -O2 -Wall -Wextra -pedantic`。
- 計測: `std::chrono::steady_clock` でソート呼び出しのみ。入力生成と結果の非減少チェックは除外。`/usr/bin/time` でプロセス全体の経過時間と最大 RSS を別途取得。

## 結果

| シード | 入力ハッシュ | ソート時間 |
| ---: | ---: | ---: |
| 20260928 | 1509227979619982748 | 33.905 ms |
| 20260929 | 10722250734341644101 | 31.592 ms |
| 20260930 | 3497850409671007560 | 33.364 ms |
| 20260931 | 16308723788654148747 | 44.136 ms |
| 20260932 | 17183469859886680923 | 34.307 ms |

最大 44.136 ms で、指定された 2 秒より短い。プロセス全体の経過時間は 0.19 秒、最大 RSS は 8564 KiB。この値は上記 VM での実測であり、各オンラインジャッジの実行時間を保証するものではない。

再実行:

```sh
g++ -std=c++17 -O2 -Wall -Wextra -pedantic benchmarks/merge_sort.cpp -o /tmp/merge-sort-bench
/usr/bin/time -f 'wall_seconds=%e max_rss_kb=%M' /tmp/merge-sort-bench
```
