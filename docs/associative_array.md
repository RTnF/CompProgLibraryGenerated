# Associative Array

## 用途と前提

[Library Checker の問題](https://judge.yosupo.jp/problem/associative_array) は、初期値がすべて 0 の連想配列に対し、`0 k v` で代入し、`1 k` で値を出力する。公式の[問題データ](https://github.com/yosupo06/library-checker-problems/tree/master/data_structure/associative_array)では `1 ≤ Q ≤ 1,000,000`、`0 ≤ k, v ≤ 10^18`、制限時間 5 秒である。問題データの README はローカルでのテスト利用を案内している。この環境からの提出は行わない。

`library/associative_array.hpp` は `cp::AssociativeArray`、`cp::associative_array_set`、`cp::associative_array_get` を提供する。空の `cp::AssociativeArray` から始め、更新済みのキーには最後に代入した値を返し、未設定キーには 0 を返す。0 の代入も有効である。キーと値は符号なし 64 ビット整数で保持し、問題の上限はその範囲内にある。標準ヘッダを含み、`a.cpp` の `solve()` の直前に貼れる。

`std::map` の要素数を `n` とすると、更新と参照は最悪 `O(log(n+1))` 時間であり、追加領域は `O(n)` である。合計 `Q` 操作は最悪 `O(Q log(Q+1))` 時間、`O(Q)` 領域である。`std::map` の比較、探索、代入の契約、およびメモリ確保の成功を前提とする。ハッシュの分布や乱数への前提はない。

## 検証の範囲

`verifier/associative_array_bridge.py` は Clang 22.1.4 と GCC 13.3.0 のヘッダを使い、公開型別名と二つの公開関数の正規化 AST、および C++ ソース全体の SHA-256 を照合する。その上で、レビュー済みの対応表から `Proofs/Generated/AssociativeArray.lean` を生成・照合する。対応する C++ 構文は型別名、関数呼び出し、局所変数、条件演算子、イテレータ比較・参照、戻り値である。対応する STL 操作は `std::map` の空の構築、`insert_or_assign`、`find`、`end`、イテレータの `->second` である。別の構文や操作を使う変更は、AST と意味対応の再レビューを要する。

Lean モデルは `std::map` を有限部分写像として扱い、未設定値を 0 にする。`Proofs/AssociativeArray.lean` は空状態での参照、同一キーの更新、別キーの不変性、操作列の停止、操作数と更新数の上界を証明する。標準ライブラリ契約から各操作に `O(log(n+1))` の費用を与え、Lean で `Q * (1 + log₂(Q+1))` の正規化費用と更新数 `≤ Q` を示す。この費用は CPU 命令数の具体的な上界ではなく、STL 契約の定数倍を省いた単位である。

`get` のイテレータ参照は `end` と異なる分岐に限るため、STL 契約とメモリ確保成功の下で未定義動作はない。公開関数内には反復がなく、各 STL 操作の停止を契約として使う。Clang AST から Lean モデルへの**意味対応そのものは証明されていない**。C++ コンパイラと STL の仕様準拠も信頼前提である。入出力を含むテスト用の問題プログラムは証明対象外である。

## 確認

`tests/associative_array.cpp` は境界値、未設定キー、再代入、0 の代入と固定シードの操作列を確認する。`tests/associative_array_checker.cpp` は問題形式の入出力を確認する。`tools/public.py` で `a.cpp` に貼った結果も C++17 でコンパイルする。[公式ケースの生成・測定手順](../benchmarks/associative_array_official.md)を公開し、実測値と測定環境は Git の追跡対象外である `benchmarks/local/` に保存する。ローカル測定はジャッジでの実行時間を保証しない。
