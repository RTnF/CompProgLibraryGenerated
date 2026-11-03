# 公開部品

公開部品は `safe_mod.hpp`、`floor_sum_unsigned.hpp`、`floor_sum.hpp`、`bit_width_u64.hpp`、`doubling.hpp`、`enumerate_quotients.hpp`、`search_util.hpp`、`sort_util.hpp`、`mod61.hpp`、`extrema.hpp` です。隣接する TOML に依存先、公開宣言、ソース全体のハッシュ、証明、検証器、テスト等の参照先を記録します。`safe_mod` は正の法に対する符号付き64 bit 整数の剰余の正規化で、[仕様と検証範囲](../docs/safe_mod_experiment.md) を参照してください。`floor_sum_unsigned` は n<2^32、0<m<2^32 のもとで床関数の和を64 bit剰余で返します。[仕様と検証範囲](../docs/floor_sum_experiment.md)を参照してください。`floor_sum` は signed64 の係数を扱い、総和が表現可能な場合の正確な値と、それ以外の場合の GCC 13.3 / x86_64 Linux / C++17 / LP64 の変換結果を検証します。すべての部品は共通の型付き AST → IR → Lean 変換器を使います。`python3 tools/check_public.py` は登録部品を全件検証します。

ライブラリ内のテンプレートを先に、依存部品と対象部品を続けて include して使用します。現在は持ち込みコードの `experiments/library/cpp/template/small_template.hpp` を使います。このテンプレート自身の Lean 検証は全件検証計画の対象です。`python3 tools/public.py --include-check enumerate_quotients --output /tmp/enumerate-quotients-included.cpp` で確認用コードを生成し、リポジトリルートを `-I` に指定してコンパイルできます。
