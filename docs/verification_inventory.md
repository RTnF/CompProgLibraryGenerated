# 持ち込みコードの検証台帳

全件検証計画の対象ファイルは [verification_inventory.json](verification_inventory.json) に記録する。元ヘッダ68件、テンプレート C++ 4件、テストドライバ65件の合計137件であり、手動・無視指定・`verify/ac/` のドライバも含む。二系列を混ぜず、それぞれの include root を使う。

台帳には元パス、ソース SHA-256、ローカル依存先、Clang による宣言の列挙、用途のコメントからの候補、関連ドライバ、重複候補、検証先、コンパイル結果を残す。宣言の種類・行・型を含む記述を記録して多重定義を区別し、コンストラクタ、private の補助関数、テンプレート内の関数も残す。コンパイラが暗黙生成した宣言は対象外とする。

宣言抽出は固定 Clang の text AST による初期調査であり、共通の意味変換器ではない。構文エラーのあるソースの AST は `partial` とする。マクロの位置と宣言列挙の完全性は人手での確認が残る。`including_drivers` は include の到達関係に過ぎず、全メンバの具体化や実行を示さない。`duplicate_candidates` は綴りの共通性に基づく候補であり、API・仕様の同一性を示さない。`byte_identical_sources` は全ファイルのバイト列が一致するものを示すが、個別の依存先とテストの確認は引き続き必要である。

`status` の調査・不具合・C++ テスト・共通変換器・Lean・include 実行確認・公開は、ファイルと宣言の両方で別々に管理する。未調査の不具合は `unknown` であり、「不具合なし」ではない。コンパイル成功だけで `cpp_tested`、`include_verified`、`lean_proved` を更新しない。検証先が未決定のものは `null` のまま追跡する。

通信を禁止した上で、次を実行する。

```sh
python3 tools/inventory_imports.py
python3 tools/inventory_imports.py --compile-drivers
python3 tools/inventory_imports.py --check
python3 tests/test_import_inventory.py
python3 tools/check_import_element_count.py
python3 tools/check_import_square_matrix.py
```

最初のコマンドは各ヘッダを系列内の small template の後に include して C++17 の構文確認を行う。各 `.cpp` の構文も確認する。次のコマンドは全ドライバとテンプレート C++ を実行可能ファイルまでコンパイル・リンクする。持ち込みドライバの実行と公式ケースの取得は行わない。最後の C++ テストはローカル生成ケースだけを使う。

再生成はソースのハッシュが同じファイルのレビュー状況・根拠・検証先を保持する。ソースが変わったファイルは未確認に戻す。`--check` はファイルの追加・削除、重複登録、ソース変更、依存先変更を検出する。これは台帳の整合性検査であり、公開条件の検証コマンドを代替しない。


## 2026-11-02のSquareMatrix差分確認

原本の比較とpowの不要な最終二乗を修正し、同ヘッダーだけを再走査した。Clangは18宣言を取得してpassedとなり、137ファイル全体のcoverage・source hash・依存参照の整合も確認した。原本の全APIは[専用回帰](../tests/imports/square_matrix_source.cpp)で通常実行とASan/UBSanを確認した。pow(ll)、行配列参照、公開matと型trait、独自要素型、全81行列/6561組、境界の累乗を含む。

台帳の同ファイルはpartialのまま、既知不具合の修正とC++実行・include確認だけを記録した。共通変換器、クラス全体のLean証明、公開は未完了。以下のコンパイル集計は初期調査の履歴であり、現在の全件検証成功ではない。

## 初期コンパイル結果

GCC 13.3.0 / C++17 で137件中123件の構文確認が成功し、14件が失敗した。テンプレート C++ 4件とドライバ65件のコンパイル・リンクでは60件が成功し、9件が失敗した。リンク段階だけで新たに失敗したものはなかった。元ドライバの実行による機能確認はまだ行っていない。

ヘッダとテンプレートから AST 宣言レコード1,434件を抽出した。これにはテンプレート宣言と本体、フィールド、内部の補助関数も含むため、公開部品数や関数数ではない。Clang の調査は66ファイルで成功し、6ファイルは部分的である。バイト列の一致は両系列の small template と、第一系列の `union_find/disjoint_set_union.hpp`・`union_find/union_find.hpp` の2組で確認した。統合先はまだ決定していない。

| 失敗元 | 確認した原因 | 影響する元ファイル数 |
| --- | --- | --- |
| `array/doubling.hpp` | C++17 にない `bit_width` | 当該ヘッダ、`tree/tree.hpp`、木のドライバ7件 |
| `fps/convolution.hpp` | C++17 にない `countr_zero` 等 | 当該ヘッダ、畳み込みドライバ1件 |
| `interval/interval.hpp` | 三方比較 `operator<=>` | 当該ヘッダ |
| `number/ratio.hpp` | `strong_ordering` と三方比較 | 当該ヘッダ |
| `verify/ac/rolling_hash_2.test_ac.cpp` | C++17 にない `unordered_set::contains` | 当該ドライバ |

この一覧はコンパイル失敗の初期分類であり、修正後の機能・算術・停止・計算量を保証するものではない。全件の診断は JSON の `compile.diagnostics` に残している。Clang の宣言調査が `partial` の6件も再調査が必要である。そのうち `number/square_matrix.hpp` は GCC の未具体化の構文確認を通るが、Clang が `SquareMatrix<T, n>` の存在しないメンバ `x` への参照を検出した。[比較演算子の再現コード](../tests/imports/square_matrix.repro.cpp) を GCC で具体化しても同じ不具合を確認した。元コードは保持し、[修正候補の仕様・再現・テスト](square_matrix_experiment.md) を別途記録した。修正候補は C++ テスト済みだが、共通変換器と Lean 証明は未完了である。

## 個別の確認と修正候補

### element_count

元の `experiments/library/cpp/array/element_count.hpp` は未具体化のヘッダだけならコンパイルできるが、`element_count(vector<int>{1, 1, 2})` が失敗する。テンプレート引数 `T` をコンテナ型として推論する一方、要素と戻り値の型にも `T` を使っているためである。[再現コード](../tests/imports/element_count.repro.cpp) と専用検査がこの失敗を確認する。

元ソースを保持し、修正候補を `experiments/verification/array/element_count.hpp` に置く。入力を `const vector<T>&` に変更し、`cp::element_count` とする。元の走査を保持し、サイズが `INT_MAX` 以下である前提の assert を加える。これは全体での頻度集計ではなく、隣接する等しい値の各連続区間を `(値, 長さ)` にする。非連続の同値は別の区間として返す。空入力は空出力となる。

等値比較は同値関係であり、要素のコピー・代入とメモリ確保が成功すると仮定する。要素操作が定数時間なら時間は O(n)、返却用の追加領域は O(連続区間数) である。`int` の区間長とループ添字はサイズ上限の下で範囲内に収まる。これらの Lean 証明とソースからの意味変換は未完了であり、公開対象ではない。

修正候補と元の `char_count` に対し、長さ0〜8・3種類の値の全9,841入力を、隣接境界の列から作る参照実装と比較する。さらに整数の最小・最大値、文字列の要素、NUL と高位ビットのある文字を確認する。`char_count` の比較は1バイト単位であり、Unicode の文字数を扱う仕様ではない。テストではテンプレートを先に include して両部品を同時に使う。

通常のテストと ASan/UBSan は成功した。UBSan は回復を無効にして診断を失敗として扱う。この環境の ptrace 実行では LeakSanitizer が動作しないため、専用検査は `detect_leaks=0` を設定している。リーク検査済みとはしない。

## 残作業

台帳は初期調査であり、全関数・型の使用例の具体化、用途・前提・境界のレビュー、重複の同一性確認と統合、共通 AST → IR → Lean 変換、全分野の証明・差分テスト、公開登録は引き続き必要である。コンパイル失敗と `partial` の宣言調査も個別に解消する。公開2部品は回帰確認として保持する。
