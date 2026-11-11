# 構造とワークフロー

## 現在の段階

公開部品は `library/` の `safe_mod.hpp`、`floor_sum_unsigned.hpp`、`floor_sum.hpp`、`bit_width_u64.hpp`、`doubling.hpp`、`enumerate_quotients.hpp`、`search_util.hpp`、`sort_util.hpp`、`mod61.hpp`、`extrema.hpp`。すべての部品が共通の型付き AST → IR → Lean 変換器（`doubling` は入れ子 vector 用の `verifier/nested_ir.py`）を使い、全入力の結果・停止・安全性・時間と追加領域の証明、C++ 比較と sanitizer、公開登録を備える。signed floor_sum は GCC 13.3 / x86_64 Linux / C++17 / LP64 の整数変換契約を明示する。共通変換器の [スカラー部分言語](scalar_converter.md)、[分岐・更新・参照](state_converter.md)、[ループの停止条件](loop_converter.md) は整備中であり、クラス・関数テンプレート・ラムダ・一般の STL は未完了。新しい部品は共通変換器での意味生成、証明、テスト、登録が揃うまで `experiments/` に置く。

持ち込みライブラリの全件検証では、対応する C++ 部分言語に対する共通の AST → 中間表現 → Lean 生成器へ移行する。部品固有の AST ハッシュに手書きモデルを対応させる方式を新しい部品へ増やさない。既存の専用 bridge は移行中の回帰確認として保持する。仕様と証明は部品ごとに用意し、共通変換器が未対応の構文は拒否する。詳細は [全件検証計画](verification_plan.md) を参照する。

## 領域

| パス | 用途 |
| --- | --- |
| `experiments/library/cpp/template/` | 持ち込みライブラリのテンプレート。現在は `small_template.hpp` を include 検査に使用 |
| `library/` | 証明とテストを終えた公開 C++ 部品とメタデータ |
| `experiments/` | 未証明の試作。公開対象外 |
| `Proofs/`, `Proofs.lean` | Lean の仕様、生成された検証対象、証明 |
| `verifier/` | Clang 構文木から Lean の検証対象を作る基盤 |
| `tests/` | C++ の仕様テストとテンプレートを先に include した結合テスト |
| `benchmarks/` | 問題・ケース・制限に結び付く測定手順と結果 |
| `tools/` | 公開判定、依存解決、コード結合などの補助ツール |
| `.github/workflows/` | 単一 C++ 環境と Lean の CI |

将来の公開部品は一つの C++ ファイルと隣接する機械可読のメタデータを持つ。メタデータには依存先、仕様と証明の参照先、ソース識別情報を記録する。部品間の依存は非循環とし、include 検査の生成器はテンプレート、必要な依存先、対象部品の順に、一度ずつ include を出力する。公開 C++ は必要な標準ヘッダを明示し、専用の名前空間に本体を置く。ライブラリ内のテンプレートのマクロや `using namespace std` は使用してよい。検証用の注釈や専用構文は入れない。標準ライブラリ以外の外部ライブラリへの依存は認めない。

## 公開まで

1. 実装と仕様を `experiments/` で検討し、前提条件、境界条件、入力サイズ、依存先を定める。
2. C++ ソースを正本として、固定バージョンの Clang 構文木から検証対象を生成する。公開宣言一覧とヘッダ全体のハッシュを登録して照合し、対応可能な C++ 構文だけを公開対象にする。
3. すべての公開関数・型について、前提条件下の結果、停止、未定義動作の不在、時間と追加領域の計算量を Lean で証明する。時間は基本演算と採用した STL 操作契約から数える。乱択では各入力を固定した期待時間、最悪時の追加領域、必要なら誤答確率の上界を証明する。
4. ライブラリ内のテンプレートを最初に include した C++ テストを実行する。依存順の include と全部品を同時に include した結果もコンパイルして確認する。
5. 対応先とソース変更の検出、証明、テスト、依存グラフ、結合結果のすべてが CI を通ってから `library/` へ移す。`Proofs.lean` の import と登録済み証明の一致も検査する。`sorry`、未説明の公理、手書きの同等アルゴリズムの証明だけでは公開条件を満たさない。

`tools/public.py` は公開部品とメタデータ、依存グラフ、参照ファイル、Lean import、テスト・検証器の登録漏れを検査し、テンプレートと部品を順に include する C++ を生成する。共有の検証基盤は `verifier/support.toml` に登録し、Lean import とファイルを照合する。複数部品が同じ bridge を使う登録も許容する。`tools/check_public.py` は TOML に登録した全部品の C++ テスト、入出力ケース、include 結合結果、AST bridge を実行し、ローカル測定結果が Git に追跡されていないことも確認する。既定のローカル実行と CI は共有検査、新規ビルド、公理依存、定理文と定義の保持、`leanchecker --fresh` と独立カーネル nanoda の検査を行う。[検査方針と許可公理の管理](proof_security.md) を参照する。CI の C++ と AST bridge は同じ GCC 13.3.0 コンテナ内で実行する。

共通状態変換を使う部品は `translation = "state_ir"`、生成モデルの名前空間、仕様文書と共通 bridge を登録する。部品別のレビュー済み AST 指紋は持たず、生成 Lean の全文を照合する。問題と制限が未定の固定幅スカラー部品に、架空の入力長上限や測定用ファイルを必須としない。`sanitizers = true` の C++ テストは通常実行に加えて ASan/UBSan でも実行する。ローカルの ptrace 制約により LeakSanitizer は無効にし、アドレスと未定義動作の検査は失敗時に停止させる。

テストケースの内容は生成スクリプトまたは専用テキストファイルに置く。TOML と YAML にはケース本文を含めず、必要なファイルへの参照先だけを置く。テストと CI の実行経路はコンテストサイトへ通信しない。問題データの取得や更新は別の明示的な作業として扱う。 入力は `in/*.txt`、期待出力は `out/*.txt` に統一する。

`tools/check_public.py` は起動時に Linux の seccomp でソケット通信を禁止する。この制限はコンパイラ、C++ テスト、AST bridge、Lean の子プロセスにも継承され、制限を設定できない環境では検証を止める。CI はツールを準備してからこの検証コマンドを実行し、公理監査も `tools/offline.py` 経由で行う。セットアップと Release 更新に必要な GitHub 等への通信は検証処理と分離する。

## ヘッダのみの配布

`tools/package_headers.py` は登録済み公開ソースのハッシュを照合し、`library/` 内の `.hpp` だけを相対パスを保持した ZIP にする。ローカル include が配布物の外を参照する場合は拒否する。`tools/check_header_package.py` は収録内容を照合し、展開したヘッダのみでコンパイルできることを確認する。公開テンプレートも全検証完了後に `library/` 内へ配置する。

CI は全件gate（`check_public.py --mode all`）を実行時間のため分割する。`verify-shard` の16ジョブが最終監査以外の全検査を`--mode tests --shard I/16` で分担し、`verify-audit` が最終監査（`--mode audit`）と配布ZIPの検査を行う。全ジョブの成功をもって全件gateの成功とする。分担は `tools/ci_shards.py` がタスク名と `tools/ci_weights.json`（CIで測った秒数）だけから最長処理時間順に決めるので、各ジョブが同じ分割を計算し、各検査はちょうど1回実行される。単独で長いテストファイルは `split_methods` に挙げ、unittest のメソッド単位の検査に分ける。重みは CI のジョブログから `python3 tools/ci_shards.py update LOG...` で更新し、`python3 tools/ci_shards.py plan 16` で各ジョブの見積もりを確かめる。Lake はモジュールのビルドを Lean のスレッドプールで実行するため、`LEAN_NUM_THREADS=1` ではモジュールを1つずつビルドする。CI は `PROOF_BUILD_THREADS` にコア数を与え、証明のビルドだけを並列にする（検査結果は変わらない）。

main push の CI 検証と公理監査が成功した後に、Release 更新専用ジョブが固定タグ `headers` と asset `library-hpp.zip` を更新する。PR や手動実行では Release を更新しない。更新ジョブは直列化し、main が既に別コミットに進んでいる場合は旧コミットによる上書きを行わない。配布元コミットは Release 本文に記録する。利用者は asset の ZIP を取得すればよく、リポジトリ全体の clone は必要ない。

同名 asset の更新には [GitHub CLI の `gh release upload --clobber`](https://cli.github.com/manual/gh_release_upload) を使う。通信禁止には [libseccomp のフィルタ](https://man7.org/linux/man-pages/man3/seccomp_load.3.html) を使う。

## 信頼境界

証明は、固定した C++ フロントエンドとソースから検証対象への変換、コンパイラ、使用する C++ 標準ライブラリ操作の契約が正しいことを前提にする。STL の契約は使用する操作ごとに結果、前提条件、時間・領域の費用を記録し、呼び出し側で前提条件を証明する。STL の「平均計算量」を使う場合は、その平均の仮定を個別に記す。仮定を示せない場合は最悪計算量を使う。


乱択アルゴリズムの証明で独立一様な抽選を用いる場合、それは明示的な信頼前提であり、C++ の乱数エンジンから無条件に導かれる保証ではない。各証明が利用する前提と、検証器・ツールチェーンの版を追跡する。

## コンパイルと実測

標準の C++ コンパイル確認環境は GCC 13.3.0、`-std=c++17 -O2 -Wall -Wextra -pedantic` の一つとする。CI は GCC 13.3.0 コンテナ内で C++ と AST bridge と Lean を実行し、Lean は `lean-toolchain` の版を使う。ローカルにも GCC 13.3.0 と同じ Lean 版を要求する。4サイトのコンパイラ設定は同一ではないため、この確認は各サイトでの動作保証を意味しない。サイト固有の確認をした場合は環境と結果を個別に記録する。

実測は問題、入力ケース、制限時間・メモリ制限が定義された場合に行う。小さな固定ケースは保存し、大きなケースは出典・生成方法・検証用の値を残す。実行環境、コンパイラ、オプション、実装、入力規模、測定方法、時間・メモリを記録し、候補の優劣が規模によって変わる場合は規模別に示す。測定環境情報と実測値は Git の追跡対象外である `benchmarks/local/` に保存し、リポジトリには測定手順と入力の確認値を残す。性能比較には管理した測定環境を使い、通常の GitHub Actions ランナーの数値を採用しない。対応する問題がなく未測定でも、証明とテストを満たせば公開できる。

この環境はコンテスト参加用 VM と隔離されている。この環境からコンテストへ提出しない。問題やテストケースの取得・利用では各サイトのルールを守る。

## 参照

- [Lean の Lake 設定](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
- [lean-action](https://github.com/leanprover/lean-action)
- [AtCoder の言語一覧](https://img.atcoder.jp/file/language-update/2025-10/language-list.html)、[Codeforces のコンパイル設定](https://codeforces.com/blog/entry/121114)、[AOJ のシステム情報](https://onlinejudge.u-aizu.ac.jp/system_info)、[Library Checker の言語設定](https://github.com/yosupo06/library-checker-judge/blob/master/langs/langs.toml)
