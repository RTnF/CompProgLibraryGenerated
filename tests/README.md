# C++ テスト

各部品のテストは独立した基準（総当たり、`__builtin_clzll` など）と照合し、ライブラリ内の `small_template.hpp` を最初に include します。CI は依存順の include と、全部品を同時に include した結果もコンパイルします。

ケースの内容は生成スクリプトまたは専用テキストファイルに置き、TOML と YAML にはファイルの参照先だけを記録します。テストと CI はコンテストサイトと通信しません。 入力は `in/*.txt`、期待出力は `out/*.txt` に統一する。

## 検査の高速化（結果のキャッシュと並列実行）

`python3 tools/check_public.py` は、成功した検査の結果を `.cache/check-results.json`（Git の管理外）に残し、前回成功したときに読んだファイルが変わっていなければ再実行しない。

- Python の検査（生成器との一致、`tests/test_*.py`、`tools/check_*.py`）の依存は自動で記録する（`tools/trace/sitecustomize.py` が読み込んだファイル、一覧したディレクトリ、サブプロセスの引数のファイル、読み込んだモジュールを記録し、`tools/check_cache.py` がそれらが include する C++ ヘッダーも辿る。`lake`/`lean` を呼ぶ検査は、引数のモジュール名や渡した `.lean` ファイルの `import` から、実際に使う `Proofs` のモジュールとその推移的な import だけに依存する。引数なしの `lake build` と `Proofs` ルートはプロジェクト全体に依存する）。
- C++ のテストは、テストと対象ヘッダーが（引用符つきの `#include` を辿って）依存するファイルで判定する。コンパイラのフラグとバージョンも鍵に入れる。
- 証明の安全性検査（`check_proof_security.py`）は `Proofs/`、`verification/`、`lakefile.toml`、`lake-manifest.json`、`lean-toolchain`、検査ツール、公開部品の `.toml` が変わらなければ再実行しない。`lake build` は常に実行する（Lake が増分で処理する）。
- 独立した検査は並列に走る（`--jobs`、既定は 3）。プロセスの優先度は `nice 19` と `ionice -c3` に下げる。
- 失敗した検査の結果は保存しない。`--no-cache` で全件を再実行する。CI は新しいチェックアウトなので常に全件を実行する。
- 2026-10-09 の実測: 全件キャッシュ済みで約 2〜5 秒（キャッシュなしでは約 20 分、並列 2 の低優先度の実行。以前の逐次実行は約 1 時間）。

キャッシュは「前回成功時に観測した入力が同じ」という判定であり、観測できない入力（サブプロセスが内部で読むファイル、時刻や乱数）には依存しない前提である。疑わしいときは `--no-cache` を使う。

## 開発中の検査（短く、負荷を抑える）

全件検査（`python3 tools/check_public.py`、`--mode all`）は、証明の再構築・独立カーネル検査を含むため、冷えた状態で 20 分以上かかり、ディスクとCPUの負荷が大きい。**開発の繰り返しでは回さない**。次の順で絞る。

1. 部品の C++ テストと bridge の一致だけ（数秒）: `python3 tools/check_public.py --mode cpp --component NAME` と `--mode bridge --component NAME`（`--component` は繰り返せる）。
2. Lean の証明: `lake build Proofs.NAMECall`（変更のあるモジュールだけが再構築される）。
3. 文の登録: 公開定理を変えたら `python3 tools/regenerate_statements.py`。
4. 全件検査（ゲート）は、コミット前・まとまった作業の最後に 1 回だけ。`--jobs` の既定は 1（並列を増やすとディスク I/O が増える。WSL の VHDX は C ドライブにあり、過去に負荷で破損している）。

### 検査を 5 分以内に収める仕組み（2026-10-11）

- 証明セキュリティ検査（`tools/check_proof_security.py`）は差分方式にした。作業ディレクトリ `.cache/proof-security-scratch/`（`.gitignore` 済み）を使い回し、Lake の増分ビルドで変わった証明モジュールだけ再ビルドする。カーネルの再生（`leanchecker`）は、ソースまたは import した証明モジュールのハッシュが変わったモジュールだけ行う（記録は `.cache/proof-security-modules.json`）。Mathlib を含む全体の再生（`leanchecker --fresh Proofs`）は、ツールチェイン・Mathlib のピン・監査済みモジュール表のどれかが変わったときだけ行う。実測: 何も変えない場合 1 分 13 秒（初回の全構築は 11 分）。差分判定は git を使わず、ファイル内容のハッシュで行う。
- `verification/InspectEnvironment.lean` の作業リストへの追加が毎回リスト全体のコピーだった（2 次の計算量）。深さ優先に直して 211 秒から 29 秒になった。出力される宣言の集合は同じ（16916 件）。
- 1 つで 5 分を超える検査は分割して別々にキャッシュする（`tests/test_nested_ir_*.py`。元は `tests/test_nested_ir.py` の 4 テスト。オラクルとの照合は 3 つに分割し、3 つで全事例）。
- `check_public.py` の制限時間は 5 分（既定 240 秒）のまま。成功した検査はキャッシュされるので、生成器など広く依存される部品を変えた直後に限り、数回に分けて実行すれば前回の続きから進む。部品を足すだけなら 1 回で終わる。制限時間を延ばして通すことはしない。
- キャッシュ判定の精密化（2026-10-11）: (1) Python の import が作るディレクトリ一覧は、実際に import されたモジュール名と一致する項目だけを依存にする（`tools/trace/sitecustomize.py` の `i`/`n` 行、`tools/check_cache.py` の `import_dirs`/`names`）。`tests/` や `verifier/` に無関係なファイルを足しても、他の検査は無効にならない。同名のモジュールを置いて差し替える場合は検出される。 (2) bridge の検査は部品のメタデータだけを検証する（`tools/public.py` の `component(name)`）。レジストリ全体の検証は `check_public.py` の起動時に 1 回だけ行う。部品を足したときに全部品の bridge 検査がやり直しになるのを避けるため。

`test_union_find_bounds.py` は公開UnionFindの元の入力assertを検査する。複数のプロセス起動と異常終了を扱うため、support検査として登録し、ケースを `imports/union_find_bounds/in/cases.txt` と `out/cases.txt` に置く。生成LeanモデルのfaultとC++のSIGABRT、および正常な境界入力をASan/UBSanで照合する。

`test_union_find_original_api.py` は、元API/別カウンタ/全メソッドの経路圧縮を保つ実験候補と元の再帰実装を全状態で比較する。ケースはPythonの生成関数に置く。private配列・カウンタの比較用C++ハーネスだけを `-fno-access-control` でビルドし、ヘッダーは改変しない。共通生成Leanモデル、Pythonの再帰モデル、ASan/UBSan付きの元C++と候補C++を照合する。一般call証明完成とは区別する。

Doublingの変更検出では、値を変える変更はoracleの失敗を要求する。reserve(n)をreserve(0)へ変えた場合はgrowにより値が保たれるため、IR差分・値oracleの成功・元と変更後の実storage work/peakの差分を検査する。

vector_copy_irの生成実行はroot/行header両入力を扱い、借用した行への書込みとcaller aliasへの反映、readonly→mutable要求、stale epoch、owner/header不一致の拒否も確認する。

`test_ret_unit_ir.py`はvoid/constructorのbare returnで後続処理が停止し、local vectorを退去すること、元vector/scalar aliasへの更新、void method/void free callerのreturn式を生成モデルとnative UBSanで照合する。unit関数がscalar returnを返す不正なモデルはfaultを要求する。新命令とunit finishの一般補題はCppUnitReturnで確認する。

`test_class_default_arguments.py`は構築子・外部receiver methodの元宣言に属する既定式を生成Lean/native UBSanで照合する。全省略/一部省略/明示指定、scalar/void/const、対象GCCの整数変換、local退去、node IDを保って式だけを変えた不正な展開の拒否、省略時の副作用拒否と明示指定時の非評価を扱う。内部inlinerや任意の副作用のサポートを意味しない。

UnionFind の代入検査は、代入の線形仕事量とコピー後の5種類の通常操作列について、初期 potential を含む一般的な償却上界への接続も確認する。

const呼出しの同検査は `UfReadPrepareBudget` のcaller-only work/3peak、scalar上界のheap/履歴totalPeak非依存とscalarLive+式nodes+slot数+49の一般上界、sizeの成分要素数/同一成分判定/元ownerへの保持を追加確認する。

同検査の `test_readonly_world_and_multiple_owner_lifetimes` は `UfReadValues` の全buffer lookup/read/receiver更新と、scope 0/1 の2owner、有効epoch7/古いepoch6、別UFのmutable権限保持およびreadonly呼出し後の別UF uniteを確認する。scope終了やcopy export全体の完了とは区別する。

同検査は `Proofs/Generated/UnionFindPublicCompat.lean` と実fixtureからの生成全文も照合し、`Proofs/UfPublicSource.lean` を直接importする。通常5/const3methodの実receiver wrapper、両constructor export、元の全postcondition、readonlyの履歴rankからの対数work上界を型検査する。[証明対象と未完了事項](../docs/union_find_public_source.md)を参照する。公開headerの切替やimplicit lifetime全体の完了は意味しない。

`test_tree_order_dp.py` は `TreeOrderMath.TO.toTS` の一般証明をimportし、順序生成の結果から有効な木のDP前提を構成する例と、余分な非親子辺を持つ三角形の反例をLeanで確認する。`tree_full_dp.cpp` は実際の `tree_order` 出力を用いて全方位DPと素朴な高さ計算を比較する。[前提と接続範囲](../docs/tree_full_dp.md)を参照する。

- `test_beats_capacities.py`: Beatsの節点配列容量とDFSスタック容量の分離を確認する。n=32の実長さ(L=264、S=256)に旧Lensが適用できないことと、新しい容量条件から生成構築モデルの正常終了・表現を得ることをLeanで検査する。公開caller/allocation/全操作の検証完了を意味しない。

- `test_beats_wide_candidate.py`: 元のサイズ範囲を保つBeats構築候補を通常/ASan/UBSan、巨大配列なしの算術境界、実ASTからのLean型検査で確認する。構成子以外の全生成関数が公開版と同一であることも確認する。公開切替と候補全範囲の証明は未完了。
