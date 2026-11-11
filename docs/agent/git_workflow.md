# Git ワークフロー

## 変更前

1. `git status --short --branch` と `git diff` で既存の変更、ブランチ、作業範囲を確認する。ユーザーの変更を上書きしない。
2. リポジトリの `AGENTS.md`、このディレクトリの教訓、対象の CI 定義を読む。

## コミット前

1. 変更に関係する検証を実行する。公開部品なら `python3 tools/check_public.py --timeout-seconds N` で（既定は 5 分の入力キャッシュ保持期間の 80% である 240 秒。全件はローカルで1時間以上かかるので N に十分大きな値を指定し、バックグラウンドで実行する。CI は同じ全件gateを16ジョブと最終監査ジョブに分けて並列に実行する（`docs/architecture.md`））登録済み全部品の公開判定、AST 対応、Lean ビルドと `leanchecker`、C++ テスト、入出力ケース、テンプレートを先に include した結合結果のコンパイルを確認する。CI の公理監査も結果を見る。
2. CI の実行シェルと GCC 13.3.0 コンテナを確認する。`sh` のステップでは Bash 専用構文を使わず、必要な場合は CI でシェルを明示する。
3. 測定環境情報と実測値を `benchmarks/local/` に保存する。`git check-ignore` で除外を確かめる。
4. 対象ファイルをステージする。`git diff --cached --check`、`git diff --cached --stat`、`git diff --cached --name-only`、必要な内容確認で意図しないファイルやローカル情報がないことを確認する。
5. コミット後にコミット ID と `git status --short --branch` を確認する。

## push と GitHub Actions

### push の粒度

- ユーザー指定により、`experiments/` の原本1ファイルの移植完了をpushの単位とする。変更行数やローカルcommit数では判断しない。
- 対象の原本パスを明示し、元のAPI・機能・汎用性を保持した公開側への移植、C++由来の検証対象生成、Leanでの結果・停止・未定義動作不在・時間と追加領域の検証、C++テストとテンプレート先行include、必要な登録・文書・台帳の確認をそのファイル全体で完了させる。有限具体化や一部のfieldモデルだけの成功をファイル全体の完了としない。
- 変換器の機能追加、不具合修正、部分証明、handoff更新だけの段階ではpushしない。必要なローカルcommitは保持し、1ファイルの移植完了時にまとめて送る。
- 完了した移植単位でも、push前の全件検証・機密情報検査・差分確認と、毎回の手動承認は省略しない。push後のCIと配布物の確認も当該移植単位の作業に含める。

### 実行と確認

1. このプロジェクトの `git push` は `.codex/rules/git-push.rules` で毎回ユーザーに承認を求める。`approvals_reviewer = "user"` をプロジェクト設定に置く。Codex は信頼済みプロジェクトのルールを起動時に読み込むため、設定後は Codex を再起動する。上位の禁止ルールが優先される場合は push できない。権限・自動承認レビューに拒否されたら、コマンドの書式やツールを変えて回避せず、未 push の状態と理由を報告する。
2. push に成功したら、**そのコミット ID** に対応する GitHub Actions 実行を調べる。例: `gh run list --repo RTnF/CompProgLibraryGenerated --commit <SHA> --json databaseId,status,conclusion,url`。
3. 実行中なら完了を待つ。例: `gh run watch <run-id> --repo RTnF/CompProgLibraryGenerated --exit-status`。実行が見つからない場合も成功とみなさず、ワークフローのトリガー、対象ブランチ、反映待ちを確認する。
4. 失敗したら `gh run view <run-id> --repo RTnF/CompProgLibraryGenerated --log-failed` で原因を確認し、修正・ローカル検証・コミット・push をやり直す。新しいコミットの Actions 結果まで確認する。
5. 最終報告には、push したコミット、Actions の結果、未解決の失敗や確認不能な理由を明記する。push が成功しただけで作業完了と報告しない。
