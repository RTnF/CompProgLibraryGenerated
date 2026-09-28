# Git ワークフロー

## 変更前

1. `git status --short --branch` と `git diff` で既存の変更、ブランチ、作業範囲を確認する。ユーザーの変更を上書きしない。
2. リポジトリの `AGENTS.md`、このディレクトリの教訓、対象の CI 定義を読む。

## コミット前

1. 変更に関係する検証を実行する。公開部品なら `tools/public.py`、対応する `verifier/*_bridge.py`、Lean ビルドと `leanchecker`、C++ テスト、貼り付け後のコンパイルを確認する。
2. CI の実行シェルとコンテナを確認する。`sh` のステップでは Bash 専用構文を使わず、必要な場合は CI でシェルを明示する。
3. 測定環境情報と実測値を `benchmarks/local/` に保存する。`git check-ignore` で除外を確かめる。
4. 対象ファイルをステージする。`git diff --cached --check`、`git diff --cached --stat`、`git diff --cached --name-only`、必要な内容確認で意図しないファイルやローカル情報がないことを確認する。
5. コミット後にコミット ID と `git status --short --branch` を確認する。

## push と GitHub Actions

1. このプロジェクトの `git push` は `.codex/rules/git-push.rules` で毎回ユーザーに承認を求める。`approvals_reviewer = "user"` をプロジェクト設定に置く。Codex は信頼済みプロジェクトのルールを起動時に読み込むため、設定後は Codex を再起動する。上位の禁止ルールが優先される場合は push できない。権限・自動承認レビューに拒否されたら、コマンドの書式やツールを変えて回避せず、未 push の状態と理由を報告する。
2. push に成功したら、**そのコミット ID** に対応する GitHub Actions 実行を調べる。例: `gh run list --repo RTnF/CompProgLibraryGenerated --commit <SHA> --json databaseId,status,conclusion,url`。
3. 実行中なら完了を待つ。例: `gh run watch <run-id> --repo RTnF/CompProgLibraryGenerated --exit-status`。実行が見つからない場合も成功とみなさず、ワークフローのトリガー、対象ブランチ、反映待ちを確認する。
4. 失敗したら `gh run view <run-id> --repo RTnF/CompProgLibraryGenerated --log-failed` で原因を確認し、修正・ローカル検証・コミット・push をやり直す。新しいコミットの Actions 結果まで確認する。
5. 最終報告には、push したコミット、Actions の結果、未解決の失敗や確認不能な理由を明記する。push が成功しただけで作業完了と報告しない。
