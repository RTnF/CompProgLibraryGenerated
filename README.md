# CompProgLibraryGenerated

C++ のコピー利用を主とする競技プログラミング用ライブラリです。公開部品の C++ ソースを正本として Lean で検証し、問題とテストケースが定義されている場合には性能も測定します。

公開部品は [整数のマージソート](library/merge_sort.hpp) と [連想配列](library/associative_array.hpp) です。Lean で各部品の仕様と費用・領域モデルの上界を検証しています。C++ と Lean の対応には、固定した Clang 構文木に対するソース固有の信頼済み変換を用います。この変換の意味的な正しさと STL 契約は証明の信頼前提です。

ヘッダのみの配布物は [library-hpp.zip](https://github.com/RTnF/CompProgLibraryGenerated/releases/download/headers/library-hpp.zip) です。自動配布はこのワークフロー変更を main に push した後に開始します。ZIP 内は `library/` 以下の `.hpp` だけで、clone は不要です。main への push ごとに全検証成功後の版へ更新し、[Release](https://github.com/RTnF/CompProgLibraryGenerated/releases/tag/headers) の本文に配布元コミットを記録します。GitHub が自動表示する「Source code」ではなく `library-hpp.zip` を取得してください。

- [構造とワークフロー](docs/architecture.md)
- [作業指針](AGENTS.md)
- [マージソートの証明と測定](docs/merge_sort.md)
- [連想配列の証明と測定](docs/associative_array.md)
- 検査に使うテンプレート: [small_template.hpp](experiments/library/cpp/template/small_template.hpp)

ローカルの確認（GCC 13.3.0 と `lean-toolchain` の Lean が必要）:

```sh
python3 tools/check_public.py
```

検証は Linux と libseccomp を必要とし、ソケット通信を禁止した状態で C++・AST・Lean の検査を実行します。テストと CI はコンテストサイトと通信しません。CI のツール取得と Release 更新は検証処理から分離します。ケース内容は生成スクリプトまたは専用テキストファイルに置き、TOML/YAML には参照先だけを記録します。 入力は `in/*.txt`、期待出力は `out/*.txt` に統一する。

配布物をローカルで確認するには次を実行します。

```sh
python3 tools/package_headers.py --output /tmp/library-hpp.zip
python3 tools/check_header_package.py /tmp/library-hpp.zip
```

Lean 4.34.1 は `lean-toolchain` で固定しています。この環境では `elan` と Lean を `.tools/elan/` にインストール済みです。シェル設定は変更していません。リポジトリのルートで次を実行できます。

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --version
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lake build
```

別の環境では[公式の elan 導入手順](https://lean-lang.org/install/manual/)で elan を入れます。検証コマンドは登録済み全コンポーネントの C++ テスト、入出力ケース、テンプレートを先に include した結果、AST 対応、Lean ビルドと `leanchecker` を確認します。CI では同じ検証対象に加え、公理監査を行います。`.tools/` と `.lake/` は Git 管理対象外です。Lean の依存関係は `lake-manifest.json` に記録します。

この環境からコンテストへコードを提出しません。
