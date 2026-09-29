# CompProgLibraryGenerated

C++ のコピー利用を主とする競技プログラミング用ライブラリです。公開部品の C++ ソースを正本として Lean で検証し、問題とテストケースが定義されている場合には性能も測定します。

公開部品は [整数のマージソート](library/merge_sort.hpp) と [連想配列](library/associative_array.hpp) です。Lean で各部品の仕様と費用・領域モデルの上界を検証しています。C++ と Lean の対応には、固定した Clang 構文木に対するソース固有の信頼済み変換を用います。この変換の意味的な正しさと STL 契約は証明の信頼前提です。

- [構造とワークフロー](docs/architecture.md)
- [作業指針](AGENTS.md)
- [マージソートの証明と測定](docs/merge_sort.md)
- [連想配列の証明と測定](docs/associative_array.md)
- 貼り付け先の見本: [a.cpp](a.cpp)

ローカルの確認（GCC 13.3.0 と `lean-toolchain` の Lean が必要）:

```sh
python3 tools/check_public.py
```

Lean 4.34.1 は `lean-toolchain` で固定しています。この環境では `elan` と Lean を `.tools/elan/` にインストール済みです。シェル設定は変更していません。リポジトリのルートで次を実行できます。

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --version
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lake build
```

別の環境では[公式の elan 導入手順](https://lean-lang.org/install/manual/)で elan を入れます。検証コマンドは登録済み全コンポーネントの C++ テスト、入出力ケース、貼り付け結果、AST 対応、Lean ビルドと `leanchecker` を確認します。CI では同じ検証対象に加え、公理監査を行います。`.tools/` と `.lake/` は Git 管理対象外です。Lean の依存関係は `lake-manifest.json` に記録します。

この環境からコンテストへコードを提出しません。
