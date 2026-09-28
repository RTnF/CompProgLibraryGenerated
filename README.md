# CompProgLibraryGenerated

C++ のコピー利用を主とする競技プログラミング用ライブラリです。公開部品の C++ ソースを正本として Lean で検証し、問題とテストケースが定義されている場合には性能も測定します。

最初の公開部品は [整数のマージソート](library/merge_sort.hpp) です。標準ライブラリのソート関数を使わず、Lean で整列・順列保存と時間・領域の上界を証明しています。C++ と Lean の対応には、固定した Clang 構文木に対する[専用の信頼済み変換](verifier/merge_sort_bridge.py)を用います。この変換の意味的な正しさと STL 契約は証明の信頼前提です。

- [構造とワークフロー](docs/architecture.md)
- [作業指針](AGENTS.md)
- [マージソートの証明と測定](docs/merge_sort.md)
- 貼り付け先の見本: [a.cpp](a.cpp)

ローカルの確認（順番に実行）:

```sh
python3 tools/public.py
python3 verifier/merge_sort_bridge.py
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lake build
g++ -std=c++17 -O2 -Wall -Wextra -pedantic tests/merge_sort.cpp -o /tmp/merge-sort-test
/tmp/merge-sort-test
python3 tools/public.py --assemble merge_sort --output /tmp/merge-sort-pasted.cpp
g++ -std=c++17 -O2 -Wall -Wextra -pedantic -fsyntax-only /tmp/merge-sort-pasted.cpp
```

Lean 4.34.1 は `lean-toolchain` で固定しています。この環境では `elan` と Lean を `.tools/elan/` にインストール済みです。シェル設定は変更していません。リポジトリのルートで次を実行できます。

```sh
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lean --version
ELAN_HOME="$PWD/.tools/elan" .tools/elan/bin/lake build
```

別の環境では[公式の elan 導入手順](https://lean-lang.org/install/manual/)で elan を入れ、このリポジトリで `lake build` を実行すると `lean-toolchain` の版が選ばれます。`.tools/` と `.lake/` は Git 管理対象外です。Lean の依存関係は `lake-manifest.json` に記録します。

この環境からコンテストへコードを提出しません。
