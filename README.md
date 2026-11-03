# CompProgLibraryGenerated

C++ のコピー利用を主とする競技プログラミング用ライブラリです。公開部品の C++ ソースを正本として Lean で検証し、問題とテストケースが定義されている場合には性能も測定します。

公開部品は [safe_mod](library/safe_mod.hpp)、[floor_sum_unsigned](library/floor_sum_unsigned.hpp)、[floor_sum](library/floor_sum.hpp)、[bit_width_u64](library/bit_width_u64.hpp)、[doubling](library/doubling.hpp)（二重化テーブル）、[enumerate_quotients](library/enumerate_quotients.hpp)（商の列挙）、[search_util](library/search_util.hpp)（`vector<int>` の区間内の個数）、[sort_util](library/sort_util.hpp)（逆置換）、[mod61](library/mod61.hpp)（ローリングハッシュの法 2^61-1 の演算）、[extrema](library/extrema.hpp)（`long long` の chmax / chmin）です。Lean で各部品の仕様と費用・領域モデルの上界を検証しています。すべての公開部品は型付き AST から共通変換器で生成します。signed 版は GCC 13.3 / x86_64 Linux / C++17 / LP64 の変換契約下で、数学的な総和が signed64 に収まる場合は正確な値、範囲外では64 bit剰余を signed に復号した値を返します。floor_sum_unsigned は n<2^32、0<m<2^32 の全入力で、床関数の和の64 bit剰余、停止・安全性、O(log m) の時間と O(1) の追加領域を検証しています。C++ から Lean への変換の意味的な正しさと STL 契約は証明の信頼前提です。

ヘッダのみの配布物は [library-hpp.zip](https://github.com/RTnF/CompProgLibraryGenerated/releases/download/headers/library-hpp.zip) です。自動配布はこのワークフロー変更を main に push した後に開始します。ZIP 内は `library/` 以下の `.hpp` だけで、clone は不要です。main への push ごとに全検証成功後の版へ更新し、[Release](https://github.com/RTnF/CompProgLibraryGenerated/releases/tag/headers) の本文に配布元コミットを記録します。GitHub が自動表示する「Source code」ではなく `library-hpp.zip` を取得してください。

- [構造とワークフロー](docs/architecture.md)
- [作業指針](AGENTS.md)
- [許可公理と証明の検査](docs/proof_security.md)
- 検査に使うテンプレート: [small_template.hpp](experiments/library/cpp/template/small_template.hpp)

ローカルの確認（GCC 13.3.0、`lean-toolchain` の Lean、Rust/Cargo が必要）:

```sh
# 初回だけ、検査経路とは別に固定ツールと依存を取得する。
python3 tools/prepare_proof_checkers.py --fetch
python3 tools/prepare_proof_checkers.py
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

別の環境では[公式の elan 導入手順](https://lean-lang.org/install/manual/)で elan を入れます。検証コマンドは登録済み全コンポーネントの C++ テスト、入出力ケース、テンプレートを先に include した結果、AST 対応、新規 Lean ビルド、公理依存、定理文・定義の保持、`leanchecker --fresh` と独立カーネル nanoda を確認します。CI も同じ検証経路を使います。公理の定義は許可項目または定義が変わった場合にだけ検査します。`.tools/` と `.lake/` は Git 管理対象外です。Lean の依存関係は `lake-manifest.json` に記録します。

この環境からコンテストへコードを提出しません。
