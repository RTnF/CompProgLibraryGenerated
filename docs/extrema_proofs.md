# chmin・chmax の具体化の証明

`Proofs/ExtremaInstances.lean` は `tests/imports/update_extrema_instantiations.cpp` の固定 Clang AST から、共通の `state_ir.py` で生成する。`tools/check_extrema_proofs.py` が生成結果の全文を照合する。手書きの同等アルゴリズムをモデルに置き換える経路は使わない。元の二系列との AST / IR の一致は `tests/test_state_ir.py` で引き続き確認する。

`Proofs/ExtremaProofs.lean` はこの生成モデルを import し、`chmin<int,int>`、`chmax<int,int>`、`chmin<unsigned int,unsigned int>`、`chmax<unsigned int,unsigned int>` の4具体化について証明する。一般の型条件を持つ主テンプレート全体の証明ではない。

## 定理の範囲

参照先の値は、符号付き32 bit または符号なし32 bit の全表現可能範囲を扱う。小規模なテスト値に限った定理ではない。メモリは参照先を先頭に置いた正規化した配置とし、無関係な任意の後続セル `tail` を持ってよい。

異なる2セルを参照する定理は、`chmax` が大きい方、`chmin` が小さい方を左辺に残し、右辺と後続セルを変えないことを証明する。返り値は厳密な比較条件が成り立つとき1、その他は0である。同じセルを参照する定理は、全入力で0を返し、メモリを変えないことを証明する。

定理は有効な型の入力の下で `call = some result` を示す。したがってモデル内の読み出し・参照の型と境界・書き込み・変換・return の検査を通る。評価器自体は構造的な再帰で定義される。これはモデルの成功と停止の保証であり、C++ のオブジェクトの寿命や実アドレスの正当性は、状態変換器の呼び出し側の契約と信頼境界に従う。

成功時の抽象仕事量は更新時9、非更新時7、最大追加領域は5であることを結果と同時に証明する。`*_bounds` の4定理は、結果の存在、仕事量が9以下、追加領域が5以下であることを示す。単位と C++ の操作・領域への対応は [状態変換器](state_converter.md) に記録した契約に従う。実測時間・実スタック使用量の定理ではない。

抽象メモリの任意のアドレス配置への拡張は下記の ExtremaReferences で扱う。C++ の参照の寿命・所有権と初期化済みオブジェクトへの対応は呼び出し側の信頼前提であり、異なる型やユーザー定義型を含む主テンプレートの証明は未完了である。候補は `experiments/verification/template/update_extrema.hpp` に保持し、公開済みとはしない。

## 検査

```sh
python3 tools/check_extrema_proofs.py
python3 tests/test_extrema_proofs.py
python3 tools/check_public.py
```

モデルの生成照合、全入力の Lean 定理、元の二系列と候補の具体化 IR の一致、境界・エイリアスの C++ / Lean 比較は全公開検証の経路に登録する。比較を `<` から `<=` に変えた C++ から共通変換器でモデルを生成し、元の全入力の証明が通らないことを別の一時ファイルで検査する。

`Proofs.lean` は生成モジュールと証明を import し、Lean ビルド・`leanchecker`・CI の公理監査の対象にする。未説明の公理や `sorry` を追加していない。具体化の証明を主テンプレート全体の完了として台帳に反映しない。

## 任意の caller メモリと参照アドレス

`Proofs/ExtremaReferences.lean` は先頭配置への制限を除く。memory[p] と memory[q] に同じ型の範囲内の初期値 a,b があることだけを要求し、p,q、caller の長さ、その他のセルは任意でよい。p=q も許す。未参照セルの型や値の有効性を全体の仮定にしない。

`schema_call` は型 Ty と条件式をパラメータにした意味論の補題で、実際の bindArgument、式評価、代入、return、scope の実行を接続する。4生成プログラムをこの補題の形へ rfl で照合し、`chmax_signed`、`chmin_signed`、`chmax_unsigned`、`chmin_unsigned` は生成済みのソースプログラムそのものの呼び出しを扱う。結果は比較が成立した時だけ1、それ以外は0。更新時は destination p の値だけ b に変え、非更新時は元の memory を保持する。仕事量は9または7、追加領域は5で、正常終了・成功する型検査を同時に示す。

`update_frame` はメモリ長、p の新値、q の元の値、p 以外のすべてのセルを保持することを証明する。`max_alias` と `min_alias` は同じセルを渡すと0を返し、メモリを保持し、費用7・領域5となる。これらの意味論補題は型 Ty をパラメータにするが、未変換の主テンプレートやユーザー定義型の証明を代替するものではない。元 C++ との生成対応を示しているのは現在の4具体化である。

`tests/test_extrema_references.py` は signed/unsigned の32 bit境界値、参照順序の反転、中央の離れたセル、同一セルを含む210配置で両ヘルパー（計420呼び出し）を確認する。全入力補題、生成プログラムの計算、独立した値とメモリの期待結果、UBSan 付き C++ が一致した。未参照の caller セルを無効な型値にしたモデルでも保持を確認し、参照先の範囲外・型不一致・存在しないアドレスは拒否する。元の候補から再生成して4生成プログラムの全入力証明を再検査し、比較2種・代入・返却値の4改変を拒否する。

主テンプレートの構文生成は [template_converter.md](template_converter.md) に記録する。型パラメータと未解決の演算を保持する JSON IR を生成し、組み込み整数7型への具体化を Clang の実際の具体化と照合する段階まで進んだ。主テンプレート全体の量化した Lean 証明や98関数の結果・安全性・費用の証明を完了したとは扱わない。

整数族の Lean 具体化規則は CppTemplate と生成 IntegralExtrema に接続した。IntegralExtremaShape の4等式により、同じ型の int / unsigned int の具体化は上記の証明対象と定義上一致する。任意の混合型の結果・安全性・費用やユーザー定義型の契約は未完了である。詳細と196個の生成等式の検査は [template_converter.md](template_converter.md) を参照する。

IntegralExtremaExecution は主テンプレートから生成する7整数型の全組へ呼び出しの証明を拡張した。比較・更新の変換後の値、更新先だけの変更、同じ型の数学的 min/max と alias、仕事量12以下・領域7以下を扱う。GCC 契約は全型範囲で正常終了、checked は実行する signed 変換の成功を条件とする。784 Lean 呼び出し・392 UBSan 付き C++ 呼び出しと20拒否ケース、同一セルの92 Lean 呼び出し・46 C++ 呼び出し、4ソース改変の拒否を検査する。任意のユーザー定義型を持つ主テンプレートの完了・公開とはしない。
