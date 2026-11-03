# STL 契約の導入計画（設計メモ。段階 1 まで実装済み）

目的: `std::sort`、`std::unique`、`std::lower_bound`、`std::pair`、`std::priority_queue`、`std::map`/`std::set` などを使う `experiments/` のヘッダー（`sort_util`、`interval_union`、`element_count`、`search_util`、graph 系、セグメント木の一部）を検証できるようにする。方針は `docs/trust_policy.md` の「1. 標準ライブラリの契約」に従う。この文書は、実装前に分かったことと、決めるべき点、段階を残す。

## 1. 契約を「公理」にするか「モデルの定義」にするか

`docs/trust_policy.md` は、契約を別区分（`stl_contract`）の Lean の公理として置くとしている。実際に必要な形を調べると、次のとおり。

- 結果の値（並べ替えの結果、`lower_bound` の位置、`unique` 後の列）は、**Lean の定義**で書ける。たとえば整数の `std::sort` の結果は昇順の並べ替えとして一意なので、`List.mergeSort` で定義でき、「昇順」「並べ替え」はコアの定理で証明できる。公理は不要。信頼するのは「C++ の `std::sort` がこの定義と同じ結果を返す」という対応だけで、これは `NStmt` の各文（`reserve`、`append` など）の意味を定義で与えているのと同じ種類の信頼である。
- 計算量（比較回数 O(n log n)）は、モデルの仕事量の課金（`charge`）として定義に埋め込む。これは標準規格の要求（C++17 [alg.sort]）に基づく仮定で、証明できない。公理に近いのはこちら。
- 比較関数が狭義弱順序であること、`lower_bound` の範囲が整列済みであることなどの前提は、定理の前提（または `assert` の検査）として扱う。

提案: 値の意味は定義、計算量の上界は `stl_contract` 区分の公理（名前・文言のハッシュ・根拠の規格条項を `verification/stl_contracts.json` に登録）にする。公理を最小にでき、レビューの対象も計算量の 1 行ずつに絞れる。方針を変える場合は利用者の確認が要る。

## 2. IR の拡張

`Proofs/CppNestedProgram.lean` の `NStmt` に文を足す必要がある（例: `sortVec (container) (ty)`、`uniqueVec`、`eraseTail`、式として `lowerBound`）。`NStmt` を参照する Lean ファイルは約 39 個あり、`CppNestedProgram` はほぼ全証明の上流にあるため、変更のたびに全体の再ビルドが要る（`nice` を付けて数十分）。反復回数を減らすため、次の順で進める。

1. まず `NStmt` の新しいコンストラクタを、意味を `none`（未対応）で追加し、既存の証明が壊れる箇所（網羅的な `match`/`cases`）を洗い出す。
2. 壊れた箇所に「新しい文は結果を変えない」旨の補題を足して直す（`pexec`/`pexecW` は `| _ => none` で済む想定）。
3. 意味（`NStmt.run`）を定義し、フレーム不変条件への影響（`FW`、storage の仕事量、ピーク）を補題にする。書き込み後の vector 内容は `sort` の結果。
4. `VecKitW` に `pstmtW_sort_ok` を足し、`pexecW` の枠組み（`soundW`）に接続する。

## 3. 変換器の拡張

- `verifier/vector_stl.py`: 標準宣言の同一性の検査（コンパイラの probe）を `std::sort`/`unique`/`lower_bound` に広げる。既存の `push_back` などと同じ方式。
- `verifier/nested_ir.py`: 呼び出し式 `std::sort(v.begin(), v.end())` を `sortVec` に、`v.erase(std::unique(v.begin(), v.end()), v.end())` を `uniqueVec` + `eraseTail` に、`std::lower_bound(v.begin(), v.end(), x) - v.begin()` を式に変換する。比較関数が既定（`<`）の場合だけ受理する。ラムダの比較関数は別の段階。

## 4. 最初の消費者

`array/sort_util.hpp` の `compress`（座標圧縮）。`sort`、`unique`、`erase`、`lower_bound` を 1 つずつ使うので、4 つの契約が揃う。ただし `std::pair` を返す `counts`、ラムダを使う `arg_sort` は後。

## 5. 段階

（段階 1 は 2026-10-11 に完了: `Proofs/StlContracts.lean`、`verification/stl_contracts.json`、`tools/proof_security.py` の `load_contracts`/`contract_dependents`、`audit_source` が登録済みの契約ファイル内だけで `axiom` を許可、`check_proof_security.py` が契約を許可して依存する定理の件数を出力、`tests/test_proof_security.py` に負例。最初の契約は `sort_comparisons_bound`（`std::sort` の比較回数の上界）。）

1. 契約の登録: `verification/stl_contracts.json`、`tools/proof_security.py` に `load_contracts`、`audit_dependencies` が契約公理を許可し、依存する定理の一覧を出す。`check_proof_security.py` の nanoda の `permitted_axioms` に契約公理を加える。
2. `NStmt.sortVec` と意味、既存証明の修復（上の 2.）。
3. `compress` 以外の最小の消費者（`sort` して `lower_bound` するだけの関数）で、変換器から定理までを通す。
4. `unique`/`erase`、`compress`。
5. `std::pair`、ラムダ、`priority_queue`、`map`/`set` は別の計画にする。

見積り: 段階 1〜3 で数日。各段階の確認は、全件検査を 1 回（5 分以内に収まる差分方式。ただし `CppNestedProgram` を変えた直後は広範囲の再ビルドが要るので、`lake build` を単独で先に通す）。
