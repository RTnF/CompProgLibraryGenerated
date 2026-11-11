# C++ から Lean への翻訳（新方式）

`docs/redesign_2026-11.md` の対応層である。公開ヘッダの C++ を、意味論を一度だけ定めた制限構文として読み、`verifier/lean_translate.py` が Lean の関数へ機械的に翻訳する。翻訳結果（`Proofs/Cpp/Gen/*.lean`）について、部品ごとの証明（`Proofs/Cpp/*.lean`）が正しさと計算量のオーダーを示す。C++ を文ごとに記号実行する証明は作らない。

## 意味論（`Proofs/Cpp/Prelude.lean`）

- 関数は `Proofs.Cpp.M := StateT Nat Option` の値になる。状態は tick 数、`none` は「正常に戻らない」（`assert` の失敗、`while` ループや再帰が `Cpp.fuel = 2^64` 回を超えること）を表す。正しさの定理は結果が `some` であることを含むので、停止も示す。
- 整数型（`int`、`long long` など符号付き）は `Int`。部品ごとに「入力と途中の値が型の範囲に収まる」を前提として一度述べ、各演算の範囲は証明しない。`/` と `%` は 0 方向への丸め（`Int.tdiv`/`Int.tmod`）、`&`・`|`・`^` は 2 の補数（Mathlib の `Int.land` などと同じ定義）、`<<` は `2^b` 倍、`>>` は算術シフト。
- 符号なし 32/64 bit 型（`unsigned`、`unsigned long long`、`std::uint64_t`、`size_t` など）は `UInt32`/`UInt64` で、折り返しを含めて C++ と同じ意味になる。符号付き・符号なしが混ざる演算は、翻訳器が C++ の通常の算術変換（幅と符号から共通の型を決める）を自分の型付けで再現し、明示的な変換を挟む（符号付き → 符号なしは `UInt64.ofInt` で 2^64 を法とする値、符号なし → 符号付きは値がそのまま入ることを前提とする）。`unsigned __int128` は 2^127 未満で使う前提で整数として扱う。`v.size()` は `Int`（非負）で、Clang が挿入する暗黙の `size_t` への変換は使わない。
- `bool` は `Bool`、`std::vector<X>` は `Array X`、`std::pair<A, B>` は `A × B`。
- テンプレート引数 `T` は Lean の型変数になり、使った演算だけを型クラス引数として要求する（`+` → `[Add T]`、`<` → `[LT T] [DecidableLT T]`、`T s = 0` → `[Zero T]`、整数から `T` への変換 → `[IntCast T]`、要素の読み出しと値初期化 → `[Inhabited T]`）。呼び出し先の要求も呼び出し元へ伝わる。証明は Mathlib の代数構造（`AddCommMonoid T` など）を仮定して述べる。値初期化（`std::vector<T>(n)`）は `default` で、`T` が数値のときに `default = 0` を仮定する定理がある。
- 範囲外の添字は C++ では未定義動作で、各部品の前提（添字が範囲内）で除く。モデルの `Cpp.get`/`Cpp.set` は全域関数にするために範囲外でも値を返すが（`default` を読む、書き込まない）、これは C++ の挙動の主張ではなく、定理と文書はこの値に依存しない。前提を満たす入力で範囲外アクセスが起きないことは、証明の中の添字の範囲と、サニタイザ付きテスト・差分テストで確かめる。
- C++ オブジェクトの寿命（コピー・ムーブ・破棄）とヒープ上の領域は扱わない。

## 翻訳の対象

| C++ | Lean |
| --- | --- |
| 自由関数・関数テンプレート | `def cp.f {T} [要求] (引数) : Cpp.M 出力` |
| クラス・クラステンプレート | `structure cp.C (T : Type)`（フィールド）と、メンバー関数ごとの関数 |
| const メンバー関数 | `cp.C.m (self : cp.C T) ... : Cpp.M R` |
| 非 const メンバー関数 | 出力に更新後の `self` を加える |
| コンストラクタ | `cp.C.init_<引数の型>`（重複がなければ `init`）。メンバー初期化子・既定のメンバー初期化子・値初期化の順 |
| 非 const 参照引数 | 出力に呼び出し後の値を加え、呼び出し側で書き戻す |
| 出力が複数 | 戻り値、参照引数（宣言順）、`self` の組 |
| 多重定義 | 名前に引数の型を付ける（`sum_int`、`sum_int_int`） |
| private メンバー関数 | 翻訳する。差分テストからは呼ばない |

文と式:

- `for (int i = a; i < b; i++)`（`<=`、`i--` と `>=`/`>` も）で、本体が `i` と上限の式の変数を変えず、上限が `size()` 以外の呼び出しを含まないもの → `for i in Cpp.range a b`（`Cpp.rangeDown`）。
- それ以外の `for`、`while` → `for _ in Cpp.forever do`（反復ごとに条件を調べて `break`）。`continue` の前に増分を実行する。
- 範囲 for（値または const 参照で、本体が範囲を変えないもの）→ `for x in v`。
- `if`/`else`、`return`、`break`、`continue`、局所変数の宣言（`let mut`）、代入、複合代入、`++`/`--`（文としてのみ）、`assert`（`Cpp.check`、失敗で `none`）、三項演算子（分岐に呼び出しを含まないもの）。
- 呼び出しは評価順に `let t ← f ...` として前に出す。`&&`/`||` の右辺と三項演算子の分岐の中の呼び出しは拒否する。
- 再帰は拒否する（定義の順序は呼び出し先が先）。

STL:

| C++ | Lean |
| --- | --- |
| `v.size()`、`v.empty()`、`v[i]`、`v.back()`、`v.front()` | `Cpp.size v`、`v.size = 0`、`Cpp.get v i`、`Cpp.back v`、`Cpp.get v 0` |
| `v[i] = x`、`v[i][j] = x`、`p.first = x` | `Cpp.set` の入れ子、組の更新 |
| `v.push_back(x)`、`v.emplace_back(x)`、`emplace_back(a, b)`（pair） | `v.push x` |
| `v.pop_back()`、`v.clear()`、`v.resize(n[, x])`、`v.assign(n, x)`、`v.reserve(n)` | `v.pop`、`#[]`、`Cpp.resize`、`Cpp.replicate`、（何もしない） |
| `std::vector<T> v(n[, x])`、`{a, b}`、コピー | `Cpp.replicate`、`#[a, b]`、同じ値 |
| `std::min`、`std::max`、`std::swap`、`std::abs` | `min`、`max`、入れ替え、`Int.natAbs` |

ここにない構文・型・関数は `Unsupported` として拒否する。拒否された実装は `experiments/` に置く。

## 計算量（tick）

翻訳結果は次の点で tick を加える: 関数の入口で 1、ループの反復ごとに 1、`push_back` で 1、長さ `n` の vector を作る・コピーする・`resize`/`assign` するときに `n`。各反復・各関数の本体のそれ以外の部分は定数個の操作なので、tick 数のオーダーが C++ の実行時間のオーダーになる。部品の定理は tick 数の明示的な上界（例: `x.size() + 1`）を示し、そこからオーダーが従う。

## 差分テスト（信頼境界）

翻訳器そのものの正しさは証明しない。代わりに `verifier/diff_harness.py` が、翻訳した関数のシグネチャから同じコマンド言語のインタプリタを C++（公開ヘッダを呼ぶ、ASan/UBSan 付き）と Lean（翻訳結果を `lean --run` で実行）の両方に生成し、部品の生成スクリプト（`tests/diff/<部品>.py`）が出すコマンドで出力が一致することを確かめる。TOML の `diff.instances` に並べたテンプレート引数の具体化（例 `T = "long long"`）ごとに行う。

`verifier/model_bridge.py`（`check_public.py` の bridge 検査）は、ヘッダのハッシュと公開宣言、翻訳のやり直しと登録済みモデルの全文一致、証明がモデルを import すること、差分テストを確かめる。
