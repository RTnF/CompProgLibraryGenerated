# monoid_lazy

`cp::RangeSum`、`cp::RangeAdd`、`cp::RangeSet` は、遅延セグメント木に使う値と作用である。`experiments/library/cpp/algebraic_structure/monoid_lazy.hpp`（`RangeAddRangeMaxMin`・`RangeAddRangeSum`・`RangeSetRangeMaxMin`・`RangeSetRangeSum`）から作った。

- `RangeSum { long long x; int size; }`: 区間の和と長さ。既定値は `(0, 0)`、`op(a, b)` は `(a.x + b.x, a.size + b.size)`。
- `RangeAdd { long long v; }`: 区間への加算。既定値（恒等）は `v = 0`、`compose(f, g)` は `RangeAdd(f.v + g.v)`、`applyExtremum(m)` は最大値（または最小値）`m` に対する新しい値 `m + v`、`applySumX(x, size)` は和 `x`・長さ `size` の区間の新しい和 `x + size * v`。
- `RangeSet { long long v; bool noop; }`: 区間への代入。既定値（恒等）は `noop = true`、`compose(f, g)` は `f.noop` なら `g`、そうでなければ `f`（`g` を先に、`f` を後に適用する作用）。`applyExtremum(m)` は `noop` なら `m`、そうでなければ `v`。`applySumX(x, size)` は `noop` なら `x`、そうでなければ `v * size`。

元のソースからの変更（元APIとコピー効果の差が未解消）:

- 型Tはクラステンプレートのまま保持し、検証した具体化はlong longである。`e()` と `id()` は既定コンストラクタに置き換えた。`numeric_limits` は使わない。
- 元の値モノイド `RangeMax`・`RangeMin` は `monoid.hpp` の `MonoidMax`・`MonoidMin`（同一の定義）に統合した（重複の整理）。`RangeSum` だけをここに置く。
- `apply` は値の型ごとに 1 つのメンバー関数にした: `applyExtremum`（元の `RangeMax`・`RangeMin` への 2 つの具体化は同じ式）と `applySumX`（元は `RangeSum` を返すが、長さは変わらないので新しい和だけを返す）。
- `RangeSet::compose` の `f.noop ? g : f` は、変換器の対象にあわせて `if` と 2 引数コンストラクタで書いた。

前提と結果（`Proofs/MonoidLazyCall.lean`、一般の入力について証明）: 11 個の関数すべて（`RangeSum_op_x`・`RangeSum_op_size`、`RangeAdd_new0`・`new1`・`compose`・`applyExtremum`・`applySumX`、`RangeSet_compose_v`・`compose_noop`・`applyExtremum`・`applySumX`）について、上の結果をそのまま返す。符号付き 64 bit の和・積が桁あふれしないことが前提（桁あふれは契約の外）。`RangeSet` の `noop` は 0 か 1。時間は定数、追加領域は局所変数 3 個以下。

定理に含めていないこと: 結合律・恒等律・「作用が演算と整合する」性質（C++ のテストで確認している）、2 フィールドのクラスのコンストラクタ（`RangeSum`・`RangeSet`。変換器が 1 フィールドのクラスだけを関数として出す）。C++ のテストは `tests/monoid_lazy.cpp`（値の組の全探索で、合成が「先に g、後に f」の逐次適用と一致することを確認する）。

型 `T` はテンプレート引数のままで（`RangeSum<T>`・`RangeAdd<T>`・`RangeSet<T>`、`op<T>`・`compose<T>` は自由関数テンプレート）、検証した具体化は `T = long long`（ヘッダー末尾の明示的な具体化）。元の入れ子の構造体 `RangeAddRangeSum<T>::RangeSum` などは平らなクラステンプレートにした（変換器が入れ子の型を扱えないため）。

2026-11-06の原本比較では、原本のstatic idが公開版になく、RangeSet composeで
コピーを観測するTに対する効果も異なることを確認した。原本は値引数と返却で3回コピーし、
公開版はconst参照とTからの再構築で2回となった。入れ子の別型を平らにしたこと、e/idとapplyの
APIを失ったことも未解消である。上記LLの定理は公開flatモデルを対象とし、
元のgeneric API全体を検証したものではない。[原本調査](experiments_findings.md)を参照する。
