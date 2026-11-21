# segment_tree_beats_sum

`library/segment_tree/segment_tree_beats_sum.hpp` のクラス `cp::SegmentTreeBeatsSum` は、元の `experiments/library/cpp/segment_tree/segment_tree_beats_sum.hpp`（tjkendev の Segment Tree Beats に区間和を加えたもの）を移植したもの。`segment_tree_beats`（`docs/segment_tree_beats.md`）に、各節点の和の配列 `sum` と区間和 `calc_sum(a, b)` を加えたクラスである。値の列 `a`（`std::int64_t`）に対して次の操作を持つ。区間はいずれも半開区間 `[a, b)` で、位置は 0 始まり。

- 区間 chmin `chmin(a, b, x)`（各値を `min(値, x)` にする）
- 区間 chmax `chmax(a, b, x)`
- 区間加算 `add_val(a, b, x)`
- 区間代入 `update_val(a, b, x)`
- 区間最大 `calc_max(a, b)`、区間最小 `calc_min(a, b)`、区間和 `calc_sum(a, b)`

構築子は `SegmentTreeBeatsSum(std::vector<ll> a)`。和を持つので、値は `INF` まで積めず、和が `int64_t` に収まる範囲に限る（下の前提）。

木は 2 冪 `n0 ≥ n` 個の葉を持つ。節点 `k` の子は `2k+1` と `2k+2`。各節点は次を持つ。

- 最大値・第 2 最大値・最大値の個数
- 最小値・第 2 最小値・最小値の個数
- 長さ `len`
- 保留中の加算 `ladd`
- 保留中の代入 `lval`（保留なしは `INF`）

chmin は、節点の第 2 最大値が `x` より小さいとき、その節点の最大値だけを `x` にして止まる。そうでなければ `push` で子へ押し下げて再帰する（chmax は対称）。

## 前提

- `1 ≤ n < 2^29`（配列の長さ `4n` が `int` に収まる。Lean の定理は `n ≤ 2^29` で示している）。
- 値の上界 `B < INF` がある。
  - 初めは `B ≥ max |a[i]|`。
  - `chmin`/`chmax`/`update_val` の `x` は `|x| ≤ B`。
  - `add_val` は上界を `B + |x|` に増やし、`B + |x| < INF` を要する。
- `update_val`/`add_val` は `b ≤ n`。`a` は任意で、負の位置は無視される。`chmin`/`chmax`/`calc_max`/`calc_min` の `a`、`b` は任意の `int`（`[0, n)` の外の位置は無視される）。
- 和と `sum[k]` の更新（`(x - max) * 個数`、`len * x`）が `int64_t` に収まる: `2 · n · B < 2^63`。
- 空の範囲では `calc_max` は `-INF`、`calc_min` は `INF`、`calc_sum` は `0` を返す。

## 元のソースからの変更

- 名前空間 `cp`、標準ヘッダの include、`std::` の修飾を加えた。元が `template/small_template.hpp` から得ていた `ll = int64_t` と `INF = 4e18` は、クラス内の `using ll = std::int64_t;` と `static constexpr ll INF = 4000000000000000000;` に置き換えた。型と値は元と同じ。
- 構築子の木の作り方を、元の 5 つのループから再帰 `_build(a, k, l, r)` に変えた。`_build` は節点 `k` に `ladd = 0`、`lval = INF`、`len = r - l` を書く。葉なら値（範囲外の葉は番兵 `-INF`/`INF`、個数 0）を置き、内部節点なら 2 つの子を作ってから `update(k)` を呼ぶ。
  - 木の全節点（`0..2n0-2`）に格納される値は元と同じで、時間も `O(n)` のまま。
  - 違うのは、木の節点でない添字 `2n0-1` の `lval` だけである（元は `INF`、新しい版は確保時の 0）。この添字はどの操作も読まない。
  - 範囲外の葉の `sum` は明示的に 0 を書く（元は確保時の 0 のまま。値は同じ）。
  - `tests/segment_tree_beats_sum.cpp` は、元の実装の逐語コピーとすべての操作の結果を照合する。
  - 書き換えの理由は、ループの不変条件を使わず、他の操作と同じ高さについての帰納法で構築を証明するためである。
- API（構築子 1 つと 6 つの操作）、型、入力範囲は元のまま。

## 結果（`Proofs/Cpp/SegmentTreeBeatsSum.lean`）

`Valid st vals B` は「`st` は値の列 `vals` を表す」ことを表す。その中身は次のとおり。

- 形: `n0 = 2^H`、`2^H < 2n`、配列の長さが `2·2^H` 以上。
- 不変条件 `Inv`（`Proofs/Cpp/Lib/SegmentTreeBeatsMath.lean`）: 各節点の要約が実値の最大・第 2 最大・個数などに一致し、保留中の操作が子と整合する。
- 安全性 `Safe`: 各値に祖先の保留中の加算を任意に足しても `|·| ≤ B` に収まる。
- 根の値の列が `vals` である。

`ValidS st vals B` は `Valid st vals B` に加えて、各節点の `sum` がその節点の値の和に等しいこと（`SumOK`、不変条件 `SInv`）を表す。`opL f a b 0 vals` は `[a, b)` の位置の値に `f` を適用した列、`maskL d a b 0 vals` は範囲外の値を `d` に置き換えた列である。

- 各定理は `segment_tree_beats` と同じ結果を `ValidS` について述べる（`init_specS`、`chmin_specS`、`chmax_specS`、`update_val_specS`、`add_val_specS`、`calc_max_specS`、`calc_min_specS`）。
- `calc_sum_specS`: 返り値は `(maskL 0 a b 0 vals).sum`（`[a, b)` の値の和）。木はまた `vals` を表す。
- `init_spec`: `1 ≤ n ≤ 2^29`、`|a[i]| ≤ B < INF` なら、構築した木は `Valid st a B`。手数は `50n + 10` 以下。
- `chmin_spec`/`chmax_spec`: `|x| ≤ B`、`-INF < x < INF` なら、結果は `Valid r (opL (min · x) a b 0 vals) B`（chmax は `max`）。
- `update_val_spec`: `b ≤ n`、`|x| ≤ B`、`-INF < x < INF` なら `Valid r (opL (fun _ => x) a b 0 vals) B`。
- `add_val_spec`: `b ≤ n`、`B + |x| < INF` なら `Valid r (opL (· + x) a b 0 vals) (B + |x|)`。
- `calc_max_spec`/`calc_min_spec`: 返り値は `lmax (maskL (-INF) a b 0 vals)`、`lmin (maskL INF a b 0 vals)`。木はまた `vals` を表す（`push` だけが状態を変える）。
- 各操作の手数は `48n + 1` 以下。

## 時間と領域

- 証明した上界は、構築が `O(n)`、各操作が `O(n)`（1 回の操作は各節点を高々 1 度訪れる）。
- Segment Tree Beats の既知の償却 `O(log^2 n)` は証明していない。性能の保証としては使わない。
- 領域は長さ `4n` の配列 9 本。再帰の深さは木の高さ `⌈log2 n⌉ + 1`。

## 証明の構成

- `Proofs/Cpp/SegmentTreeBeatsSumCore.lean`: `segment_tree_beats` の証明（`Proofs/Cpp/SegmentTreeBeats.lean`）を、配列 `sum` を加えた構造体に移したもの。`view` は `sum` を読まないので、結果はそのまま成り立つ。
- `Proofs/Cpp/Lib/SegmentTreeBeatsSumMath.lean`: 和の不変条件 `SInv`（各節点の `sum` は実在の葉の値の和）と、各節点操作の和の更新（C++ と同じ規則）が `SInv` を保つこと。
  - chmin は、最大値の値だけが `x` になることから `sum += (x - max) · 個数`。chmax は対称。
  - 加算 `+= len · x`、代入 `= x · len` は、これらが実在の葉だけの節点にしか適用されないことから正しい。
  - `push` は子への加算・代入と `caps`（chmin/chmax）を順に追う（`push_sinv`）。
- `Proofs/Cpp/SegmentTreeBeatsSum.lean`: `viewS` で配列 `sum` を読み、各節点操作の `sum` の変化（`unm_sum` …、`push_sum`）と、各再帰が `SInv` を保つこと（`*_rec_S`）を示す。前の結果とは `triple_and` で合わせる。`calc_sum` は値と状態をまとめて示す（`qsum_rec_spec`）。

## 検証

- **翻訳**: `verifier/lean_translate.py` がヘッダ全体を翻訳する（`segment_tree_beats` と同じ規則）。
- **差分テスト** `tests/diff/segment_tree_beats_sum.py`: 前提を満たす操作列で、構築と 7 つの操作をモデルと C++ で比べる。
- **C++ テスト** `tests/segment_tree_beats_sum.cpp`（ASan/UBSan 付き）: 素朴な配列と元の実装の両方と照合する。値の大きさは 3 段階（小、`10^9`、`10^16`）で試す。

## 元の実装の不具合と前提（`docs/experiments_findings.md`）

- 実値が範囲内でも、chmin の後の大きな加算で、格納値と保留中の加算の和が `int64_t` を溢れることがある。例: `[-3.9e18, 3.9e18]` に `chmin(0, 2, -3.8e18)` の後、`add_val(0, 2, 3.85e18)` を 2 回。このため前提は実値ではなく、上の上界 `B`（各加算で `|x|` 増える）で述べる。
- `n = 0` の構築は、長さ 0 の配列の添字 0 に書き込む（未定義動作）。前提は `1 ≤ n`。
