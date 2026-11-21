# segment_tree_beats

`library/segment_tree/segment_tree_beats.hpp` のクラス `cp::SegmentTreeBeats` は、元の `experiments/library/cpp/segment_tree/segment_tree_beats.hpp`（tjkendev の Segment Tree Beats）を移植したもの。値の列 `a`（`std::int64_t`）に対して次の操作を持つ。区間はいずれも半開区間 `[a, b)` で、位置は 0 始まり。

- 区間 chmin `chmin(a, b, x)`（各値を `min(値, x)` にする）
- 区間 chmax `chmax(a, b, x)`
- 区間加算 `add_val(a, b, x)`
- 区間代入 `update_val(a, b, x)`
- 区間最大 `calc_max(a, b)`、区間最小 `calc_min(a, b)`

構築子は `SegmentTreeBeats(std::vector<ll> a)`。和は持たない代わりに、`INF = 4×10^18` まで値を積める。

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
- 空の範囲では `calc_max` は `-INF`、`calc_min` は `INF` を返す。

## 元のソースからの変更

- 名前空間 `cp`、標準ヘッダの include、`std::` の修飾を加えた。元が `template/small_template.hpp` から得ていた `ll = int64_t` と `INF = 4e18` は、クラス内の `using ll = std::int64_t;` と `static constexpr ll INF = 4000000000000000000;` に置き換えた。型と値は元と同じ。
- 構築子の木の作り方を、元の 5 つのループから再帰 `_build(a, k, l, r)` に変えた。`_build` は節点 `k` に `ladd = 0`、`lval = INF`、`len = r - l` を書く。葉なら値（範囲外の葉は番兵 `-INF`/`INF`、個数 0）を置き、内部節点なら 2 つの子を作ってから `update(k)` を呼ぶ。
  - 木の全節点（`0..2n0-2`）に格納される値は元と同じで、時間も `O(n)` のまま。
  - 違うのは、木の節点でない添字 `2n0-1` の `lval` だけである（元は `INF`、新しい版は確保時の 0）。この添字はどの操作も読まない。
  - `tests/segment_tree_beats.cpp` は、元の実装の逐語コピーとすべての操作の結果を照合する。
  - 書き換えの理由は、ループの不変条件を使わず、他の操作と同じ高さについての帰納法で構築を証明するためである。
- API（構築子 1 つと 6 つの操作）、型、入力範囲は元のまま。

## 結果（`Proofs/Cpp/SegmentTreeBeats.lean`）

`Valid st vals B` は「`st` は値の列 `vals` を表す」ことを表す。その中身は次のとおり。

- 形: `n0 = 2^H`、`2^H < 2n`、配列の長さが `2·2^H` 以上。
- 不変条件 `Inv`（`Proofs/Cpp/Lib/SegmentTreeBeatsMath.lean`）: 各節点の要約が実値の最大・第 2 最大・個数などに一致し、保留中の操作が子と整合する。
- 安全性 `Safe`: 各値に祖先の保留中の加算を任意に足しても `|·| ≤ B` に収まる。
- 根の値の列が `vals` である。

`opL f a b 0 vals` は `[a, b)` の位置の値に `f` を適用した列、`maskL d a b 0 vals` は範囲外の値を `d` に置き換えた列である。

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

- **数学層** `Proofs/Cpp/Lib/SegmentTreeBeatsMath.lean`:
  - 列の要約 `Summ`。
  - 節点の配列を関数として見た状態 `BS` と、節点操作（`unm`/`unmin`/`addAll`/`updAll`/`upd`/`push`）の補題。
  - 木の値 `T`（祖先の保留中の加算と clamp を通した実値）、不変条件 `Inv`、安全性 `Safe`。
- **橋渡し** `Proofs/Cpp/SegmentTreeBeats.lean`:
  - `view` が C++ の配列を `BS` として読む。
  - 生成モデルの節点操作は、`BS` の操作に等しい（`unm_cpp` … `push_cpp`）。
- **再帰**: 各再帰（`_chmin`/`_chmax`/`_add_val`/`_update_val`/`_calc_max`/`_calc_min`/`_build`）は、節点の高さについての帰納法で示す。
  - 内部節点の共通部分（押し下げ、2 つの子、`update`）は `inner_post`/`query_inner`/`build_inner` にまとめる。
  - 祖先が押し下げ済みなので、訪れる節点の保留中の加算のオフセットは `[0]` である。加算だけは `[0, x]` を使う。
- **数値の扱い**: 整数は数学的な整数として扱う。値と途中の値が `int64_t` に収まることは、上の `B < INF` の前提から従う。添字が `int` に収まることは `n < 2^29` から従う。

## 検証

- **翻訳**: `verifier/lean_translate.py` がヘッダ全体を翻訳する。この部品のために次を加えた（`docs/translation.md`）。
  - 自己再帰（燃料つきの `_rec`）
  - `static constexpr` のメンバー定数
  - 代入の連鎖
  - コンマ文
  - vector の代入
- **差分テスト** `tests/diff/segment_tree_beats.py`: 前提を満たす操作列で、構築と 6 つの操作をモデルと C++ で比べる。
- **C++ テスト** `tests/segment_tree_beats.cpp`（ASan/UBSan 付き）: 素朴な配列と元の実装の両方と照合する。値の大きさは 3 段階（小、`10^9`、`10^18`）で試す。

## 元の実装の不具合と前提（`docs/experiments_findings.md`）

- 実値が範囲内でも、chmin の後の大きな加算で、格納値と保留中の加算の和が `int64_t` を溢れることがある。例: `[-3.9e18, 3.9e18]` に `chmin(0, 2, -3.8e18)` の後、`add_val(0, 2, 3.85e18)` を 2 回。このため前提は実値ではなく、上の上界 `B`（各加算で `|x|` 増える）で述べる。
- `n = 0` の構築は、長さ 0 の配列の添字 0 に書き込む（未定義動作）。前提は `1 ≤ n`。
