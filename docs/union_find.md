# union_find

`cp::UnionFind` は素集合データ構造（Union Find）のクラスである。元の `experiments/library/cpp/union_find/union_find.hpp`（`disjoint_set_union.hpp` は同じ内容）の `UnionFind` をそのまま公開する。要素は `0 .. n-1`、結合は大きさによる（union by size）、根を求めるたびに経路を圧縮する（path compression）。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `UnionFind()` | 要素のない構造 | O(1) |
| `UnionFind(int n)` | `n` 個の要素がそれぞれ 1 つの木 | O(n) |
| `unite(a, b)` | `a`、`b` を含む木を結合し（大きい木の根が親）、結果の根を返す。同じ木なら何も変えず根を返す | O(log n)、償却ほぼ定数 |
| `same(a, b)` | 同じ木にあるか | 同上 |
| `root(a)` | `a` を含む木の根。`a` から根までの経路の各要素を根に直接つなぐ | 同上 |
| `size(a)` | `a` を含む木の要素数 | 同上 |
| `num_groups()` | 木の数 | O(1) |

表現: `_ps[i] < 0` なら `i` は根で `-_ps[i]` が木の大きさ、`_ps[i] >= 0` なら `_ps[i]` が `i` の親。`_num_groups` は木の数、`_n` は要素数。

- 前提: `0 <= n < 2^31`、各メソッドの引数は `0 <= a, b < n`（`assert` で検査する。`NDEBUG` のビルドは失敗経路の保証の対象外）。
- `same`・`size` も経路を圧縮するので `const` ではない（元のまま）。

## 元のソースからの変更

- 公開側では `namespace cp` に置き、`std::` を明示した（`swap` は `std::swap`）。本体は元と同じ。

## 検証（新方式、`docs/translation.md`）

`verifier/lean_translate.py` がクラスを Lean の構造体 `cp.UnionFind`（`_ps`、`_num_groups`、`_n`）とメソッドに翻訳する（`Proofs/Cpp/Gen/UnionFind.lean`）。自己再帰の `root` は燃料つきの `root_rec`、`return _ps[a] = root(_ps[a]);` は代入のあと `_ps[a]` を返す形になる。

`Proofs/Cpp/UnionFind.lean` が次を示す。到達関係は `Reach`（親をたどる）、根は `IsRoot`、`a` の根が `r` であることは `RootOf`。不変条件 `Inv uf rank` は、`_ps` が森（親は要素で、親へ進むたびに厳密に減るランク `rank` がある）、`_n = _ps.size()`、`_ps.size() < 2^31`。

- `init_int_spec`、`init_0_spec`: 全要素が大きさ 1 の根で、`_num_groups = n`、ランク 0 で `Inv`。
- `root_spec`: 戻り値は `a` の根（元の配列での `RootOf`）。結果の配列は `Comp`（根の集合と根の値が同じで、新しい配列でたどった根は元の配列でも同じ根）を満たし、同じランクで `Inv`。tick 数は `rank a + 1` 以下。証明は `root_rec_spec`（燃料についての帰納法。燃料 `2^64` はランクを要素数以下に正規化した `nrank` より大きい）と `compress_step`（再帰の後に `_ps[a]` を根に書いても森のまま）、`compress_comp`。
- `same_spec`: 元の配列での `a`、`b` の根 `r1`、`r2` について、結果は `r1 = r2`。2 回目の探索は圧縮後の配列で行うが、`Comp` により元の根と一致する。
- `size_spec`: `a` の根 `r` について `-_ps[r]`（元の配列の値）。
- `unite_spec`: `a`、`b` の根 `r1`、`r2`（元の配列）について、2 回の圧縮の後の配列 `ps2`（`Comp`）に対し、等しければ `ps2` のまま `r1` を返す。異なれば大きさで親を決め（`-_ps[r1] < -_ps[r2]` なら `r2` が親）、`link`（親の値に子の値を足し、子を親につなぐ）を返し、`_num_groups` を 1 減らす。結果は新しいランク `urank` で `Inv` を満たす（`link_forest`）。
- `num_groups_spec`: `_num_groups` をそのまま返す。

木の大きさの値（`-_ps[r]` が木の要素数に等しいこと）と、償却の逆アッカーマン上界は主張しない。

差分テスト（`tests/diff/union_find.py`、乱択の操作列）と C++ のテスト（`tests/union_find.cpp`、素朴な実装との比較）で翻訳と実装を確かめる。
