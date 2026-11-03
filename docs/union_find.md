# union_find

`cp::UnionFind` は素集合データ構造（Union Find）のクラスである。元の `experiments/library/cpp/union_find/union_find.hpp` の `UnionFind` と同じ構成子とメンバー関数を持つ（`UnionFind()`、`UnionFind(int n)`、`unite`、`same`、`root`、`size`、`num_groups`）。要素は `0 .. n-1`、結合は大きさによる（union by size）。

| メンバー | 内容 | 時間 |
| --- | --- | --- |
| `UnionFind()` | 要素のない構造 | O(1) |
| `UnionFind(int n)` | `n` 個の要素がそれぞれ 1 つの木 | O(n) |
| `unite(a, b)` | `a`、`b` を含む木を結合し、結果の根を返す。同じ木なら何も変えず根を返す | O(log n) |
| `same(a, b)` | 同じ木にあるか | O(log n) |
| `root(a)` | `a` を含む木の根（`a` から根までの経路を圧縮する） | 償却ほぼ定数 |
| `size(a)` | `a` を含む木の要素数 | O(log n) |
| `num_groups()` | 木の数 | O(1) |

森の表現: vector `ps` は `n + 1` 個の要素を持つ。`i < n` について、`ps[i] < 0` なら `i` は根で値は木の大きさの符号反転、`ps[i] >= 0` なら `ps[i]` が `i` の親である。最後の要素 `ps[n] = -1 - (木の数)` は、`n` 未満の添字からは到達されない根（番兵）で、木の数を持つ。

元のソースからの変更（検証できる形にするために書き換えた）:

- 元は木の数と要素数を別のフィールド（`_num_groups`、`_n`）に持つ。検証できる関数は、クラスをフィールドごとの引数（vector は参照）に分けて作る。公開版の既存証明では木の数を `ps` の最後の要素に置き、要素数は `ps.size() - 1` で得る。変換器は現在、可変スカラーフィールドを参照で受ける関数を扱える。元の別フィールドを保つ候補と全状態照合は [union_find_experiment.md](union_find_experiment.md) に記録しており、候補の一般call証明とクラス全体の不変条件への接続が未完了である。
- `unite`、`same`、`size` は、根を求めるときに経路圧縮をしない（元は毎回圧縮する）。木の高さは大きさによる結合で `log2 n` 以下なので 1 回あたり最悪 O(log n) だが、元の償却の見積もり（逆アッカーマン関数）は主張しない。`root` は元どおり経路圧縮をする。
- 元の `assert(0 <= a && a < _n)` は、`assert(0 <= a)` と `assert(a < (int)ps.size() - 1)` に分けて保持する。`b` も同じ順序で検査する。`UnionFind(int n)` の本体にも元と同じ非負検査を保持する。assert有効の固定C++17検証プロファイルでは、不正な添字はvectorの読み取り前に異常終了する。`NDEBUG` でassertを無効にしたビルドは、この失敗経路の保証対象に含めない。
- `-ps[x]` は `0 - ps[x]` と書いた（検証済みの式に、vector の読み取りへの単項マイナスがないため）。

前提:

- 正常終了の前提は `0 <= n < 2^31 - 1`、`0 <= a, b < n`。番兵を含む `ps.length` ではなく、要素数 `ps.length - 1` を上限にする。
- 森の条件（`Forest ps rank`）: 親の添字が範囲内で、親へ進むたびに厳密に減るランク `rank : Nat → Nat` が存在する（閉路がない）。要素は `int` に収まる。
- `unite`: `n` 未満の添字の親はすべて `n` 未満（番兵を指さない）、`0 - x` が `int` に収まる、2 つの根の大きさの和が `int` に収まる、木の数が 1 以上（番兵の値 `+ 1` が負）。

証明する内容（`Proofs/UnionFindCall.lean`。`T = int` の vector について、一般の入力で）:

- `union_find_find_root_correct`（非公開の `find_root`）、`union_find_root_correct`（`root`）、`union_find_same_correct`（`same`）、`union_find_size_correct`（`size`）、`union_find_unite_correct`（`unite`）: 以前の `uf_root`、`uf_find`、`uf_same`、`uf_size`、`uf_unite` の定理を、クラスのメンバーとして述べ直したもの。`root` は戻り値が根で、`a` から根までの経路上の節点（根を除く）が根を指す vector に変わり、それ以外は変わらず、再び `Forest` を満たす。`unite` は 2 つの根を結合し（`uniteVecC`）、木の数の要素を 1 だけ増やす（符号反転で 1 減る）。結合後も `Forest` を満たす（`uniteVecC_forest`）。
- `union_find_num_groups_correct`: 戻り値は `-1 - ps[ps.size() - 1]`。
- `union_find_new_correct`: 構成子 `UnionFind(n)` の本体の非負assertと `ps[n] = -1 - n`。
- 各公開メソッドの成功定理はassertを含む生成bodyを実行し、検査のworkと一時領域を上界に含める。共通の `UfBounds.reject_bounds` は、任意の本体、int添字、長さ `1 <= ps.length < 2^31` について、負の添字または `a >= ps.length - 1` を本体実行前に拒否する純粋実行補題である。実NProgramの失敗との照合は専用の有限テストでも行う。

定理に含めていないこと: `UnionFind()` と `UnionFind(int n)` の `ps(1, -1)`、`ps(n + 1, -1)`（標準ライブラリの `std::vector<int>(size_type, const int &)` の契約による）、木の数が実際の木の数に等しいという不変条件、`unite`/`same`/`size` での経路圧縮。C++ のテストは `tests/union_find.cpp` で、乱択の操作列を素朴な成分の再ラベル付けと照合し、20 万要素の連鎖も確認する。

`tests/test_union_find_bounds.py` は専用の `tests/imports/union_find_bounds/in/cases.txt` と `out/cases.txt` を読み、元の入力検査を生成NProgramのfaultとC++のSIGABRTで照合する。空集合、先頭/末尾の正しい要素、番兵、負数、INT_MIN/INT_MAX、二引数メソッドの両引数を扱い、ASan/UBSanで不正アクセスが先行しないことを確認する。assertを除くと空集合の番兵が根0として正常返却される対照も確認する。

構成子のvectorフィールド初期化は本体のassertより前に実行される（元のソースも同じ順序）。負のnが確保例外を起こす場合までSIGABRTとは主張しない。n=-1では空vectorの初期化後、本体assertで停止する。番兵のための `n+1` の範囲制限、元の別カウンタ、unite/same/sizeの経路圧縮は引き続き未解消である。
