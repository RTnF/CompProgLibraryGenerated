# C++ ライブラリの不具合修正記録

ライブラリ（`library/` の公開版、および `experiments/` の持ち込みコード）で直した不具合を、直したときに追記する。規則は `AGENTS.md` の「作業の進め方」を参照する。新しい修正は表の末尾に足す（日付は修正した日）。

記録する内容: どのファイルのどこか、症状（どんな入力でどうなるか）、原因、直し方、再発防止（テストや証明）。`docs/experiments_findings.md` は「直していない注意点」も含む調査表で、こちらは「直したもの」だけを並べる。

| 日付 | 場所 | 症状 | 原因 | 修正 | 再発防止 |
| --- | --- | --- | --- | --- | --- |
| 2026-10-09（持ち込みコードは 2026-10-28） | `library/fenwick_tree.hpp` と `experiments/library/cpp/segment_tree/binary_indexed_tree.hpp` の `BinaryIndexedTree(const vector<T>&)` | 構築で範囲外に書き込む（`v.size() = 3`、`i = 2` で添字 4。`vector::at` で `out_of_range`） | 第 2 ループ `tree[i + (i & -i)] += tree[i]` に上限の検査がなかった | `i + lowbit(i)` が範囲内（`< tree.size()`）のときだけ加算する。持ち込みコードも利用者の指示で同じ形に直した（`if (i + (i & -i) < (int)tree.size())`） | `tests/fenwick_tree.cpp`（長さ 0〜70 の乱数操作、全区間）と構築ループの Lean 証明（`FenwickBuildMath`）。持ち込みコードも修正済み（`experiments_findings.md` の旧記録は当時の調査結果） |
| 2026-10（日付は handoff 参照） | `library/enumerate_quotients.hpp`（元: `experiments/` の商の列挙） | `n > 2^64 - 2^32` で商の上限 `K` を取り損ねる | 上限の定数が `4294967295` だった | `4294967296` に直した。利用者の指示（2026-10-28）で対象範囲を `1 <= n <= 2^64 - 2^32` と明記した（ヘッダとドキュメント） | `docs/enumerate_quotients.md` に記載。全入力の Lean 証明（`EnumerateQuotientsMath`）と C++ テスト |
| 2026-10 | `library/countr_zero.hpp`（元: `countr_zero_constexpr` の `1 << x`） | `int` の `1 << x` が `x = 31` で符号付きオーバーフロー（未定義動作） | ビット判定 `n & (1 << x)` | 「2 で割り切れるか」と `n = n / 2` の繰り返しに書き換え（結果は同じ） | `docs/countr_zero.md`。全入力の Lean 証明（`CountrZeroExec`） |
| 2026-10-27 | `experiments/library/cpp/number/square_matrix.hpp` の `SquareMatrix::operator-()`（単項マイナス） | `minus.mat[i][j] - mat[i][j];` は値を捨てる文で、結果の行列が未初期化のまま返る（成分が不定） | 代入 `=` と符号反転 `-` の書き間違い（`-` の左右の式を引き算にしてしまった） | `minus.mat[i][j] = -mat[i][j];` に直した。公開版には同等の `mat_negate`（`T(0) - a[i]`）を追加 | `tests/square_matrix.cpp` の `mat_negate` と Lean 証明（`SquareMatrixNeg`）。持ち込みコード自体も修正済み。`tools/check_import_square_matrix.py` から単項マイナスの専用回帰ケースを通常実行・ASan/UBSan で確認 |
| 2026-10-29 | `library/bellman_ford.hpp` の `bellman_ford` | 元の `ListGraph::bellman_ford` が持つ親配列（経路復元）と負閉路の印がなかった（機能を落とす変更になっていた） | 検証できる形への書き換えで落とした | 引数に `parent` を追加（緩和で `parent[v] = u`）、後半 `n` 周で負閉路から届く頂点に `-inf` と `parent = -1`。元の印は値に加算して桁あふれするので `-inf` に変更 | `tests/bellman_ford.cpp`（Floyd–Warshall 基準）と Lean（`Proofs/BellmanFordPExec.lean`、`Proofs/BellmanFordParent.lean`） |
| 2026-11-01（候補のみ、公開未反映） | `experiments/verification/segment_tree_beats_wide.hpp`（`library/segment_tree_beats.hpp` の修正候補） | 元の4*nがintに収まるn=2^28でも、新しい8*n+8や構成子の未使用節点の子添字がintに収まらない | 反復化の配列拡大と子参照をintのまま計算し、葉/未使用節点でも子番号を生成していた | 確保長と、全4*n節点を走査する構成子内の子添字をunsigned long longで計算する候補を追加。木の高さから操作側のint子添字は元のサイズ範囲で安全と証明し、6操作は変更しない。公開版/構築証明へは未切替 | 通常/ASan/UBSanの素朴配列比較、算術境界、AST/Lean生成の3検査成功。構成子以外の全生成関数は公開版と一致。候補の全範囲構築証明は未完了 |
| 2026-11-02 | `library/fenwick_tree.hpp` のvector構築子 | 元の `BinaryIndexedTree<T>` で使える、`+=` と `-` はあるが `+` のない型が公開版ではコンパイルできない | 構築時の `+=` を `a = a + b` に書き換え、元にない型の演算要件を加えていた | 元と同じ `tree[j] += tree[i]` に戻した。元ソースは変更しない | `tests/fenwick_tree.cpp` のAdditiveWithoutPlus（3構築子・add・両sum）、元で成功/旧公開で失敗する再現、long longの全4関数の生成IR一致。Leanの既存仕様・モデルは変更しない |
| 2026-11-02 | `experiments/library/cpp/number/square_matrix.hpp` の比較・pow | 比較を具体化すると存在しないxへの参照でコンパイル不可。LLONG_MAX/LLONG_MINの1×1行列のpow(1)で不要な二乗が桁あふれ | 比較がmat以外を参照し、最後の指数ビットの後もyを二乗していた | 各要素を比較し、指数を右シフトして残りがあるときだけ二乗する。非負指数を明示し、pow(ll)・行参照・公開配列・aggregateは維持 | `tests/imports/square_matrix_source.cpp` の全81行列/6561組、独自要素型・乗算回数・型/trait確認と既存power/unary回帰。クラス全体のLean証明は未完了 |
| 2026-11-02（候補、未公開） | `experiments/verification/number/square_matrix.hpp` の型と初期化 | LP64でpow(int64_t)は原本のpow(ll)とメンバー関数型が異なり、配列のメンバー初期化子でtrivialな型でもなくなる | 検証候補へ移す際の型・初期化の書換え | 引数をlong longに戻し、原本と同じ配列宣言にした。追加の次元static_assertも外した | `tests/imports/square_matrix.cpp` のpow型・aggregate/trivial/standard-layoutのstatic_assertと全ケース。標準C++での正次元の前提は文書化し、クラス全体のLean証明は未完了 |

## 付記（直したのではなく、前提に含めたもの）

次は元のコードが持つ性質で、直さずに前提として明記した（`docs/experiments_findings.md`）: `GroupMul::inv()` は整数で `±1` 以外だと 0、`MonoidMul::op` と `CumulativeSum` は符号付きの桁あふれが未定義動作。
