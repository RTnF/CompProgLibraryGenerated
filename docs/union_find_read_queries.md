# UnionFind の const query 本体

公開切替用の隔離 fixture `tests/imports/union_find_public_compat.hpp` について、const same／size／num_groups の本体を検証する。公開ヘッダーはまだ置き換えない。通常の 5 メソッドの既存候補との一致と native ASan/UBSan は [読み取り専用の根探索](union_find_read_cursor.md) の検査に含まれる。

`Proofs/UfReadInline.lean` は、元の scalar denotation から `_n` と探索位置を捕捉し、readonly 根探索、返却値のローカルへの格納、後続コマンドへの継続を構成する。既存 memory／bindings と親配列を保ち、新しい 3 個のローカルだけを追加する。元フィールドへの書込み権限を要求しない。コマンドの slot 計算に使う `shape` は binding 数を表す構文上のリストであり、実行時の bindings を架空のアドレスで置き換えない。

`Proofs/UfReadQueries.lean` は、入力チェックから実インライン展開と最終 return までを合成する。成功した本体やループを前提にせず、次の入力条件から正常終了を構成する。

- vector は slot 0、counter は slot 1、`_n` は slot 2、外部引数は slot 3 以降。scalar binding 数は size で 3、same で 4。
- 元 memory／binding 配置は任意。引数と `_n` の型付き読取りは有効で、探索位置は実際の vector の範囲内。
- 親配列は `Forest vec rank` を満たし、長さは 2^31 未満。fuel は各探索位置の rank+2 以上。
- size はさらに負の根の重みが −|vec| 以上という `UfFieldsSize.Weights` を要求する。これにより INT_MIN の不正な符号反転を除外する。Forest だけではこの条件を導けない。

`_n` は任意の有効 i32 でよく、vector 長と同一とは仮定しない。元の const query は実際の vector 長をチェックするため、値 99 を格納していても長さ 4 の配列への添字 4 を拒否する。readonly counter の書込み権限も要求しない。

M を入力 scalar memory 長、B を入力 scalar binding 数とする。

| 本体 | 返却と保持 | 仕事量上界 | need 上界 |
| --- | --- | --- | --- |
| size(a) | 元配列の到達根 r の重み w に対して −w。元配列を保持 | 16·rank(a)+40 | M+B+30 |
| same(a,b) | 元配列の到達根 r1／r2 の一致なら 1、異なれば 0。元配列を保持 | 16·rank(a)+16·rank(b)+74 | M+B+40 |
| num_groups() | slot 1 の格納値。全 memory と配列を保持 | 2 | M+B+3 |

size の最終 scalar 状態は `inlineState`、same は `sameState` として厳密に特定し、元 memory／bindings をそのまま prefix に残す。vector 書込み数はすべて 0。need は元配置を含む抽象領域の計数であり、byte 数や実測値ではない。この本体の rank に関する上界を、独立した rank 上界の証明なしに対数時間や償却時間と解釈しない。

`tests/test_uf_read_queries.py` は正規 AST 変換器から生成した各本体との定義的一致と、実際の生成本体への一般定理の適用を検査する。異なる／同じ成分、readonly 元 binding の保持、`_n` と実長の相違、空配列、負・終端添字、fuel 不足、INT_MIN の符号反転を扱う。getter は空配列でも格納値を返し、vector 長で値を正規化しない。

この証明はコンパクトな本体実行器に対するもの。元の Context field／header／capability からの引数評価・prepare、実 NProgram 呼出しと finish／restore、および実 initial を含む 3 peak 上界は [readonly receiver の実呼出し](union_find_read_call.md) へ接続した。元 caller だけの資源式への最終合成も同文書の `UfReadPrepareBudget` で扱う。公開 UF の切替、元 DisjointSet の残り API、全 experiments の完了も未達である。
