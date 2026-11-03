# 追加フィールドを保つ読み取り専用の根探索

`Proofs/UfReadCursor.lean` は、vector が slot 0 にあり、任意個の scalar binding の後ろに探索位置の値を置く配置で、親をたどるループを検証する。生成された C++ の const メソッドには counter 参照や `_n` の値が残るため、探索位置が slot 1 にある既存の証明をそのまま使えない。この配置でも既存フィールドの書込み権限を広げない。

`cursor P bindings a` は元 memory P に探索位置の cell を 1 個だけ追加し、元 bindings の後ろにその cell への writable binding を追加する。書き換えるのはこのローカル cell だけである。元 memory と bindings は任意であり、元フィールドへの書込み権限や counter の値は根探索の前提にしない。

`Forest ps rank` は全要素が i32 として有効で、非負の親が配列内を指し、親への移動ごとに rank が厳密に減少することを要求する。配列長は 2^31 未満、初期位置 a は配列内とする。長さ INT_MAX はこの条件に含まれる。

- `loop_run` は fuel ≥ rank(a)+2 から実ループの終了を構成し、負の値を持つ根 r への Reach、配列全体の保持、元 memory と bindings の保持を保証する。
- `body_run` は最後の return も含めて r を返す。仕事量は 16·rank(a)+18 以下、need は |P|+|bindings|+20 以下、vector 書込み数は 0 である。
- need は元 memory と binding の計数も含む抽象領域であり、byte 数や実測値ではない。rank の対数上界や UnionFind 全体の償却計算量は、この補題だけからは主張しない。

`tests/test_uf_read_cursor.py` は `tests/imports/union_find_public_compat.hpp` という公開切替用の隔離 fixture を元に、正規の AST 変換器で 9 メソッドを生成する。通常の 5 メソッドが既存候補の NProgram と定義的に同一であること、const helper の本体が `body` と同一であることを検査し、任意の元フィールド配置と Forest に対して実 helper 本体へ `body_run` を適用する。const same の 2 ループと const size のループも、それぞれ異なる binding 数で `loop` と一致する。readonly な元 bindings の保持、fuel 不足、範囲外入力を有限例でも確認する。

同 fixture の native テストは、既定・サイズ指定コンストラクタ、通常・const の各 API、copy と move 後の getter を ASan/UBSan と単純な分割モデルで照合する。型を指定した通常・const のメンバー関数ポインタも確認する。overload の追加により、型を指定しない `auto p = &UnionFind::same` 等は曖昧になるため、公開切替時の API 互換性に注意が必要である。

この段階では公開ヘッダーを置き換えない。const same/size/num_groups のチェック・ローカル宣言・返却を含む本体全体は [const query 本体](union_find_read_queries.md) で追加検証する。実 Context の準備と復元は [readonly receiver の実呼出し](union_find_read_call.md) へ接続した。元 caller だけの資源式への合成も同文書で扱う。fixture の native 成功と本体の一般証明を、これらの API 全体や全 experiments の検証完了とは扱わない。
