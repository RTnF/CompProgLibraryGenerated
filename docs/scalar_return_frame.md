# Scalar returnによるbuffer内容の保持

`Proofs/CppScalarReturnFrame.lean` はscalarだけを評価するreturnの実行結果から、frame・slots・scope・scalar memory/bindings/baseの保持を導く。

`ret_core` は実runFuelの結果を分解し、正常returnとbreaking=falseも返す。`sequence_core` はreturn後の任意の後続commandを実行しないことを含む。実行結果を仮定する効果定理であり、任意の式の正常終了を単独で保証するものではない。

`retire_payload` は対象scopeにownerがない場合、実retireScopeでforestと全storage objectsを保持する。`finish_payload` はこれをscalar finishへ接続する。過去peakや仕事量の一致は主張しない。退役時のobserveはpeakを更新しうる。

[UF getterのframe証明](union_find_object_getter_frame.md)から、実prepare/body/finish/restoreを通じて適用し、別bufferの内容も保持することを確認する。検査は`tests/test_uf_object_getter_frame.py`に登録する。
