# Compact呼出しで書込み先以外のbuffer内容を保つ

`Proofs/CppCompactValues.lean` は、既存の`CppFixedRun.run_values`をcompact Context呼出しへ接続する。既存の証明はscalar primitive、local vector slot 0への要素書込み、分岐、sequence、scope、while、break/returnを扱う。式評価の一時bindingは既存のprefix/release証明で扱い、flat式だけへ制限しない。

`call_other` は実prepareArguments/compactの結果と初期Target、scope条件、所有条件、scalar result、実callFuel正常結果から、対象owner以外のprojectされたstorage lookupを保持する。実callを分解し、既存run_valuesでbodyを扱い、finish_valuesとrestoreContext_projectでcallerへ戻す。

この定理は実行が成功した場合の効果を述べる。正常終了の存在、返却意味、仕事量/領域上界は元のmethod証明と併用する。割当・resize・copy/move・別methodのinvokeScalarは、このfragmentの対象外である。

[UF全methodの非干渉](union_find_object_values.md)から使い、`tests/test_uf_object_values.py`で元生成body/実呼出しへ適用する。
