# 元ObjectRefのUF列全体に対するヒープ上界

`Proofs/UfObjectHeapPeak.lean` は[実成功したUF列](union_find_object_trace_actual.md)のヒープpeakと生存量を証明する。全5メソッドの呼び出し後に同じresident量と測定基準を保つため、列の長さに応じてヒープ上界を加算する必要はない。

## 前提と空間の対応

通常のStateと元の添字条件に加え、`HeadersLive`、すなわちallocationを持つ各headerが生存allocationを指すことを明示する。Unique/OwnsAllと合わせ、materializeした評価器の生存量が元heapのliveSpaceと等しいことを使う。State自体やmoved-fromの弱いgetter定理の条件は変更しない。

元heapのliveSpaceは、生存vector headerごとの1単位と生存allocationの容量の和である。grant履歴、墓標、証明用のrank等はC++の追加領域へ数えない。抽象単位をC++のバイト数や実測値としては扱わない。

`prepare_heap` は実resolve/prepareSavedから元heapの保持を導く。`prepared_budget` は実prepare・compact・FWと上記の物理空間対応から、従来のstorageBudgetを次の元callerの量へ照合する。

```
budget(source) = max source.heap.peak
                    (source.heap.liveSpace + 1 - source.heap.baseSpace)
```

減算は自然数の切捨て減算である。初期peakと測定基準を省かない。

## 各呼び出しと列全体

`invoke_peak` は全5メソッドの既存heapPeak postを用い、異なるfuelの成功一意性で実結果Contextへ上界を移す。`invoke_heap_effects` は実restoreからliveSpace/baseSpace/HeadersLiveを保持する。各methodの正常終了は既存stepから構成し、実成功仮定でその構成を置き換えない。

`history_peak` は各Stepに沿ってこれらを合成する。中間ContextでもliveSpaceとbaseSpaceは同じで、そのpeakは元budget以下なので、tailに適用する予算も元budget以下となる。`actual_peak` は供給された実成功scriptへ同じ結果を転送する。

`actual_additional_peak` は、測定開始時にbaseSpace=liveSpaceとした場合、結果のheap peakがmax(初期heap peak,1)以下であることを示す。新しい測定として初期heap peakを0にした場合は高々1単位であり、操作列の長さに依存しない。

`execute_peak_work` は元Stateと添字条件から、正常終了するscript、結果列、最終State、全History、Charges、仕事量上界、heap peak上界、生存量/基準量/HeadersLive保持を同時に構成する。仕事量だけやヒープ量だけへ結果を弱めない。

## 検査と残件

`tests/test_uf_object_heap_peak.py` は全5method混在列、任意自然数回のroot、2成分からのunite列で、一定のheap上界と生存量保持を確認する。元move後の実payloadとfieldsを保って生存量7を新測定の基準とし、初期heap peak=0から混在列全体の追加heap peak≤1と、仕事量/返却意味を合わせて証明する。

[全5メソッドのスカラー上界](union_find_object_scalar_peak.md)を追加した。スタックを含む列全体の全peak、rank履歴/償却、元caller/constructorからの初期StateとHeadersLiveの構成、評価順/副作用、寿命操作との混在、割当/resize/nested/異種vector、公開UF相違と他旧ライブラリは未完了である。
