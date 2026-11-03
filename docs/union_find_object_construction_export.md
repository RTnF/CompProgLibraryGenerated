# 元UF constructorからowned heapへ

`Proofs/UfObjectConstructionExport.lean` は元生成constructorの実 `constructFuel` 結果と、新しいmutable header/allocation表でのbuffer登録を接続する。Contextの正常State全体への接続は引き続き未完了である。

## 実constructorと既存caller

`sized_export` / `default_export` は旧 `UfConstructedReceiver` の正常終了構成、実Initializedとnew bufferを使う。元sourceの同じfuelの結果を `UfConstructionReferences` の結果と同定し、元FrameのExtendsと既存の正常read保持も返す。callerのwellFormed、HeapModels、scope/基準量/長さの条件、元heapのUnique/OwnsAll/HeadersLive/AllocationsValidを保持する。sized版は元のint範囲の非負サイズとscalar式の型/値条件を使う。

実new bufferはreplicate n(-1)、capacity n、元limit、epoch 0である。同じbufferのownerを新allocation IDへ付け替え、[構築済みbufferの表登録](move_append_owned.md)でheader/allocationの末尾へ追加する。元NStateのowner IDと新しい表のowner IDを混同せず、buffer全体の対応を明示する。

## 不変条件と実counter

`exportedHeap` はheap work/peak/baseSpaceを実NState結果からそのまま引き継ぎ、`exported_counters` で一致を保証する。Unique/OwnsAll/HeadersLive/AllocationsValid、新currentBuffer、元grantのownerが元allocation表内ならread結果一致、生存量=元+1+nを証明する。

元heapに登録されたIDとgrantは変えない。source側の既存Frame/readの保持と、登録heap側の参照保持を両方扱う。materializeの空placeholder番号の移動を含む全NStateの同一性を仮定しない。

`tests/test_uf_object_construction_export.py` は空callerと既存scalar=7を持つcallerについて、任意n<2^31の実sized constructor、実scalar fieldsとnew buffer、登録heap不変条件を検査する。[実constructor配置](constructor_layout.md)からfield数2、binding数+2、元slotsと新vector/scalar slotsの配置を導く。default版の実正常終了/exportも検査する。

## 残件

実scalar fields/bindings/slots/viewsから正常Context StateとHeadersLiveを構成し、元caller全体との対応を証明する接続が残る。その後の寿命操作混在、元caller AST/評価順/副作用、公開UF相違解消と他旧ライブラリも未完了である。このheap exportをwhole-class検証完了とは扱わない。

[実fields/views/slotsから正常Stateと任意有限method列へ](union_find_object_constructed_state.md)接続した。caller全体の再番号付けを含む意味対応と寿命混在は引き続き残る。
