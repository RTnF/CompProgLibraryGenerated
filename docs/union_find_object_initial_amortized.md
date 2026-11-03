# singleton初期状態からのUF列の仕事量

`Proofs/UfObjectInitialAmortized.lean` は[全5methodの償却評価](union_find_object_amortized.md)の初期potential項を、消せる条件の下で取り除く。

`zero_vertex` / `zero_forest` は、数学的rankが全点で0ならvertex/forest potentialが0となることを任意の親配列について証明する。`initialized_resources` は正常Stateの親配列が `List.replicate n (-1)` であることから `initial_history n` を適用し、正常終了する任意有限列について次を保証する。

```
work(out) ≤ work(source) + 718*操作数*(alpha(n)+1)
```

初期potential=0と最終potential≥0を使う。n=0を除外しない。元Stateのsize/型/所有・配置条件、操作ごとの添字条件、HeadersLiveを保持し、実script、全返却、最終State、全Historyと数学的History、既存scalar/heap/全体peak上界を同時に構成する。任意の既存状態で初期potentialを省く定理ではない。

`tests/test_uf_object_initial_amortized.py` は4 singletonの正常Stateから任意有限操作列を構成し、元意味・数学的History・初期potentialなしの仕事量と全領域を確認する。空の正常State、任意自然数回getter、添字0へのrootが範囲外となる境界も検査する。これらのfixtureは正常なモデル状態を明示構成したものであり、元C++ constructorとの接続を完了したとは扱わない。

元constructorからこのState/HeadersLiveを構成する接続、寿命操作混在、元callerの評価順/副作用、公開UF相違と他旧ライブラリは未完了である。
