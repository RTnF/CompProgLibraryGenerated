# readonly UF 呼出しによる全 payload・参照の保持

`Proofs/UfReadValues.lean` は [readonly の実呼出し](union_find_read_call.md) に、全 owner の buffer、既存参照の read、caller の配置と receiver の保持を接続する。公開切替用 const size／same／num_groups の 3 メソッドについて、元 receiver の条件から成功 call を構成する最終定理を提供する。公開ヘッダーはまだ変更しない。

`Preserved before after object receiver` は次を保証する。

- 元 scalar memory 全体の同一性と、slot／binding／scope／header／view／grant 等の caller Layout。
- 任意 owner に対する storage.lookup の同一性。items だけでなく、owner・capacity・limit・epoch を含む buffer 全体を保持する。
- 任意の既存 reference に対する Frame.read の同一性。正しい値の保持と、型・epoch・権限等により拒否されていた read の拒否保持を両方含む。
- 更新先の ReadReceiver を構成でき、元の counter／`_n` の値を保つ。

## 証明の接続

restore の実 shape guard から `SameHeaders` と最大権限の保持を得る。元 receiver から実 prepare／compact と target を再構成し、既存の `CppCompactValues.call_other` で対象以外の owner を保持する。対象 owner については、元配列 items と header signature の一致から buffer 全体の同一性を構成する。これらを合成して全 lookup を保持する。

caller Layout と shape から `CallEffects` を構成し、全 lookup と型付き frame 条件から全 reference の read を保持する。viewBinding の一致は各 view の header と allocation 数に基づいて示し、部分適用された map を無理に展開しない。元 memory と Layout から receiver を更新する。

`all_payload` 等の共通効果補題は成功 call と対象 payload を中間入力に取る。最終 `size_call`／`same_call`／`counter_call` は、`UfReadPrepareBudget` が元条件から構成した call／payload／memory をこれらへ渡すため、成功 call を利用者の前提に追加しない。返却値の意味、停止、caller 基準の仕事量・3peak 上界は同定理から引き継ぐ。

## 検査範囲

`tests/test_uf_read_call.py` は実 C++ から生成した program／引数写像と最終呼出し定理の対応を既存経路で検査する。全保持の fixture は元 readonly receiver から 3 呼出し定理を構成し、全 lookup／read と receiver 更新へ適用する。

追加の複数 owner 例には、scope 0 の対象 UF と scope 1 の別 mutable UF を同居させる。対象の最大 header 権限は任意 Bool、借用 view と対象 scalar bindings は readonly。別 UF の有効な epoch 7 の参照と、古い epoch 6 の参照を区別する。readonly 呼出し後も別 UF の counter／size と mutable 権限を復元できる一般例を検査する。実呼出し列でも、readonly size の後に別 UF を unite し、有効参照が更新値を読み、古い epoch の参照は拒否され、対象の親配列は変わらないことを確認する。

この例は寿命の異なる live owner を扱う。scope 終了による破棄・copy export・任意の長い操作列を含む寿命全体の証明や、公開 UF の切替、元 DisjointSet の残 API、全 experiments の完了は未達である。C++ ソースは今回変更しておらず、native ASan/UBSan は既存の検査経路を保持する。
