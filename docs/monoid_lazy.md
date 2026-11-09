# monoid_lazy

`cp::RangeSum`、`cp::RangeAdd`、`cp::RangeSet` は、遅延セグメント木に使う値と作用である。`experiments/library/cpp/algebraic_structure/monoid_lazy.hpp`（`RangeAddRangeMaxMin`・`RangeAddRangeSum`・`RangeSetRangeMaxMin`・`RangeSetRangeSum`）から作った。

- `RangeSum { long long x; int size; }`: 区間の和と長さ。既定値は `(0, 0)`、`op(a, b)` は `(a.x + b.x, a.size + b.size)`。
- `RangeAdd { long long v; }`: 区間への加算。既定値（恒等）は `v = 0`、`compose(f, g)` は `RangeAdd(f.v + g.v)`、`applyExtremum(m)` は最大値（または最小値）`m` に対する新しい値 `m + v`、`applySumX(x, size)` は和 `x`・長さ `size` の区間の新しい和 `x + size * v`。
- `RangeSet { long long v; bool noop; }`: 区間への代入。既定値（恒等）は `noop = true`、`compose(f, g)` は `f.noop` なら `g`、そうでなければ `f`（`g` を先に、`f` を後に適用する作用）。`applyExtremum(m)` は `noop` なら `m`、そうでなければ `v`。`applySumX(x, size)` は `noop` なら `x`、そうでなければ `v * size`。

元のソースからの変更（元APIとコピー効果の差が未解消）:

- 型Tはクラステンプレートのまま保持し、検証した具体化はlong longである。`e()` と `id()` は既定コンストラクタに置き換えた。`numeric_limits` は使わない。
- 元の値モノイド `RangeMax`・`RangeMin` は `monoid.hpp` の `MonoidMax`・`MonoidMin`（同一の定義）に統合した（重複の整理）。`RangeSum` だけをここに置く。
- `apply` は値の型ごとに 1 つのメンバー関数にした: `applyExtremum`（元の `RangeMax`・`RangeMin` への 2 つの具体化は同じ式）と `applySumX`（元は `RangeSum` を返すが、長さは変わらないので新しい和だけを返す）。
- `RangeSet::compose` の `f.noop ? g : f` は、変換器の対象にあわせて `if` と 2 引数コンストラクタで書いた。

前提と結果（`Proofs/MonoidLazyCall.lean`、一般の入力について証明）: 11 個の関数すべて（`RangeSum_op_x`・`RangeSum_op_size`、`RangeAdd_new0`・`new1`・`compose`・`applyExtremum`・`applySumX`、`RangeSet_compose_v`・`compose_noop`・`applyExtremum`・`applySumX`）について、上の結果をそのまま返す。符号付き 64 bit の和・積が桁あふれしないことが前提（桁あふれは契約の外）。`RangeSet` の `noop` は 0 か 1。時間は定数、追加領域は局所変数 3 個以下。

定理に含めていないこと: 結合律・恒等律・「作用が演算と整合する」性質（C++ のテストで確認している）、2 フィールドのクラスのコンストラクタ（`RangeSum`・`RangeSet`。変換器が 1 フィールドのクラスだけを関数として出す）。C++ のテストは `tests/monoid_lazy.cpp`（値の組の全探索で、合成が「先に g、後に f」の逐次適用と一致することを確認する）。

型 `T` はテンプレート引数のままで（`RangeSum<T>`・`RangeAdd<T>`・`RangeSet<T>`、`op<T>`・`compose<T>` は自由関数テンプレート）、検証した具体化は `T = long long`（ヘッダー末尾の明示的な具体化）。元の入れ子の構造体 `RangeAddRangeSum<T>::RangeSum` などは平らなクラステンプレートにした（公開版は入れ子の型に未対応だった旧変換器の制約に合わせた形を保持している）。

2026-11-06の原本比較では、原本のstatic idが公開版になく、RangeSet composeで
コピーを観測するTに対する効果も異なることを確認した。原本は値引数と返却で3回コピーし、
公開版はconst参照とTからの再構築で2回となった。入れ子の別型を平らにしたこと、e/idとapplyの
APIを失ったことも未解消である。上記LLの定理は公開flatモデルを対象とし、
元のgeneric API全体を検証したものではない。[原本調査](experiments_findings.md)を参照する。

2026-11-09: 原本の入れ子型をそのまま使い、`RangeAddRangeMaxMin<long long>::RangeAdd::apply<M>`を`M=RangeMax/RangeMin`へ具体化した生成モデルでも一般証明を追加した。`original_extrema_add_member_general.lean`は任意の既存メモリP・receiver位置・64bit有効入力x/vについて、x+vが範囲内なら既存prefixを保持し、入力コピー・計算値・返却fieldの全セルを含むraw実行を証明する。IR仕事量は7、必要領域はP.length+10である。`original_extrema_member_prepare.lean`は任意callerから1参照と1値を準備する状態・仕事量5を証明する。登録回帰は両Max/Minで独立kernel各3313宣言とC++/UBSanを通過した。任意T/M・厳密なobject lifetimeと元の公開API復元は未完了である。

AddのMax/Min applyは`original_extrema_add_member_call.lean`で任意callerへの接続も証明した。prepare、本体、結果fieldのcapture・exportを通じ、既存scalarの全値と権限・vectorの内容/参照・スコープを保持し、返却先のconst指定を反映する。仕事量の増分は14以下（prepare5、本体7、export2）。scalar/storage/outer peakの上界もcallerと初期stateから明示する。receiverの可変権限、typed入力、加算の範囲内、frameのwellFormed/権限表/所有スコープ、baseMemory範囲を前提とし、成功した呼出しそのものを前提にはしない。fresh原本モデルを使う登録テストで独立kernelはMax/Min各4079宣言、C++/UBSanと既存Set回帰も成功した。

SetのMax/Min applyも`original_extrema_set_member_general.lean`と`original_extrema_set_member_call.lean`で任意prefix/入力から任意callerのexportまで証明した。noopなら入力recordをコピーし、それ以外はvから構築する選択枝だけを実行し、各scopeの一時セルを除去する。型が有効なv/x/boolを前提とし、加算や乗算の範囲条件は課さない。raw実行のIR仕事量はnoop時9・代入時12、必要領域はP.length+13以下。2参照+1値のprepareは仕事量7、exportも含む総増分は21以下で、既存scalar/vector・権限とconst結果、scopeとpeakを扱う。登録テストのfresh原本Add/Set×Max/Minは、独立kernel4080/4080/4100/4100宣言とC++/UBSanに成功した。任意T/M、厳密identity/lifetimeと公開版の元nested API復元は引き続き未完了である。

2026-11-09: 元nested APIの公開前候補を`experiments/verification/algebraic_structure/monoid_lazy.hpp`に置いた。原本からnamespace/includeだけを変え、4familyと全nested型・hidden friend・e/id・record返却apply、型T/Mを保持する。公開`library/`のflat版はまだ切り替えていない。非自明なTのcopy/assignment/destruction traceと、元4familyの利用例を原本と比較した際、原本Add::idの`return 0`がTへの変換とRangeAddへの変換を重ねてコンパイルに失敗することを確認した。MaxMin/Sumの2か所を`return RangeAdd(0)`へ修正し、旧式だけを戻した負例で両方の失敗を検査する。

修正後の原本と候補に対し、MaxMin applyの既存一般証明をfresh生成モデルから再検査した。両方とも固定kernel4080/4080/4100/4100宣言で成功し、旧frontend AddSum一般caller・両Add compose/id・API/copy回帰も成功した。これはlong longのモデルとnative非自明Tの回帰であり、任意T/MのLean検証・厳密なobject identity/lifetime・候補全体の公開条件は未達である。候補のSum構築/e/op/apply、MaxMin op/e、Add/Set composeにも既存一般証明を接続した。原本と候補が同じ生成・証明経路を使い、候補側でも任意callerの全field・既存scalar/vector・const権限・work/peakを確認する。7tests/507.224秒、固定kernelは原本構築4316、候補構築4316×2、Sum op4086×2、MaxMin op/e4117×4、Add compose4072×2、Set compose4102×2、Sum apply4126/4104で成功し、C++/UBSanと入力hash不変も確認した。1fieldの値構築とRangeAdd::idにも任意caller仕様を追加した。original_scalar_record_constructor_general.leanの12rootsは純粋scalar引数式の評価からfield capture/exportまで扱い、総IR workは引数式nodes+6以下（literalでは7以下）、raw needはP.length+7である。original_scalar_record_zero_factory_general.leanの6rootsはidの32→64bit変換と一時scopeを含め、総IR work9以下を示す。既存scalar/vectorと権限・const結果・scope/peakを保持する。原本/候補のRangeMax/RangeMin/RangeAddの6型ずつをfresh生成し、12回の固定kernel3857/3885宣言、C++/UBSan・入力hash不変で2tests/380.630秒成功。次はRangeSetの2field value/default/id入口を一般化し、任意T/Mと厳密な型・寿命の対応を解消する。
