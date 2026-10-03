---
title: モノイド (Monoid)
documentation_of: //cpp/algebraic_structure/monoid.hpp
---
<link rel="stylesheet" type="text/css" href="../../css/common.css">

[Wikipedia - モノイド](https://ja.wikipedia.org/wiki/%E3%83%A2%E3%83%8E%E3%82%A4%E3%83%89)

群は集合と二項演算の組であって、以下の条件を満たす。

- 結合法則
- 単位元の存在

もし逆元があるなら、群になる。

## コンストラクタ

```cpp
Group g()
```

引数がない場合、単位元で初期化するものとする。

## op

```cpp
Group op(Group a, Group b)
```

演算 $a \cdot b$ を行う。

## e

```cpp
Group e()
```

単位元を返す。

## モノイド

|クラス名|対象の集合|二項演算|単位元|
|--|--|--|--|
|`MonoidMul`|整数、実数など|乗算|$1$|
|`MonoidMax`|整数、実数など|$\max (a, b)$|最小値または $-\infty$|
|`MonoidMin`|整数、実数など|$\min (a, b)$|最大値または $\infty$|