---
title: 群 (Group)
documentation_of: //cpp/algebraic_structure/group.hpp
---
<link rel="stylesheet" type="text/css" href="../../css/common.css">

[Wikipedia - 群 (数学)](https://ja.wikipedia.org/wiki/%E7%BE%A4_(%E6%95%B0%E5%AD%A6))

群は集合と二項演算の組であって、以下の条件を満たす。

- 結合法則
- 単位元の存在
- 逆元の存在

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

## inv

```cpp
Group g.inv()
```

$g$ の逆元を返す。

## 群

|クラス名|対象の集合|二項演算|単位元|逆元|
|--|--|--|--|--|
|`GroupSum`|整数、実数など|加算|$0$|$-x$|
|`GroupMul`|整数、実数など(0を除く)|乗算|$1$|$\frac{1}{x}$|
|`GroupAffine`|アフィン写像 $y=a x + b$|合成 $y = a_1 (a_2 x + b) + b$|$y = x$|$ y = \frac{x}{a} - \frac{b}{a} $|