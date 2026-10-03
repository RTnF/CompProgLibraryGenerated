---
title: 素集合データ構造 (Union Find)
documentation_of: //cpp/set/disjoint_set_union.hpp
---
<link rel="stylesheet" type="text/css" href="../../css/common.css">

## コンストラクタ

```cpp
DisjointSetUnion dsu()
DisjointSetUnion dsu(int n)
```

$n$ 頂点、結合がない状態で初期化する

**計算量**

- $O(n)$


## unite

```cpp
int unite(int a, int b)
```

頂点 $a, b$ を結合する

**制約**

- $ 0 \le a < n $
- $ 0 \le b < n $

**計算量**

- ならし $ O(\alpha(n)) $


## same

```cpp
bool same(int a, int b)
```

頂点 $a, b$ が連結か

**制約**

- $0 \leq a < n$
- $0 \leq b < n$

**計算量**

- ならし $O(\alpha(n))$

## root

```cpp
int root(int a)
```

頂点 $a$ の属する連結成分の代表元

**制約**

- $0 \leq a < n$

**計算量**

- ならし $O(\alpha(n))$

## size

```cpp
int size(int a)
```

頂点 $a$ の属する連結成分のサイズ

**制約**

- $0 \leq a < n$

**計算量**

- ならし $O(\alpha(n))$
