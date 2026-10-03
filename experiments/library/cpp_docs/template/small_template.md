---
title: 共通ヘッダー
documentation_of: //cpp/template/small_template.hpp
---
<link rel="stylesheet" type="text/css" href="../../css/common.css">

## 一括インクルード、 `std::` の省略

```cpp
#include <bits/stdc++.h>
using namespace std;
```

## 型の略記

```cpp
using ll = int64_t;
using ull = uint64_t;
using ld = long double;
```

`long long` ではなく、 `long` として扱われる。

## 定数

```cpp
constexpr ll INF = 4e+18;
constexpr ld EPS = 1e-12L;
constexpr ld PI = 3.14159265358979323846L;
```

`INF + INF` がオーバーフローしないように