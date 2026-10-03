---
title: ランレングス圧縮
documentation_of: //cpp/string/char_count.hpp
---
<link rel="stylesheet" type="text/css" href="../../css/common.css">

## char_count

```cpp
vector<pair<char, int>> char_count(const string &s)
```

**制約**

文字はASCIIに含まれる。

**計算量**

- $ O(|S|) $

**例**

```cpp
char_count("")
// -> []

char_count("abc")
// -> [('a', 1), ('b', 1), ('c', 1)]

char_count("aaaAAABBbb")
// -> [('a', 3), ('A', 3), ('B', 2), ('b', 2)]
```