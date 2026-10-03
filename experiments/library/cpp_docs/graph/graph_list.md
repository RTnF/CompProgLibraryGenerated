---
title: グラフ (隣接リスト形式)
documentation_of: //cpp/graph/graph_list.hpp
---
<link rel="stylesheet" type="text/css" href="../../css/common.css">

隣接リスト。  
最短距離と `Dijkstra Tree` のうちの一つをもつ

グラフアルゴリズム：
- [Bellman-Ford](bellman_ford.hpp)
- [Dijkstra](dijkstra.hpp)
- [lowlink](lowlink.hpp)
- [prim](prim.hpp)
- [Topological Sort](topological_sort.hpp)
- [Warshall-Floyd](warshall_floyd.hpp)

## コンストラクタ

```cpp
ListGraph<Cost = ll, E = Edge<Cost>> graph()
```

$n$ 頂点、結合がない状態で初期化する

## add_node

```cpp
void graph.add_node()
```

頂点を $1$ つ追加する

**計算量**

- ならし $ O(1) $

## add_edge

```cpp
void graph.add_edge(int from, int to, Args... args)
```

頂点 $from → to$ の有向辺を追加する  
`args` は `Edge` のコンストラクタに渡る

**計算量**

- ならし $ O(1) $

## add_bidirectional_edge

```cpp
void graph.add_bidirectional_edge(int from, int to, Args... args)
```

頂点 $from → to$ と $to → from$ の有向辺を追加する  
`args` は `Edge` のコンストラクタに渡る

**計算量**

- ならし $ O(1) $

## operator[]

```cpp
vector<E> graph.&operator[](int i)
```

頂点 $i$ の隣接リストを返す

## reset_shortest

```cpp
void graph.reset_shortest()
```

最短距離のキャッシュをクリアする。  
`add_edge` か `add_node` で発動する。

**計算量**

- キャッシュがある場合 $ O(size) $

## get_dist

```cpp
Cost graph.get_dist(int from, int to)
vector<Cost> graph.get_dist(int from)
```

キャッシュから最短距離を返す

## get_shortest_path

```cpp
vector<int> graph.get_shortest_path(int from, int to)
```

キャッシュから最短パスを求める

## 定数

```cpp
Cost ListGraph<Cost, E>::UNREACHABLE
Cost ListGraph<Cost, E>::NEGATIVE_CYCLE
```

- `UNREACHABLE` : 最短距離において到達不能 $(\infty)$ を表す
- `NEGATIVE_CYCLE` : 最短距離において負のループ $(-\infty)$ を表す

## operator<< (出力)

```cpp
ostream &operator<<(ostream &os, const ListGraph<C_, E_> &graph)
```

デバッグ用