#pragma once
#include "array/doubling.hpp"
#include "graph/edge.hpp"

// 根付き木
template<class Cost = ll, class E = Edge<Cost>>
class Tree {
  int n_, root_;
  vector<vector<E>> adj;
  // 0の親は0, 深さ(根からの辺の数/コスト合計)
  vector<vector<int>> parent_, depth_, cost_depth_;
  vector<vector<int>> ancestor_; // 2**i回遡った祖先
  vector<int> farthest_node_;    // 最遠点
  vector<Cost> height_;          // 高さ(最遠点までの距離)

  // 返り値：最遠ノード O(N)
  void build_depth(int from) {
    if (farthest_node_[from] != -1) {
      return;
    }
    parent_[from] = vector<int>(n_);
    depth_[from] = vector<int>(n_);
    cost_depth_[from] = vector<int>(n_);
    parent_[from][from] = from;
    depth_[from][from] = 0;
    cost_depth_[from][from] = 0;
    basic_string<bool> visited(n_, false);
    stack<tuple<int, int, Cost>> s;
    Cost max_cost = -1;
    int farthest = -1;
    s.emplace(from, 0, 0);
    visited[from] = true;
    while (s.size()) {
      auto [node, d, dc] = s.top();
      s.pop();
      if (max_cost < dc) {
        max_cost = dc;
        farthest = node;
      }
      for (auto &&e: adj[node]) {
        if (!visited[e.to]) {
          visited[e.to] = true;
          parent_[from][e.to] = node;
          depth_[from][e.to] = d + 1;
          cost_depth_[from][e.to] = dc + e.cost;
          s.emplace(e.to, d + 1, dc + e.cost);
        }
      }
    }
    farthest_node_[from] = farthest;
    height_[from] = max_cost;
  }

public:
  Tree(int root, vector<int> &from, vector<int> &to, vector<Cost> &cost):
    n_(from.size() + 1), root_(root), adj(n_), parent_(n_), depth_(n_), cost_depth_(n_),
    farthest_node_(n_, -1), height_(n_, -1) {
    assert(n_ == (int)to.size() + 1);
    assert(n_ == (int)cost.size() + 1);
    for (int i = 0; i < n_ - 1; i++) {
      assert(0 <= from[i]);
      assert(from[i] < n_);
      assert(0 <= to[i]);
      assert(to[i] < n_);
      adj[from[i]].emplace_back(from[i], to[i], cost[i]);
      adj[to[i]].emplace_back(to[i], from[i], cost[i]);
    }
    build_depth(root_);
  }
  Tree(int root, vector<int> &from, vector<int> &to):
    n_(from.size() + 1), root_(root), adj(n_), parent_(n_), depth_(n_), cost_depth_(n_),
    farthest_node_(n_, -1), height_(n_, -1) {
    assert(n_ == (int)to.size() + 1);
    for (int i = 0; i < n_ - 1; i++) {
      assert(0 <= from[i]);
      assert(from[i] < n_);
      assert(0 <= to[i]);
      assert(to[i] < n_);
      adj[from[i]].emplace_back(from[i], to[i]);
      adj[to[i]].emplace_back(to[i], from[i]);
    }
    build_depth(root_);
  }
  Tree(int root, vector<int> &parent):
    n_(parent.size()), root_(root), adj(n_), parent_(n_), depth_(n_), cost_depth_(n_),
    farthest_node_(n_, -1), height_(n_, -1) {
    assert(n_ > 0);
    for (int i = 0; i < n_; i++) {
      if (i != parent[i] && 0 <= parent[i] && parent[i] < n_) {
        adj[parent[i]].emplace_back(parent[i], i);
        adj[i].emplace_back(i, parent[i]);
      }
    }
    build_depth(root_);
  }
  Tree(vector<int> &parent):
    n_(parent.size()), adj(n_), parent_(n_), depth_(n_), cost_depth_(n_), farthest_node_(n_, -1),
    height_(n_, -1) {
    assert(n_ > 0);
    int r = -1;
    for (int i = 0; i < n_; i++) {
      if (parent[i] == i || parent[i] < 0) {
        r = i;
      }
    }
    root_ = r;
    assert(r >= 0);
    for (int i = 0; i < n_; i++) {
      if (i != parent[i] && 0 <= parent[i] && parent[i] < n_) {
        adj[parent[i]].emplace_back(parent[i], i);
        adj[i].emplace_back(i, parent[i]);
      }
    }
    build_depth(root_);
  }

  vector<E> &operator[](int i) { return adj[i]; }

  template<class C_, class E_>
  friend ostream &operator<<(ostream &, const Tree<C_, E_> &);

  // 直径(from, to, cost) O(N)
  tuple<int, int, Cost> diameter() {
    build_depth(0);
    int f0 = farthest_node_[0];
    build_depth(f0);
    return {f0, farthest_node_[f0], height_[f0]};
  }

  // vから最遠点までの距離 O(N)
  vector<Cost> height() {
    auto [f0, f1, d] = diameter();
    build_depth(f1);
    vector<Cost> h(n_);
    for (int i = 0; i < n_; i++) {
      h[i] = max(cost_depth_[f0][i], cost_depth_[f1][i]);
    }
    return h;
  }

  // 経路 O(N)
  vector<int> path(int from, int to) const {
    stack<int> s;
    s.emplace(from);
    vector<int> path_parent(n_, -1);
    path_parent[from] = from;
    while (s.size()) {
      int node = s.top();
      if (node == to) {
        vector<int> path;
        for (int i = node; i != path_parent[i]; i = path_parent[i]) {
          path.emplace_back(i);
        }
        path.emplace_back(from);
        return path;
      }
      s.pop();
      for (auto &&e: adj[node]) {
        if (path_parent[e.to] == -1) {
          path_parent[e.to] = node;
          s.emplace(e.to);
        }
      }
    }
    return {}; // 到達しない
  }

  // ダブリングによる祖先構築 O(N log N)
  void build_ancestor() { ancestor_ = doubling(parent_[root_], n_ - 1); }

  // i回遡った祖先 O(log N)
  int ancestor(int v, int i) const {
    int k = 0;
    for (int j = 1; j <= i; j <<= 1, k++) {
      if (i & j) {
        v = ancestor_[k][v];
      }
    }
    return v;
  }

  // LCA O(log N)
  int lowest_common_ancestor(int u, int v) const {
    int du = depth_[root_][u];
    int dv = depth_[root_][v];
    if (du > dv) {
      u = ancestor(u, du - dv);
      du = dv;
    } else if (du < dv) {
      v = ancestor(v, dv - du);
    }
    if (u == v) {
      return u;
    }
    for (int k = bit_width((unsigned)du); k >= 0; k--) {
      int nu = ancestor_[k][u];
      int nv = ancestor_[k][v];
      if (nu != nv) {
        u = nu;
        v = nv;
      }
    }
    return ancestor_[0][u];
  }

  // 距離 O(log N)
  Cost distance(int u, int v) const {
    assert(0 <= u);
    assert(u < n_);
    assert(0 <= v);
    assert(v < n_);
    return cost_depth_[root_][u] + cost_depth_[root_][v]
         - cost_depth_[root_][lowest_common_ancestor(u, v)] * 2;
  }

  int depth(int v) const { return depth_[root_][v]; }

  Cost cost_depth(int v) const { return cost_depth_[root_][v]; }

  /**
   * @brief 全方位木DP
   * @tparam M モノイド
   * @tparam F (M, M) -> M
   * @tparam G M -> M
   * @param e 単位元
   * @param op モノイドの二項演算
   * @param sum_up すべての子の総積から木のDP値を求める
   * @return vector<M> 
   */
  template<class M, class F, class G>
  vector<M> full_tree_dp(M e, F op, G sum_up) {
    vector<M> dp(n_), dp_full(n_);
    vector<vector<M>> dp_sub(n_), dp_sub_left(n_), dp_sub_right(n_);
    for (int i = 0; i < n_; i++) {
      dp_sub[i].reserve(adj[i].size());
      dp_sub_left[i].reserve(adj[i].size());
      dp_sub_right[i].reserve(adj[i].size());
    }
    auto dfs = [&](auto &Self, int node, int par) -> void {
      dp[node] = e;
      for (auto &&edge: adj[node]) {
        if (edge.to != par) {
          Self(Self, edge.to, node);
          dp[node] = op(dp[node], dp[edge.to]);
          dp_sub[node].emplace_back(dp[edge.to]);
        }
      }
      dp[node] = sum_up(dp[node]);
      dp_sub_left[node].emplace_back(e);
      dp_sub_right[node].emplace_back(e);
      for (int i = 0; i < (int)adj[node].size(); i++) {
        if (adj[node][i].to != par) {
          dp_sub_left[node].emplace_back(op(dp_sub_left[node].back(), dp[adj[node][i].to]));
        }
      }
      for (int i = (int)adj[node].size() - 1; i >= 0; i--) {
        if (adj[node][i].to != par) {
          dp_sub_right[node].emplace_back(op(dp_sub_right[node].back(), dp[adj[node][i].to]));
        }
      }
    };
    dfs(dfs, root_, -1);

    queue<tuple<int, int, M>> q;
    q.emplace(root_, -1, e);
    dp_full[root_] = dp[root_];
    while (q.size()) {
      auto [node, par, v] = q.front();
      q.pop();
      if (node != root_) {
        dp_full[node] = sum_up(op(v, dp_sub_left[node].back()));
      }
      int i = 0;
      for (auto &&edge: adj[node]) {
        if (edge.to != par) {
          q.emplace(edge.to,
                    node,
                    sum_up(op(op(v, dp_sub_left[node][i]),
                              dp_sub_right[node][dp_sub_right[node].size() - i - 2])));
          i++;
        }
      }
    }
    return dp_full;
  }
};

template<class C_, class E_>
ostream &operator<<(ostream &os, const Tree<C_, E_> &graph) {
  os << "N = " << graph.n_ << '\n';
  for (const auto &ev: graph.adj) {
    for (const auto &e: ev) {
      os << e << '\n';
    }
  }
  return os;
}