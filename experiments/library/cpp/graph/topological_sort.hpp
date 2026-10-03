#pragma once
#include "graph/graph_list.hpp"
#include "template/small_template.hpp"

/**
 * トポロジカルソート(Kahn) O(E + V)
 * 返り値：DAGの場合根から順、非DAGの場合空
 * https://ja.wikipedia.org/wiki/トポロジカルソート
 */
template <class Cost, class E>
vector<int> ListGraph<Cost, E>::topological_sort() {
  vector<int> sorted_node, in_count(n_, 0);
  // vector<bool> visited(n_, false);
  sorted_node.reserve(n_);
  stack<int> st;
  for (auto &es : adj) {
    for (auto &e : es) {
      in_count[e.to]++;
    }
  }
  for (int i = 0; i < n_; ++i) {
    if (in_count[i] == 0) {
      st.emplace(i);
    }
  }
  while (!st.empty()) {
    int v = st.top();
    st.pop();
    // visited[v] = true;
    sorted_node.emplace_back(v);
    for (auto &e : adj[v]) {
      if (--in_count[e.to] == 0) {
        st.emplace(e.to);
      }
    }
  }
  if ((int)sorted_node.size() != n_) {
    return vector<int>();
  }
  return sorted_node;
}

/**
 * トポロジカルソート(Kahn)
 * 辞書順最小O(E + V log V)
 */
template <class Cost, class E>
vector<int> ListGraph<Cost, E>::topological_sort_minimum() {
  vector<int> sorted_node, in_count(n_, 0);
  // vector<bool> visited(n_, false);
  sorted_node.reserve(n_);
  priority_queue<int, vector<int>, greater<int>> pq;
  for (auto &es : adj) {
    for (auto &e : es) {
      in_count[e.to]++;
    }
  }
  for (int i = 0; i < n_; ++i) {
    if (in_count[i] == 0) {
      pq.emplace(i);
    }
  }
  while (!pq.empty()) {
    int v = pq.top();
    pq.pop();
    // visited[v] = true;
    sorted_node.emplace_back(v);
    for (auto &e : adj[v]) {
      if (--in_count[e.to] == 0) {
        pq.emplace(e.to);
      }
    }
  }
  if ((int)sorted_node.size() != n_) {
    return vector<int>();
  }
  return sorted_node;
}