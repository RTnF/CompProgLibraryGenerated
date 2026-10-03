#pragma once
#include "Template/SmallTemplate.hpp"
#include "Graph/GraphL.hpp"

/**
 * トポロジカルソート(Kahn) O(E + V)
 * 返り値：DAGの場合根から順、非DAGの場合空
 * https://ja.wikipedia.org/wiki/トポロジカルソート
 */
template<class Cost, class E>
vector<int> GraphL<Cost, E>::topologicalSort() {
    vector<int> sorted_node, in_count(n, 0);
    vector<bool> visited(n, false);
    sorted_node.reserve(n);
    stack<int> st;
    for(auto &es: adj) {
        for(auto &e: es) {
            in_count[e.to]++;
        }
    }
    for(int i = 0; i < n; ++i) {
        if(in_count[i] == 0) {
            st.emplace(i);
        }
    }
    while(!st.empty()) {
        int v = st.top();
        st.pop();
        visited[v] = true;
        sorted_node.emplace_back(v);
        for(auto &e: adj[v]) {
            if(--in_count[e.to] == 0) {
                st.emplace(e.to);
            }
        }
    }
    if(sorted_node.size() != n) {
        return vector<int>();
    }
    return sorted_node;
}

/**
 * トポロジカルソート(Kahn)
 * 辞書順最小O(E + V log V)
 */
template<class Cost, class E>
vector<int> GraphL<Cost, E>::topologicalSortMinimum() {
    vector<int> sorted_node, in_count(n, 0);
    vector<bool> visited(n, false);
    sorted_node.reserve(n);
    priority_queue<int, vector<int>, greater<int>> pq;
    for(auto &es: adj) {
        for(auto &e: es) {
            in_count[e.to]++;
        }
    }
    for(int i = 0; i < n; ++i) {
        if(in_count[i] == 0) {
            pq.emplace(i);
        }
    }
    while(!pq.empty()) {
        int v = pq.top();
        pq.pop();
        visited[v] = true;
        sorted_node.emplace_back(v);
        for(auto &e: adj[v]) {
            if(--in_count[e.to] == 0) {
                pq.emplace(e.to);
            }
        }
    }
    if(sorted_node.size() != n) {
        return vector<int>();
    }
    return sorted_node;
}