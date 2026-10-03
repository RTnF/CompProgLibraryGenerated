#pragma once
#include "Template/SmallTemplate.hpp"
#include "Graph/GraphL.hpp"

/**
 * ベルマンフォード法
 * 有向グラフの単一始点最短経路 O(EV)
 * 到達不能：max, 負閉路を通る：min
 * https://mhrb-minase.hatenablog.com/entry/2019/08/20/003915
 */
template<class Cost, class E>
void GraphL<Cost, E>::bellmanFord(int start_node) {
    if(shortest_path_dist.count(start_node)) {
        return;
    }
    vector<Cost> dist(n, GraphL::UNREACHABLE);
    vector<int> parent(n, -1);
    dist[start_node] = 0;
    for(int i = 0; i < n - 1; ++i) {
        for(auto &es: adj) {
            for(auto &e: es) {
                if(dist[e.from] != GraphL::UNREACHABLE && dist[e.from] + e.cost < dist[e.to]) {
                    dist[e.to] = dist[e.from] + e.cost;
                    parent[e.to] = e.from;
                }
            }
        }
    }
    for(int i = 0; i < n; ++i) {
        for(auto &es: adj) {
            for(auto &e: es) {
                if(dist[e.from] != GraphL::UNREACHABLE && dist[e.from] + e.cost < dist[e.to]) {
                    dist[e.to] = GraphL::NEGATIVE_CYCLE;
                    parent[e.to] = -1;
                }
            }
        }
    }
    shortest_path_dist[start_node] = move(dist);
    shortest_path_parent[start_node] = move(parent);
}