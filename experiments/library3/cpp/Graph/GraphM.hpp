#pragma once
#include "Template/SmallTemplate.hpp"

// グラフ(隣接行列)
template<class Cost = ll>
class GraphM {
    int n, m;
    vector<vector<Cost>> mat;
    vector<vector<Cost>> shortest_path_dist;
    vector<vector<int>> shortest_path_parent;
    bool has_negative_cycle = false;

public:
    static const Cost UNREACHABLE = numeric_limits<Cost>::max() >> 2;

    GraphM(int n_): n(n_), m(0), mat(n_, vector<Cost>(n_, GraphM::UNREACHABLE)) {
        for(int i = 0; i < n; ++i) {
            mat[i][i] = 0;
        }
    }

    void addEdge(int from, int to, Cost cost = 1) {
        mat[from][to] = cost;
        m++;
    }

    // 最短距離
    void warshallFloyd();
    Cost getDist(int from, int to) { return shortest_path_dist[from][to]; }
    vector<int> getShortestPath(int from, int to) {
        vector<int> path;
        for(int cur = to; cur != from; cur = shortest_path_parent[from][cur]) {
            path.emplace_back(cur);
            if(cur == -1) {
                return vector<int>();
            }
        }
        path.emplace_back(from);
        reverse(path.begin(), path.end());
        return path;
    }
    bool hasNegativeCycle() const { return has_negative_cycle; }

    template<class T>
    friend std::ostream &operator<<(std::ostream &, const GraphM<T> &);
};

template<class T>
ostream &operator<<(ostream &os, const GraphM<T> &graph) {
    os << "N = " << graph.n << ", M = " << graph.m << '\n';
    for(int i = 0; i < graph.n; ++i) {
        for(int j = 0; j < graph.n; ++j) {
            os << graph.mat[i][j] << " \n"[j == graph.n - 1];
        }
    }
    return os;
}