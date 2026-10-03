#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/4/GRL_4_A"
#include "Graph/TopologicalSort.hpp"

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int V, E;
    cin >> V >> E;
    GraphL graph(V);
    for(int i = 0; i < E; ++i) {
        int s, t;
        cin >> s >> t;
        graph.addEdge(s, t);
    }
    cout << !graph.topologicalSortMinimum().size() << '\n';
}