#define PROBLEM "https://judge.yosupo.jp/problem/shortest_path"
#include "Graph/Dijkstra.hpp"

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int V, E, start, goal;
    cin >> V >> E >> start >> goal;
    GraphL graph(V);
    for(int i = 0; i < E; ++i) {
        int s, t, d;
        cin >> s >> t >> d;
        graph.addEdge(s, t, d);
    }
    graph.dijkstra(start);
    ll dist = graph.getDist(start, goal);
    if(dist == GraphL<>::UNREACHABLE) {
        cout << "-1\n";
    } else {
        auto ans = graph.getShortestPath(start, goal);
        int n = (int)ans.size() - 1;
        cout << dist << ' ' << n << '\n';
        for(int i = 0; i < n; ++i) {
            cout << ans[i] << ' ' << ans[i + 1] << '\n';
        }
    }
}