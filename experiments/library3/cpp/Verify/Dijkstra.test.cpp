#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_A"
#include "Graph/Dijkstra.hpp"

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int V, E, r;
    cin >> V >> E >> r;
    GraphL<int> graph(V);
    for(int i = 0; i < E; ++i) {
        int s, t, d;
        cin >> s >> t >> d;
        graph.addEdge(s, t, d);
    }
    graph.dijkstra(r);
    for(int i = 0; i < V; ++i) {
        int dist = graph.getDist(r, i);
        if(dist >= 2000000000) {
            cout << "INF\n";
        } else {
            cout << dist << '\n';
        }
    }
}