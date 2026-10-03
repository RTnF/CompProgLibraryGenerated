#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_B"
#include "Graph/BellmanFord.hpp"

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int V, E, r;
    cin >> V >> E >> r;
    GraphL graph(V);
    for(int i = 0; i < E; ++i) {
        int s, t, d;
        cin >> s >> t >> d;
        graph.addEdge(s, t, d);
    }
    graph.bellmanFord(r);
    for(int i = 0; i < V; ++i) {
        ll dist = graph.getDist(r, i);
        if(dist == GraphL<>::NEGATIVE_CYCLE) {
            cout << "NEGATIVE CYCLE\n";
            return 0;
        }
    }
    for(int i = 0; i < V; ++i) {
        ll dist = graph.getDist(r, i);
        if(dist == GraphL<>::UNREACHABLE) {
            cout << "INF\n";
        } else {
            cout << dist << '\n';
        }
    }
}