#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/1/GRL_1_C"
#include "Graph/WarshallFloyd.hpp"

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int V, E;
    cin >> V >> E;
    GraphM g(V);
    for(int i = 0; i < E; ++i) {
        int s, t;
        ll d;
        cin >> s >> t >> d;
        g.addEdge(s, t, d);
    }
    g.warshallFloyd();
    if(g.hasNegativeCycle()) {
        cout << "NEGATIVE CYCLE\n";
    } else {
        for(int i = 0; i < V; ++i) {
            for(int j = 0; j < V; ++j) {
                if(g.getDist(i, j) >= GraphM<>::UNREACHABLE) {
                    cout << "INF";
                } else {
                    cout << g.getDist(i, j);
                }
                cout << " \n"[j == V - 1];
            }
        }
    }
}