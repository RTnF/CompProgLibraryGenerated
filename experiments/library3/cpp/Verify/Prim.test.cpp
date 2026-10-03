#define PROBLEM "https://onlinejudge.u-aizu.ac.jp/courses/library/5/GRL/2/GRL_2_A"
#include "Graph/Prim.hpp"

int main() {
    cin.tie(0);
    ios::sync_with_stdio(false);
    int V, E;
    cin >> V >> E;
    GraphL graph(V);
    for(int i = 0; i < E; ++i) {
        int s, t, d;
        cin >> s >> t >> d;
        graph.addBidirectionalEdge(s, t, d);
    }
    cout << graph.prim() << '\n';
}