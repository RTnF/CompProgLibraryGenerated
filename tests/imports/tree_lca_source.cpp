#ifndef TREE_SOURCE_HEADER
#define TREE_SOURCE_HEADER "../../experiments/library/cpp/tree/tree.hpp"
#endif
#include TREE_SOURCE_HEADER
#include <random>

// A naive parent walk is independent of the doubling table under test.
static int expected_lca(const vector<int>& p, const vector<int>& d, int u, int v) {
  while (d[u] > d[v]) u = p[u];
  while (d[v] > d[u]) v = p[v];
  while (u != v) { u = p[u]; v = p[v]; }
  return u;
}
static void check(Tree<>& tree, const vector<int>& parent, const vector<int>& depth) {
  tree.build_ancestor();
  for (int u = 0; u < (int)parent.size(); ++u)
    for (int v = 0; v < (int)parent.size(); ++v)
      assert(tree.lowest_common_ancestor(u,v) == expected_lca(parent,depth,u,v));
}
static void check_parent(vector<int> parent) {
  vector<int> depth(parent.size());
  for (int i = 1; i < (int)parent.size(); ++i) depth[i] = depth[parent[i]]+1;
  Tree<> tree(parent);
  check(tree,parent,depth);
}
static void enumerate(vector<int>& parent, int i) {
  if (i == (int)parent.size()) { check_parent(parent); return; }
  for (int p = 0; p < i; ++p) { parent[i] = p; enumerate(parent,i+1); }
}
int main(int argc, char**) {
  if (argc > 1) { // Four nodes, two siblings of depth 2, only two table rows.
    vector<int> parent{0,0,1,1};Tree<> tree(parent);tree.build_ancestor();
    assert(tree.lowest_common_ancestor(2,3) == 1);return 0;
  }
  for (int n = 2; n <= 8; ++n) { vector<int> parent(n);enumerate(parent,1); }
  for (int n : {3,4,7,8,15,16,31,32,63,64,127,128}) {
    vector<int> chain(n),star(n),fork(n);
    for (int i=1;i<n;++i) {chain[i]=i-1;fork[i]=(i-1)/2;}
    check_parent(chain);check_parent(star);check_parent(fork);
  }
  mt19937 random(20261108);
  for (int round=0;round<80;++round) {
    int n=2+random()%127, root=random()%n;
    vector<int> from,to;vector<ll> costs;
    vector<vector<int>> adj(n);
    for(int i=1;i<n;++i){int p=random()%i;from.push_back(p);to.push_back(i);costs.push_back(1);
      adj[p].push_back(i);adj[i].push_back(p);}
    vector<int> parent(n,-1),depth(n),order{root};parent[root]=root;
    for(int i=0;i<n;++i)for(int v:adj[order[i]])if(parent[v]<0){
      parent[v]=order[i];depth[v]=depth[order[i]]+1;order.push_back(v);}
    Tree<> edges(root,from,to);check(edges,parent,depth);
    Tree<> weighted(root,from,to,costs);check(weighted,parent,depth);
    Tree<> parents(root,parent);check(parents,parent,depth);
  }
  // No table access is needed on the equal-vertex early return.
  vector<int> one{0};Tree<> singleton(one);assert(singleton.lowest_common_ancestor(0,0)==0);
}
