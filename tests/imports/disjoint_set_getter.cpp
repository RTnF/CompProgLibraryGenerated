#include "experiments/library3/cpp/Graph/UnionFind.hpp"
#include <cassert>
int main() {
  DisjointSet empty(0);
  assert(empty.getNum()==0);
  for(int n=1;n<=32;++n) {
    DisjointSet uf(n);
    assert(uf.getNum()==n);
    for(int i=1;i<n;++i) {
      uf.unite(0,i);
      assert(uf.getNum()==n-i);
      uf.unite(i,0);
      assert(uf.getNum()==n-i);
      assert(uf.same(0,i));
      assert(uf.size(i)==i+1);
    }
    DisjointSet copied(uf);
    assert(copied.getNum()==uf.getNum());
    DisjointSet moved(std::move(copied));
    assert(moved.getNum()==uf.getNum());
    assert(copied.getNum()==uf.getNum());
    DisjointSet assigned(0);
    assigned=std::move(moved);
    assert(assigned.getNum()==uf.getNum());
    assert(moved.getNum()==uf.getNum());
  }
}
