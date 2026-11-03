#include "union_find_public_compat.hpp"
#include <algorithm>
#include <random>
#include <type_traits>
#include <utility>
using UF=cp::UnionFind;
static_assert(std::is_constructible<UF>::value && std::is_constructible<UF,int>::value);
int (UF::*groups_mutable)()=&UF::num_groups;
int (UF::*groups_const)()const=&UF::num_groups;
bool (UF::*same_mutable)(int,int)=&UF::same;
bool (UF::*same_const)(int,int)const=&UF::same;
int (UF::*size_mutable)(int)=&UF::size;
int (UF::*size_const)(int)const=&UF::size;
int main() {
  UF empty;
  const UF& zero=empty;
  assert((empty.*groups_mutable)()==0 && (zero.*groups_const)()==0);
  std::mt19937 random(20261025);
  for(int n : {1,2,3,4,7,16,64,127}) {
    UF uf(n);
    std::vector<int> label(n);
    for(int i=0;i<n;++i) label[i]=i;
    int groups=n;
    for(int step=0;step<2048;++step) {
      int a=int(random()%unsigned(n)),b=int(random()%unsigned(n));
      const UF& view=uf;
      bool expected=label[a]==label[b];
      assert((view.*same_const)(a,b)==expected);
      assert((uf.*same_mutable)(a,b)==expected);
      assert((view.*size_const)(a)==std::count(label.begin(),label.end(),label[a]));
      assert((uf.*size_mutable)(b)==std::count(label.begin(),label.end(),label[b]));
      if(step%2==0) {
        int from=label[a],to=label[b];
        uf.unite(a,b);
        if(from!=to) {
          --groups;
          for(int& x:label) if(x==from) x=to;
        }
      }
      assert((uf.*groups_mutable)()==groups && (view.*groups_const)()==groups);
      assert((uf.root(a)==uf.root(b))==(label[a]==label[b]));
    }
    const UF frozen=uf;
    for(int i=0;i<n;++i) {
      assert(frozen.size(i)==std::count(label.begin(),label.end(),label[i]));
      for(int j=0;j<n;++j) assert(frozen.same(i,j)==(label[i]==label[j]));
    }
    UF copied(frozen);
    UF moved(std::move(copied));
    assert(moved.num_groups()==groups && std::as_const(moved).num_groups()==groups);
    assert(copied.num_groups()==groups && std::as_const(copied).num_groups()==groups);
  }
}
