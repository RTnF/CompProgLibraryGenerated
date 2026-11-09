#include <cassert>
#include <iostream>
#include <limits>
#include <type_traits>
#include <vector>
#ifdef CANDIDATE_API
#include "../../experiments/verification/algebraic_structure/monoid_lazy.hpp"
using namespace cp;
#else
#include "../../experiments/library/cpp/algebraic_structure/monoid_lazy.hpp"
#endif

static std::vector<int> events;
struct Traced {
  int value;
  Traced(int v) : value(v) { events.push_back(v); }
  Traced(const Traced &x) : value(x.value) { events.push_back(100+value); }
  Traced &operator=(const Traced &x) { value=x.value; events.push_back(400+value); return *this; }
  ~Traced() { events.push_back(200+value); }
  friend Traced operator+(const Traced &a,const Traced &b) { return a.value+b.value; }
  friend Traced operator*(int a,const Traced &b) { return a*b.value; }
  friend Traced operator*(const Traced &a,int b) { return a.value*b; }
  friend bool operator<(const Traced &a,const Traced &b) { events.push_back(300); return a.value<b.value; }
};
namespace std {
template<> class numeric_limits<Traced> {
public:
  static Traced min() { return -50; }
  static Traced max() { return 50; }
};
}

static void print() {
  for (int event : events) std::cout << event << ',';
  std::cout << '\n';
  events.clear();
}

template<class R> static void extrema() {
  using Max=typename R::RangeMax; using Min=typename R::RangeMin;
  {
    Max mx, a(Traced(2)), b(Traced(3));
    Min mn, c(Traced(2)), d(Traced(3));
    auto maxIdentity=Max::e(); auto minIdentity=Min::e();
    auto maximum=op(a,b); auto minimum=op(c,d);
    assert(mx.x.value==-50 && mn.x.value==50 && maxIdentity.x.value==-50 && minIdentity.x.value==50);
    assert(maximum.x.value==3 && minimum.x.value==2);
  }
  print();
}

template<class R> static void add_extrema() {
  using A=typename R::RangeAdd; using Max=typename R::RangeMax; using Min=typename R::RangeMin;
  {
    A f(Traced(3)), g(Traced(-2)); auto id=A::id(); auto fg=compose(f,g);
    const Max input(Traced(7)); const Min inputMin(Traced(9));
    auto maximum=fg.template apply<Max>(input); auto minimum=fg.apply(inputMin);
    static_assert(std::is_same_v<decltype(maximum),Max>);
    assert(id.v.value==0 && fg.v.value==1 && maximum.x.value==8 && minimum.x.value==10);
    assert(input.x.value==7 && inputMin.x.value==9);
  }
  print();
}

template<class R> static void set_extrema() {
  using A=typename R::RangeSet; using Max=typename R::RangeMax; using Min=typename R::RangeMin;
  for (bool noop : {false,true}) {
    {
      A f(Traced(3)), g(Traced(5)); f.noop=noop;
      auto id=A::id(); auto fg=compose(f,g);
      const Max input(Traced(7)); const Min inputMin(Traced(9));
      auto maximum=fg.template apply<Max>(input); auto minimum=id.apply(inputMin);
      assert(id.noop && fg.v.value==(noop?5:3) && maximum.x.value==(noop?5:3));
      assert(minimum.x.value==9 && input.x.value==7 && inputMin.x.value==9);
    }
    print();
  }
}

template<class R,bool IsSet> static void sum() {
  using S=typename R::RangeSum;
  {
    S zero, a(Traced(7),2), b(Traced(5),3); auto identity=S::e(); auto added=op(a,b);
    assert(zero.x.value==0 && zero.size==0 && identity.x.value==0 && identity.size==0);
    assert(added.x.value==12 && added.size==5);
  }
  print();
  if constexpr (IsSet) {
    using A=typename R::RangeSet;
    for (bool noop : {false,true}) {
      {
        A f(Traced(3)), g(Traced(5)); f.noop=noop;
        auto id=A::id(); auto fg=compose(f,g); const S input(Traced(7),2);
        auto result=fg.apply(input); auto kept=id.apply(input);
        assert(result.x.value==(noop?10:6) && result.size==2 && kept.x.value==7 && kept.size==2);
        assert(input.x.value==7 && input.size==2);
      }
      print();
    }
  } else {
    using A=typename R::RangeAdd;
    {
      A f(Traced(3)), g(Traced(-2)); auto id=A::id(); auto fg=compose(f,g); const S input(Traced(7),2);
      auto result=fg.apply(input); auto kept=id.apply(input);
      assert(result.x.value==9 && result.size==2 && kept.x.value==7 && kept.size==2);
      assert(input.x.value==7 && input.size==2);
    }
    print();
  }
}

int main() {
  extrema<RangeAddRangeMaxMin<Traced>>();
  extrema<RangeSetRangeMaxMin<Traced>>();
  add_extrema<RangeAddRangeMaxMin<Traced>>();
  set_extrema<RangeSetRangeMaxMin<Traced>>();
  sum<RangeAddRangeSum<Traced>,false>();
  sum<RangeSetRangeSum<Traced>,true>();
}
