#include <vector>
namespace other {
template<class T,int N> struct Outer {
 struct Middle {
  struct Leaf {
   T x;
   Leaf():x(5){}
   Leaf(T value):x(value){}
   T get()const{return x;}
  };
 };
};
}
