#include <vector>
namespace other {
template<class T> struct Box { T value; Box(T x):value(x){} };
template<class T> struct OtherBox { T value; OtherBox(T x):value(x){} };
template<class T> struct Action {
 T delta; Action(T x):delta(x){}
 template<class V> V apply(V value) { return value.value+delta; }
};
}
