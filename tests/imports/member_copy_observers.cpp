#include <vector>
#include <cassert>
struct Box {std::vector<int> values;int count;};
int main(){std::vector<std::vector<int>> outer{{91}};int &saved=outer[0][0];
 int *allocation=&saved;outer.reserve(outer.capacity()+1);
 assert(&outer[0][0]==allocation && saved==91);
 Box original{{19},42};Box copied(original);copied.values[0]=7;
 assert(original.values[0]==19 && copied.count==42 && saved==91);}
