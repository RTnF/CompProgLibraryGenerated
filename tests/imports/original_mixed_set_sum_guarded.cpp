#include <limits>
int main(int argc,char**){
 using R=RangeSetRangeSum<long long>;
 R::RangeSet f;f.v=std::numeric_limits<long long>::max();
 R::RangeSum x(7,argc>1?2:4);
 if(argc>1)f.noop=false;
 auto a=f.apply(x);
 return a.x==7 && a.size==4 && x.x==7 && x.size==4?0:1;
}
