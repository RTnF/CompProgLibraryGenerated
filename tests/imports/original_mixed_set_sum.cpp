int main(){
 using R=RangeSetRangeSum<long long>;
 R::RangeSet f(3),g(2),none;auto id=R::RangeSet::id();
 auto fg=compose(f,g),ng=compose(none,g),fn=compose(f,none);
 R::RangeSum x(7,4),y(2,1),z;auto e=R::RangeSum::e();auto s=op(x,y);
 auto a=f.apply(x),b=none.apply(x),c=f.apply(R::RangeSum(7,-4));
 return !f.noop && none.noop && id.noop && id.v==0 && fg.v==3 && !fg.noop &&
  ng.v==2 && !ng.noop && fn.v==3 && !fn.noop && a.x==12 && a.size==4 &&
  b.x==7 && b.size==4 && c.x==-12 && c.size==-4 && x.x==7 && x.size==4 &&
  z.x==0 && z.size==0 && e.x==0 && e.size==0 && s.x==9 && s.size==5 ?0:1;
}
