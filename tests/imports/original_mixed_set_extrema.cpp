int main(){
 using R=RangeSetRangeMaxMin<long long>;
 R::RangeSet f(3),g(2),none; auto id=R::RangeSet::id();
 auto fg=compose(f,g),ng=compose(none,g),fn=compose(f,none);
 R::RangeMax a(7),az; R::RangeMin b(9),bz;
 auto ae=R::RangeMax::e();auto be=R::RangeMin::e();
 auto am=op(a,az);auto bm=op(b,bz);
 auto x=f.apply(a),ax=none.apply(a);auto y=f.apply(b),by=none.apply(b);
 return id.noop && id.v==0 && fg.v==3 && !fg.noop && ng.v==2 && !ng.noop &&
  fn.v==3 && !fn.noop && x.x==3 && ax.x==7 && y.x==3 && by.x==9 &&
  a.x==7 && b.x==9 && am.x==7 && bm.x==9 && az.x==ae.x && bz.x==be.x ? 0:1;
}
