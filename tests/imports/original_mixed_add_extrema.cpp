int main(){
 using R=RangeAddRangeMaxMin<long long>;
 R::RangeAdd f(3),g(-2);auto id=R::RangeAdd::id();auto fg=compose(f,g);
 R::RangeMax a(7),az;R::RangeMin b(9),bz;
 auto ae=R::RangeMax::e();auto be=R::RangeMin::e();
 auto am=op(a,az);auto bm=op(b,bz);auto x=f.apply(a);auto y=f.apply(b);
 return id.v==0 && fg.v==1 && am.x==7 && bm.x==9 && x.x==10 && y.x==12 &&
  a.x==7 && b.x==9 && az.x==ae.x && bz.x==be.x?0:1;
}
