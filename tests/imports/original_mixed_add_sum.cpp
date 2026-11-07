int main() {
 using R=RangeAddRangeSum<long long>;
 R::RangeAdd f(3),g(2); auto id=R::RangeAdd::id(); auto h=compose(f,g);
 R::RangeSum x(7,4), y(2,1), z; auto e=R::RangeSum::e(); auto s=op(x,y);
 auto a=f.apply(x);
 return id.v==0 && h.v==5 && a.x==19 && a.size==4 && x.x==7 && x.size==4 &&
        z.x==0 && z.size==0 && e.x==0 && e.size==0 && s.x==9 && s.size==5 ? 0:1;
}
