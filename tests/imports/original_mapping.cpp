#include <iostream>
using AffineSourceWitness = ::Affine<long long>;
using Target = AffineSourceWitness;
int main(){Target id;Target x(2,1),y(3,4);auto z=compose(x,y);auto inv=Target(1,4).inv();std::cout<<id.a<<" "<<id.b<<" "<<x.apply(3LL)<<" "<<x.apply(3)<<" "<<x.apply(0.5)<<" "<<z.a<<" "<<z.b<<" "<<inv.a<<" "<<inv.b;std::cout<<"\n";}
