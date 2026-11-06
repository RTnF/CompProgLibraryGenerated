#include <iostream>
using GroupAffineSourceWitness = ::GroupAffine<long long>;
using Target = GroupAffineSourceWitness;
int main(){Target id;Target x(2,1),y(3,4);auto z=op(x,y);auto inv=Target(1,4).inv();std::cout<<id.a<<" "<<id.b<<" "<<z.a<<" "<<z.b<<" "<<inv.a<<" "<<inv.b;std::cout<<"\n";}
