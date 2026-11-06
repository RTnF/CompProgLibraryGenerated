#include <iostream>
using GroupSumSourceWitness = ::GroupSum<long long>;
using Target = GroupSumSourceWitness;
int main(){Target fresh;if(fresh.x!=0)return 1;auto id=Target::e();Target x(4),y(3);auto minus=x.inv();auto added=op(x,y);x.x=9;std::cout<<id.x<<" "<<minus.x<<" "<<added.x<<" "<<x.x;std::cout<<"\n";}
