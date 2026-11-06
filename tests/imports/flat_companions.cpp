int main(){
 other::Action<long long> action(3);
 other::Box<long long> box(7);other::OtherBox<long long> other(9);
 return action.apply(box).value==10 && action.apply(other).value==12 ? 0:1;
}
