#include "../../experiments/library/cpp/template/small_template.hpp"
namespace legacy {
#include "../../experiments/library/cpp/union_find/union_find.hpp"
}
#include "../../experiments/verification/data_structure/union_find.hpp"
#include <random>
#include <string>
#include <type_traits>

static_assert(std::is_same_v<decltype(&cp::UnionFind::same), bool (cp::UnionFind::*)(int,int)>);
static_assert(std::is_same_v<decltype(&cp::UnionFind::root), int (cp::UnionFind::*)(int)>);
static_assert(std::is_same_v<decltype(&cp::UnionFind::size), int (cp::UnionFind::*)(int)>);
static_assert(std::is_same_v<decltype(&cp::UnionFind::num_groups), int (cp::UnionFind::*)()>);
static_assert(std::is_same_v<decltype(&cp::UnionFind::unite), int (cp::UnionFind::*)(int,int)>);
static_assert(std::is_default_constructible_v<cp::UnionFind>);
static_assert(std::is_constructible_v<cp::UnionFind,int>);

// Built with -fno-access-control only to inspect both classes' original private
// representation. Neither header is modified or instrumented by this harness.
template<class U> int apply(U &uf, const std::string &method, int a, int b) {
    if (method == "root") return uf.root(a);
    if (method == "size") return uf.size(a);
    if (method == "same") return uf.same(a,b);
    if (method == "unite") return uf.unite(a,b);
    assert(method == "num_groups");
    return uf.num_groups();
}
void compare(const legacy::UnionFind &old, const cp::UnionFind &next) {
    assert(old._ps == next._ps);
    assert(old._num_groups == next._num_groups);
    assert(old._n == next._n);
}
int main(int argc, char **argv) {
    if (argc > 1) {
        assert(argc == 6);
        const std::string kind = argv[1], method = argv[2];
        const int n = std::stoi(argv[3]), a = std::stoi(argv[4]), b = std::stoi(argv[5]);
        if (kind == "old") { legacy::UnionFind uf(n); apply(uf,method,a,b); }
        else { cp::UnionFind uf(n); apply(uf,method,a,b); }
        return 0;
    }
    legacy::UnionFind empty_old;
    cp::UnionFind empty_next;
    compare(empty_old,empty_next);
    assert(empty_next._ps.empty());
    std::string method;
    int n, groups, a, b;
    while (std::cin >> method >> n >> groups >> a >> b) {
        std::vector<int> ps(n);
        for (int &x : ps) std::cin >> x;
        legacy::UnionFind old(n);
        cp::UnionFind next(n);
        old._ps = next._ps = ps;
        old._num_groups = next._num_groups = groups;
        const int result = apply(old,method,a,b);
        assert(result == apply(next,method,a,b));
        compare(old,next);
        std::cout << result << ' ' << next._num_groups << ' ' << next._n;
        for (int x : next._ps) std::cout << ' ' << x;
        std::cout << '\n';
    }
    std::mt19937 random(20261015);
    for (int count : {0,1,2,3,4,8,16,32,128}) {
        legacy::UnionFind old(count);
        cp::UnionFind next(count);
        compare(old,next);
        for (int step=0; count>0 && step<4000; ++step) {
            int a0 = random()%count, b0 = random()%count;
            const char *methods[] = {"root","size","same","unite","num_groups"};
            const std::string op = methods[random()%5];
            assert(apply(old,op,a0,b0) == apply(next,op,a0,b0));
            compare(old,next);
            if (step%31 == 0) {
                auto old_copy = old;
                auto next_copy = next;
                assert(old_copy.root(a0) == next_copy.root(a0));
                compare(old_copy,next_copy);
                old = old_copy;
                next = next_copy;
            }
        }
    }
}
