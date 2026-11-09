#include "../../experiments/library/cpp/template/small_template.hpp"
#include "../../library/union_find/union_find.hpp"
#include <cstdlib>
#include <iostream>
#include <string>

int main(int argc, char **argv) {
    if (argc != 5) return 2;
    const std::string method = argv[1];
    const int n = std::stoi(argv[2]), a = std::stoi(argv[3]), b = std::stoi(argv[4]);
    cp::UnionFind uf(n);
    if (method == "new") std::cout << uf.num_groups();
    else if (method == "root") std::cout << uf.root(a);
    else if (method == "size") std::cout << uf.size(a);
    else if (method == "same") std::cout << uf.same(a,b);
    else if (method == "unite") std::cout << uf.unite(a,b);
    else return 2;
    std::cout << '\n';
}
