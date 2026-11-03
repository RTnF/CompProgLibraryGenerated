#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree_find_root.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261104);
    for (int round = 0; round < 20000; ++round) {
        int size = random() % 14;
        int n = size == 0 ? 0 : random() % (size + 1);  // only the first n entries are examined
        std::vector<int> parent(size);
        for (int i = 0; i < size; ++i) {
            int kind = random() % 5;
            if (kind == 0) parent[i] = i;
            else if (kind == 1) parent[i] = -1 - (int)(random() % 3);
            else parent[i] = (int)(random() % 20);
        }
        // the loop of the original constructor, with the test written as the original does
        int expect = -1;
        for (int i = 0; i < n; i++) {
            if (parent[i] == i || parent[i] < 0) expect = i;
        }
        assert(cp::tree_find_root(parent, n) == expect);
    }
    return 0;
}
