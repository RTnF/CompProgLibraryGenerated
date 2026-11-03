#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree_height.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261102);
    for (int round = 0; round < 20000; ++round) {
        int size = random() % 12;
        int n = size == 0 ? 0 : random() % (size + 1);  // only the first n entries are written
        std::vector<long long> c0(size), c1(size), h(size);
        for (int i = 0; i < size; ++i) {
            c0[i] = (long long)(random() % 2001) - 1000;
            c1[i] = (long long)(random() % 2001) - 1000;
            h[i] = (long long)(random() % 2001) - 1000;
        }
        std::vector<long long> before = h;
        cp::tree_height(c0, c1, h, n);
        for (int i = 0; i < size; ++i) {
            if (i < n)
                assert(h[i] == std::max(c0[i], c1[i]));
            else
                assert(h[i] == before[i]);
        }
    }
    return 0;
}
