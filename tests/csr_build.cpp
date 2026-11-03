#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/csr_build.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261015);
    for (int round = 0; round < 5000; ++round) {
        int n = 1 + random() % 8;
        int m = random() % 20;
        std::vector<int> from(m), to(m);
        for (int i = 0; i < m; ++i) {
            from[i] = random() % n;
            to[i] = random() % n;
        }
        std::vector<int> head(n + 1, 0), target(m, 0), pos(n, 0);
        cp::csr_build(from, to, head, target, pos, n);
        assert(head[0] == 0 && head[n] == m);
        for (int v = 0; v < n; ++v) assert(head[v] <= head[v + 1]);
        for (int v = 0; v < n; ++v) {
            std::vector<int> expected;
            for (int i = 0; i < m; ++i) if (from[i] == v) expected.push_back(to[i]);
            std::vector<int> got(target.begin() + head[v], target.begin() + head[v + 1]);
            assert(got == expected);
        }
    }
    return 0;
}
