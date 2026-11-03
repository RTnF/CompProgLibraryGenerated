#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/tree_arc_costs.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261106);
    for (int round = 0; round < 20000; ++round) {
        int m = random() % 12;
        std::vector<long long> cost(m + random() % 3);
        for (auto &c : cost) c = (long long)(random() % 2000001) - 1000000;
        if (random() % 8 == 0 && m > 0) cost[random() % m] = (random() & 1) ? (long long)9e18 : -(long long)9e18;
        int size = 2 * m + random() % 3;
        std::vector<long long> ac(size, -7);
        cp::tree_arc_costs(cost, ac, m);
        // the costs exactly as the original constructor attaches them to both arcs of an edge
        for (int i = 0; i < m; ++i) assert(ac[2 * i] == cost[i] && ac[2 * i + 1] == cost[i]);
        for (int k = 2 * m; k < size; ++k) assert(ac[k] == -7);  // the rest is untouched
    }
    return 0;
}
