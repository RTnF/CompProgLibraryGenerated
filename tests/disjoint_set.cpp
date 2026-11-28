#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/union_find/disjoint_set.hpp"
#include "fixtures/disjoint_set_checks.hpp"

int main() {
  check_disjoint_set<cp::DisjointSet>();
}
