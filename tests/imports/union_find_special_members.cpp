#include "../../experiments/library/cpp/template/small_template.hpp"
namespace legacy {
#include "../../experiments/library/cpp/union_find/union_find.hpp"
}
#include "../../experiments/verification/data_structure/union_find.hpp"
#include <type_traits>
#include <utility>

// Private-field observation is enabled only for this test translation unit.
// Moved-from indexed methods are never called without restoring the receiver.
template<class U> struct Snapshot {
  std::vector<int> ps;
  int groups, n;
  explicit Snapshot(const U& u) : ps(u._ps), groups(u._num_groups), n(u._n) {}
  void equal(const U& u) const {
    assert(ps == u._ps && groups == u._num_groups && n == u._n);
  }
};
struct Observed {
  int ctor_bad_invariant = 0, assign_bad_invariant = 0, self_bad_invariant = 0;
  bool operator==(const Observed& other) const {
    return ctor_bad_invariant == other.ctor_bad_invariant &&
      assign_bad_invariant == other.assign_bad_invariant && self_bad_invariant == other.self_bad_invariant;
  }
};
template<class U> Observed exercise(int n) {
  static_assert(std::is_copy_constructible_v<U> && std::is_copy_assignable_v<U>);
  static_assert(std::is_nothrow_move_constructible_v<U> && std::is_nothrow_move_assignable_v<U>);
  U source(n);
  for (int i = 1; i <= n/2; ++i) source.unite(0,i);
  source._ps.reserve(source._ps.size()+17);
  const Snapshot<U> original(source);
  const U& constant = source;
  U copied(constant);
  original.equal(copied);
  original.equal(source);
  assert(copied._ps.capacity() == copied._ps.size()); // GCC 13.3 profile.
  if (n) assert(copied._ps.data() != source._ps.data());
  if (n) copied.root(n-1);
  original.equal(source);
  U target(n+2);
  target._ps.reserve(n+40);
  const auto old_capacity = target._ps.capacity();
  int* const target_ref = target._ps.data();
  U& assigned = (target = constant);
  assert(&assigned == &target);
  original.equal(target);
  assert(target._ps.capacity() == old_capacity);
  if (n) { assert(target._ps.data() == target_ref); assert(*target_ref == source._ps[0]); }
  U& same_target = target;
  target = same_target;
  original.equal(target);
  assert(target._ps.capacity() == old_capacity);

  int* const source_ref = source._ps.data();
  U moved(std::move(source));
  original.equal(moved);
  if (n) { assert(moved._ps.data() == source_ref); assert(*source_ref == original.ps[0]); }
  assert(source._num_groups == original.groups && source._n == original.n);
  assert(source.num_groups() == original.groups);
  assert(source._ps.size() <= source._ps.capacity());
  Observed result;
  result.ctor_bad_invariant = source._ps.size() != static_cast<std::size_t>(source._n);
  source = moved;
  original.equal(source);
  if (n) source.root(n-1);
  const Snapshot<U> after_restore(source);
  int* const assignment_ref = source._ps.data();
  U destination(n+3);
  U& move_assigned = (destination = std::move(source));
  assert(&move_assigned == &destination);
  after_restore.equal(destination);
  if (n) { assert(destination._ps.data() == assignment_ref); assert(*assignment_ref == after_restore.ps[0]); }
  assert(source._num_groups == after_restore.groups && source._n == after_restore.n);
  assert(source.num_groups() == after_restore.groups);
  assert(source._ps.size() <= source._ps.capacity());
  result.assign_bad_invariant = source._ps.size() != static_cast<std::size_t>(source._n);
  source = U(n);
  assert(source._ps.size() == static_cast<std::size_t>(source._n));
  if (n) assert(source.size(n-1) == 1);

  U self(n);
  U& same_self = self;
  self = std::move(same_self);
  assert(self._n == n && self._num_groups == n && self.num_groups() == n);
  assert(self._ps.size() <= self._ps.capacity());
  result.self_bad_invariant = self._ps.size() != static_cast<std::size_t>(self._n);
  self = U(n);
  if (n) assert(self.root(n-1) == n-1);
  return result;
}
int main() {
  int n;
  while (std::cin >> n) {
    assert(n >= 0);
    const auto old = exercise<legacy::UnionFind>(n);
    const auto next = exercise<cp::UnionFind>(n);
    assert(old == next);
    std::cout << n << ' ' << next.ctor_bad_invariant << ' ' << next.assign_bad_invariant
      << ' ' << next.self_bad_invariant << '\n';
  }
}
