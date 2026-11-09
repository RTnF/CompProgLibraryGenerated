#pragma once
#include <vector>  // the common nested generator audits the standard vector declarations of every source

namespace cp {

// Xorshift64 generator (https://ja.wikipedia.org/wiki/Xorshift). The state must be nonzero for a full period;
// the verified contract holds for every 64 bit state (state 0 stays 0).
// get() advances the state and returns the new state, in [0, 2^64). Time and extra space O(1).
// The generator lowers a class whose fields are scalars to functions whose fields are reference parameters,
// so every method is checked as a function of the fields it touches.
class Xor64 {
  unsigned long long s;

public:
  Xor64(unsigned long long s_) : s(s_) {}
  unsigned long long get() {
    unsigned long long x = s;
    x = x ^ (x << 7);
    s = x ^ (x >> 9);
    return s;
  }
};

} // namespace cp
