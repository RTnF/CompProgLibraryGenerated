#include "../../experiments/verification/template/update_extrema.hpp"

template bool cp::chmax<int, int>(int &, const int &);
template bool cp::chmin<int, int>(int &, const int &);
template bool cp::chmax<unsigned int, unsigned int>(unsigned int &, const unsigned int &);
template bool cp::chmin<unsigned int, unsigned int>(unsigned int &, const unsigned int &);
