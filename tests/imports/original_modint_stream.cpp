#include "template/small_template.hpp"
#include "modint/modint.hpp"
#include <iomanip>
#include <sstream>

template<uint32_t Mod> int run() {
  string operation, mode;
  while (cin >> operation >> mode) {
    uint64_t initial;
    cin >> initial;
    ModInt<Mod> value(initial);
    if (operation == "r") {
      size_t length;
      cin >> length;
      string text;
      for (size_t i = 0; i < length; ++i) {
        int c;
        cin >> c;
        text.push_back(static_cast<char>(c));
      }
      istringstream input(text);
      if (mode == "fail") input.setstate(ios::failbit);
      if (mode == "eof") input.setstate(ios::eofbit);
      if (mode == "bad") input.setstate(ios::badbit);
      if (mode == "throw_fail") input.exceptions(ios::failbit);
      if (mode == "throw_eof") input.exceptions(ios::eofbit);
      bool thrown = false;
      istream *returned = nullptr;
      try { returned = &(input >> value); }
      catch (const ios_base::failure &) { thrown = true; }
      cout << "r " << value.get() << ' ' << input.fail() << ' ' << input.eof()
           << ' ' << input.bad() << ' ' << thrown << ' ' << (returned == &input) << '\n';
    } else if (operation == "w") {
      ostringstream output;
      if (mode == "showpos") output << showpos;
      if (mode == "hex") output << hex << uppercase << showbase;
      if (mode == "octal") output << oct << showbase;
      if (mode == "padded") output << setw(12) << setfill('_');
      ostream &returned = output << value;
      string text = output.str();
      cout << "w " << (&returned == &output) << ' ' << text.size();
      for (unsigned char c : text) cout << ' ' << static_cast<unsigned>(c);
      cout << '\n';
    } else return 2;
  }
  return 0;
}
int main(int argc, char **argv) {
  if (argc != 2) return 2;
  switch (stoull(argv[1])) {
    case 2: return run<2>();
    case 7: return run<7>();
    case 998244353: return run<998244353>();
    case 2147483647: return run<2147483647>();
    case 4294967291: return run<4294967291>();
    default: return 2;
  }
}
