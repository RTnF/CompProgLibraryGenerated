"""Differential tests of the C++ -> Lean translation (docs/translation.md).

From the translated signatures this module generates two interpreters of one command language, one in C++
(calling the public header) and one in Lean (running the translated functions), runs both on the same
generated commands and requires identical output. The translator itself is not proved; this test is the
check that its output behaves like the C++ code (docs/trust_policy.md).

Command language (whitespace separated tokens, one command per line):
  call <function> <args...>          a free function; prints its outputs
  new <constructor> <args...>        constructs object number k (0, 1, ... in order of creation)
  do <k> <method> <args...>          calls a member function of object k; prints its outputs
  field <Class.field> <k>           reads a public field of object k
Values: an integer; a bool as 0/1; a vector or string as its length and its elements; a pair as its two values.
Input streams: a token count followed by canonical decimal tokens or `x` (invalid input).
Character streams also accept `bytes <count> <0..255>...` with canonical byte codes.
Output streams: no argument tokens (a fresh default-formatted empty output stream).
Stream output: EOF/failure bits for input, byte count and character codes for output.
Mutable object arguments: updated in the object table and reported as `objref`.
Outputs of a call: the returned value (if not void), then each non-const reference argument after the call.
"""

from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_translate as lt  # noqa: E402

ROOT = lt.ROOT


def cpp_value_type(qual: str, instance: dict) -> str:
    s = re.sub(r"\bconst\b", "", qual).replace("&", "").strip()
    for name, value in instance.items():
        s = re.sub(rf"\b{name}\b", value, s)
    return re.sub(r"\s+", " ", s)


# These template bindings use mathematical integers under the component's
# no-narrowing-overflow premise. Their C++ expressions promote to int, rather
# than computing in UInt8/UInt16 at every operator. Explicit concrete source
# declarations/casts still go through lean_translate.parse_type and are rejected.
SMALL_UNSIGNED_BINDINGS = {"unsigned char": 8, "unsigned short": 16, "unsigned short int": 16, "char16_t": 16}


def instance_type(cpp: str):
    if cpp in SMALL_UNSIGNED_BINDINGS:
        return lt.INT32
    return lt.parse_type(cpp, set(), set())


def lean_instance_type(cpp: str) -> str:
    return lt.lean_type(instance_type(cpp))


def type_traits_binding(cpp):
    return lt.known_type_traits(cpp)


CPP_PRELUDE = r"""
#include <iostream>
#include <limits>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>
#if __cplusplus >= 202002L
#include <compare>
#endif

namespace difftest {
template <class X> void rd(std::vector<X> &v);
template <class A, class B> void rd(std::pair<A, B> &p);
template <class X> void pr(const std::vector<X> &v);
template <class A, class B> void pr(const std::pair<A, B> &p);
template <class X> void rd(X &x) {
  if constexpr (std::is_unsigned_v<X>) { unsigned long long v; std::cin >> v; x = (X)v; }
  else { long long v; std::cin >> v; x = (X)v; }
}
inline void rd(std::string &s) {
  std::size_t n;
  std::cin >> n;
  s.resize(n);
  for (auto &ch : s) rd(ch);
}
inline void rd(bool &x) { int v; std::cin >> v; x = v != 0; }
template <class X> void rd(std::vector<X> &v) {
  long long n; std::cin >> n; v.assign(n, X());
  for (long long i = 0; i < n; i++) { X e; rd(e); v[i] = e; }
}
template <class A, class B> void rd(std::pair<A, B> &p) { rd(p.first); rd(p.second); }
template <class X> void pr(const X &x) {
  if constexpr (std::is_unsigned_v<X>) std::cout << ' ' << (unsigned long long)x;
  else std::cout << ' ' << (long long)x;
}
#if __cplusplus >= 202002L
inline void pr(std::strong_ordering x) { std::cout << ' ' << (x < 0 ? -1 : x > 0 ? 1 : 0); }
#endif
inline void pr(bool x) { std::cout << ' ' << (x ? 1 : 0); }
template <class X> void pr(const std::vector<X> &v) {
  std::cout << ' ' << v.size();
  for (std::size_t i = 0; i < v.size(); i++) pr((X)v[i]);
}
template <class A, class B> void pr(const std::pair<A, B> &p) { pr(p.first); pr(p.second); }
} // namespace difftest
"""


LEAN_PRELUDE = r"""
namespace DiffTest

-- Differential tests compare values, not time. A test-only cost instance lets
-- them execute numeric contracts whose complexity is unspecified by the standard.
instance : Proofs.Cpp.NumericCost where
  gcd _ _ := 1
  lcm _ _ := 1

class Rd (α : Type) where
  rd : List String → Option (α × List String)

instance : Rd Int where
  rd | t :: ts => (t.toInt?).map (·, ts) | [] => none

instance : Rd UInt64 where
  rd | t :: ts => (t.toNat?).map (fun v => (UInt64.ofNat v, ts)) | [] => none

instance : Rd UInt32 where
  rd | t :: ts => (t.toNat?).map (fun v => (UInt32.ofNat v, ts)) | [] => none

instance : Rd Bool where
  rd | t :: ts => (t.toInt?).map (fun v => (v ≠ 0, ts)) | [] => none

partial def rdArray {α : Type} [Rd α] (n : Nat) (acc : Array α) (ts : List String) : Option (Array α × List String) :=
  if n = 0 then some (acc, ts) else do
    let (x, ts) ← Rd.rd ts
    rdArray (n - 1) (acc.push x) ts

instance {α : Type} [Rd α] : Rd (Array α) where
  rd ts := do
    let (n, ts) ← (Rd.rd ts : Option (Int × List String))
    rdArray n.toNat #[] ts

instance {α β : Type} [Rd α] [Rd β] : Rd (α × β) where
  rd ts := do
    let (a, ts) ← Rd.rd ts
    let (b, ts) ← Rd.rd ts
    some ((a, b), ts)

class Pr (α : Type) where
  pr : α → String

instance : Pr Int where pr x := s!" {x}"
instance : Pr UInt64 where pr x := s!" {x.toNat}"
instance : Pr UInt32 where pr x := s!" {x.toNat}"
instance : Pr Bool where pr x := if x then " 1" else " 0"
instance : Pr Ordering where
  pr | .lt => " -1" | .eq => " 0" | .gt => " 1"
instance {α : Type} [Pr α] : Pr (Array α) where
  pr v := s!" {v.size}" ++ String.join (v.toList.map Pr.pr)
instance {α β : Type} [Pr α] [Pr β] : Pr (α × β) where
  pr p := Pr.pr p.1 ++ Pr.pr p.2
instance : Pr Unit where pr _ := ""

def arg {α : Type} [Rd α] (ts : List String) : IO (α × List String) :=
  match Rd.rd ts with
  | some r => pure r
  | none => throw (IO.userError "bad argument")

end DiffTest
"""


CPP_STREAM_PRELUDE = r"""
#include <sstream>
#include <stdexcept>
#include <limits>
namespace difftest {
inline bool stream_token(const std::string &s) {
  if (s == "x" || s == "0") return true;
  std::size_t i = !s.empty() && s[0] == '-' ? 1 : 0;
  if (i == s.size() || s[i] < '1' || s[i] > '9') return false;
  for (++i; i < s.size(); ++i) if (s[i] < '0' || s[i] > '9') return false;
  return true;
}
inline void rd(std::istringstream &s) {
@@BYTE_INPUT@@
  long long n;
  if (!(std::cin >> n) || n < 0) throw std::runtime_error("invalid stream token count");
  std::string input, token;
  for (long long i = 0; i < n; ++i) {
    if (!(std::cin >> token)) throw std::runtime_error("missing stream token");
    if (!stream_token(token)) throw std::runtime_error("unsupported stream token");
    if (i) input += ' ';
    input += token;
  }
  s.str(input);
}
inline void rd(std::ostringstream &) {}
inline void pr(const std::istream &s) { std::cout << ' ' << s.eof() << ' ' << s.fail(); }
inline void pr(const std::istringstream &s) { pr(static_cast<const std::istream &>(s)); }
inline void pr(const std::ostream &s) {
  const auto &buffer = dynamic_cast<const std::ostringstream &>(s);
  const auto text = buffer.str();
  std::cout << ' ' << text.size();
  for (unsigned char c : text) std::cout << ' ' << static_cast<unsigned>(c);
}
inline void pr(const std::ostringstream &s) { pr(static_cast<const std::ostream &>(s)); }
} // namespace difftest
"""

CPP_CHARACTER_BYTE_INPUT = r"""
  static_assert(std::numeric_limits<unsigned char>::digits == 8,
                "character differential binding needs 8-bit bytes");
  static_assert(std::numeric_limits<@@CHAR_TYPE@@>::is_signed == @@CHAR_SIGNED@@,
                "character differential binding has the wrong character signedness");
  std::cin >> std::ws;
  if (std::cin.peek() == 'b') {
    std::string mode;
    long long n;
    if (!(std::cin >> mode >> n) || mode != "bytes" || n < 0)
      throw std::runtime_error("invalid stream byte count");
    std::string input;
    for (long long i = 0; i < n; ++i) {
      std::string token;
      if (!(std::cin >> token) || !stream_token(token) || token == "x"
          || token[0] == '-' || token.size() > 3)
        throw std::runtime_error("invalid stream byte");
      const int byte = std::stoi(token);
      if (byte > 255) throw std::runtime_error("invalid stream byte");
      input.push_back(static_cast<char>(byte));
    }
    s.str(input);
    return;
  }
"""

LEAN_CHARACTER_BYTE_READER = r"""
partial def streamBytes : Nat → List String → Option (List Char × List String)
  | 0, ts => some ([], ts)
  | n + 1, t :: ts => do
    let byte ← t.toNat?
    if byte > 255 || toString byte != t then none else do
      let (rest, ts) ← streamBytes n ts
      some (Char.ofNat byte :: rest, ts)
  | _, [] => none
"""

LEAN_SIGNED_STREAM_OPS = r"""
instance : @StreamRead Int streams where
  read input old := do
    if input.failed then return (old, input)
    if input.eof then return (old, { input with failed := true })
    match input.tokens with
    | [] => return (old, { input with eof := true, failed := true })
    | none :: rest => return (0, { input with tokens := rest, failed := true })
    | some value :: rest =>
      let clipped := max (@@MIN@@ : Int) (min (@@MAX@@ : Int) value)
      return (clipped, { input with tokens := rest, eof := rest.isEmpty, failed := clipped != value })

instance : @StreamWrite Int streams where
  write output value := pure (String.append output (toString value))
"""

LEAN_UNSIGNED_STREAM_OPS = r"""
instance : @StreamRead @@TYPE@@ streams where
  read input old := do
    if input.failed then return (old, input)
    if input.eof then return (old, { input with failed := true })
    match input.tokens with
    | [] => return (old, { input with eof := true, failed := true })
    | none :: rest => return (0, { input with tokens := rest, failed := true })
    | some value :: rest =>
      let overflow := decide (value.natAbs > @@MAX@@)
      let result := if overflow then @@MAX@@ else
        if value < 0 then @@CAPACITY@@ - value.natAbs else value.natAbs
      return (@@TYPE@@.ofNat result,
        { input with tokens := rest, eof := rest.isEmpty, failed := overflow })

instance : @StreamWrite @@TYPE@@ streams where
  write output value := pure (String.append output (toString value.toNat))
"""

LEAN_CHARACTER_STREAM_OPS = r"""
instance : @StreamRead Int streams where
  read input old := do
    if input.failed then return (old, input)
    if input.eof then return (old, { input with failed := true })
    match input.chars.dropWhile (fun c => [9, 10, 11, 12, 13, 32].contains c.toNat) with
    | [] => return (old, { input with chars := [], eof := true, failed := true })
    | c :: rest =>
      let value : Int := if @@CHAR_SIGNED@@ then
        (if c.toNat < 128 then c.toNat else (c.toNat : Int) - 256) else c.toNat
      return (value, { input with chars := rest })

instance : @StreamWrite Int streams where
  write output value := pure (String.push output (Char.ofNat (value % 256).toNat))
"""

LEAN_STREAM_PRELUDE = r"""
namespace DiffTest
open Proofs.Cpp
structure StreamInput where
  tokens : List (Option Int)
  chars : List Char := []
  eof : Bool := false
  failed : Bool := false

instance streams : Streams where
  Input := StreamInput
  Output := String

-- Concrete decimal or ASCII-character test binding, not a universal std::istream parser.
-- The protocol only accepts canonical decimal tokens or the invalid token "x".
partial def streamTokens : Nat → List String → Option (List (Option Int) × List String)
  | 0, ts => some ([], ts)
  | n + 1, t :: ts => do
    let token ← if t == "x" then some none else do
      let value ← t.toInt?
      if toString value != t then none else some (some value)
    let (rest, ts) ← streamTokens n ts
    some (token :: rest, ts)
  | _, [] => none

@@BYTE_READER@@
instance : Rd (@IStream streams) where
  rd ts := do
    if ts.head? == some "bytes" then
@@RAW_INPUT@@
    else
      let (n, ts) ← (Rd.rd ts : Option (Int × List String))
      if n < 0 then none else do
        let (tokens, ts) ← streamTokens n.toNat ts
        some ((@@INPUT_VALUE@@ : StreamInput), ts)

instance : Rd (@OStream streams) where
  rd ts := some ("", ts)

@@NUMERIC_OPS@@
instance : @StreamWrite StreamChar streams where
  write output value := pure (String.push output (Char.ofNat (value.code % 256).toNat))

instance : Pr (@IStream streams) where
  pr s := s!" {if s.eof then 1 else 0} {if s.failed then 1 else 0}"
instance : Pr (@OStream streams) where
  pr s := " " ++ toString (String.length s) ++ String.join
    ((String.toList s).map fun c => " " ++ toString c.toNat)
end DiffTest
"""


class Harness:
    def __init__(self, source: Path, instance: dict, lean_module: str, deps=(), standard="c++17", calls=None):
        self.selected_calls = None if calls is None else frozenset(calls)
        self.source = source
        self.instance = instance             # template parameter -> C++ type
        self.lean_module = lean_module
        tr = lt.Translator(lt.source_decls(source, standard), source.read_bytes(),
                           [(lt.source_decls(Path(d), standard), Path(d).read_bytes()) for d in deps])
        translated = tr.translate()
        self.numeric_trait_parameters = sorted(set(re.findall(r'Cpp\.NumericTraits "(\w+)"', translated)))
        self.tr = tr
        selected_requirements = ' '.join(r for info, sig in self.callables()
            if sig.public and not (info is not None and sig.is_static)
            for r in tr.built_functions[id(sig)].reqs.items)
        self.source_stream_contracts = sorted(set(re.findall(
            r'Cpp\.SourceStream(Read|Write) "(\w+)" (\w+)', selected_requirements)))
        self.source_stream_only = bool(self.source_stream_contracts) and not re.search(
            r'Cpp\.Stream(?:Read|Write) (?!Cpp\.StreamChar)\w+', selected_requirements)
        self.type_trait_parameters = sorted(set(re.findall(r'Cpp\.TypeTraits "(\w+)"', selected_requirements)))
        self.mod_to_u32_parameters = sorted(set(re.findall(r'Cpp\.ModToUInt32 "(\w+)"', selected_requirements)))
        self.value_parameters = {}
        for values in [*(c.value_params for c in tr.classes.values()),
                       *(sig.value_params for _, sig in self.callables(unfiltered=True))]:
            for name, ty in values.items():
                if name in self.value_parameters and (self.value_parameters[name] != ty
                        or self.value_parameters[name].width != ty.width):
                    raise lt.Unsupported(f"different non-type parameter types sharing binding {name}")
                self.value_parameters[name] = ty
        if self.selected_calls is not None:
            known = {sig.lean_name.removeprefix("cp.") for info, sig in self.callables(unfiltered=True)
                     if sig.public and not (info is not None and sig.is_static)}
            unknown = self.selected_calls - known
            if unknown:
                raise lt.Unsupported(f"unknown or non-public differential calls: {sorted(unknown)}")
        policies = {pol for _, sig in self.callables() for pol in sig.policies}
        self.policy_class = {k: re.sub(r"<.*", "", v).removeprefix("cp::") for k, v in instance.items() if k in policies}
        self.lean_instance = {k: (lt.lean_type(lt.parse_value_arg(v, self.value_parameters[k], {}))
                                  if k in self.value_parameters else lean_instance_type(v))
                              for k, v in instance.items() if k not in policies}
        for k, v in instance.items():
            if k in policies or k in self.value_parameters:
                continue
            ty = instance_type(v)
            if ty.kind == "vec":   # a container parameter T: its element type is T_value_type
                self.lean_instance[f"{k}_value_type"] = lt.lean_type(ty.args[0])
        self.has_streams = any(t.kind in ("istream", "ostream")
                               for _, sig in self.callables() for t in [sig.ret, *[p[1] for p in sig.params]])
        self.stream_bits = 64
        self.stream_unsigned = False
        self.stream_character = False
        if self.has_streams:
            signed_bits = {"short": 16, "short int": 16, "int": 32, "std::int32_t": 32, "int32_t": 32,
                           "long": 64, "long int": 64, "long long": 64, "long long int": 64,
                           "ll": 64, "std::int64_t": 64, "int64_t": 64}
            values = [] if self.source_stream_only else [v for k, v in instance.items()
                if k not in policies and k not in self.value_parameters]
            models = []
            message = "stream differential protocol needs one uniform numeric or character model"
            for value in values:
                if value in signed_bits:
                    models.append((signed_bits[value], False, False))
                elif value in ("char", "signed char"):
                    models.append((8, False, True))
                elif value in SMALL_UNSIGNED_BINDINGS:
                    bits = SMALL_UNSIGNED_BINDINGS[value]
                    models.append((bits, True, bits == 8))
                elif value in lt.UNSIGNED_NAMES:
                    models.append((32 if lt.UNSIGNED_NAMES[value].kind == "u32" else 64, True, False))
                else:
                    raise lt.Unsupported(message)
            if len(set(models)) > 1:
                raise lt.Unsupported(message)
            if models:
                self.stream_bits, self.stream_unsigned, self.stream_character = models[0]


    def callables(self, *, unfiltered=False):
        out = []
        for kind, item in self.tr.order:
            if kind == "fn":
                out.append((None, item))
            else:
                for sig in item.methods:
                    out.append((item, sig))
        if self.selected_calls is not None and not unfiltered:
            out = [(info, sig) for info, sig in out
                   if sig.lean_name.removeprefix("cp.") in self.selected_calls]
        return out

    def param_quals(self, sig):
        return [p.get("type", {}).get("qualType", "") for p in lt.inner(sig.node) if p.get("kind") == "ParmVarDecl"]

    # ------------------------------------------------------------------ C++
    def cpp_class(self, info):
        args = [self.instance[t] for t in info.tparams]
        if info.name in self.tr.nested_record_names:
            family, member = self.tr.nested_record_names[info.name]
            return f"cp::{family}<{', '.join(args)}>::{member}"
        return f"cp::{info.name}" + (f"<{', '.join(args)}>" if args else "")

    def cpp_driver(self) -> str:
        include = os.path.relpath(self.source.resolve(), (ROOT / "tests/diff").resolve())
        lines = [f'#include "../../experiments/library/cpp/template/small_template.hpp"',
                 f'#include "{include}"', CPP_PRELUDE,
                 (CPP_STREAM_PRELUDE.replace("@@BYTE_INPUT@@",
                     CPP_CHARACTER_BYTE_INPUT.replace("@@CHAR_TYPE@@",
                       "unsigned char" if self.stream_unsigned else (
                         "char" if "char" in self.instance.values() else "signed char"))
                       .replace("@@CHAR_SIGNED@@", "false" if self.stream_unsigned else "true")
                     if self.stream_character else "") if self.has_streams else ""), "int main() {", "  std::string cmd, name;"]
        classes = [item for kind, item in self.tr.order if kind == "class"]
        checked_traits = {packet for fn in self.tr.built_functions.values()
                          for packet in fn.type_trait_bindings}
        checked_traits.update((self.instance[p], *type_traits_binding(self.instance[p]))
                              for p in set(self.type_trait_parameters) | set(self.mod_to_u32_parameters))
        if self.mod_to_u32_parameters or checked_traits:
            lines.append('  static_assert(std::numeric_limits<unsigned int>::digits == 32);')
            lines.append('  static_assert(std::numeric_limits<long>::digits == 63);')
            lines.append('  static_assert(std::numeric_limits<long long>::digits == 63);')
        for cpp, signed, int128 in sorted(checked_traits):
            if cpp == "wchar_t":
                lines.append('  static_assert(std::numeric_limits<wchar_t>::digits == 31);')
            elif cpp in ("char16_t", "char32_t"):
                lines.append(f'  static_assert(std::numeric_limits<{cpp}>::digits == {16 if cpp == "char16_t" else 32});')
            lines.append(f'  static_assert(std::is_signed_v<{cpp}> == {str(signed).lower()});')
            lines.append(f'  static_assert(std::is_same_v<std::remove_cv_t<{cpp}>, __int128> == {str(int128).lower()});')
        if self.source_stream_contracts:
            lines.append('  static_assert(sizeof(int) == 4 && sizeof(long) == 8 && sizeof(long long) == 8);')
        for info in classes:
            lines.append(f"  std::vector<{self.cpp_class(info)}> objects_{info.name};")
        lines.append("  while (std::cin >> cmd >> name) {")
        for info in classes:
            for name, ty, _ in info.fields:
                if name in info.public_fields and self.field_is_observable(ty):
                    lines.append(f'    if (cmd == "field" && name == "{info.name}.{name}") {{')
                    lines.append('      long long k; std::cin >> k; std::cout << "ok";')
                    lines.append(f'      difftest::pr(objects_{info.name}[k].{name}); std::cout << "\\n"; continue;')
                    lines.append('    }')
        for info, sig in self.callables():
            if (sig.is_static and info is not None) or not sig.public:
                continue
            quals = self.param_quals(sig)
            decls, names = [], []
            for i, q in enumerate(quals):
                pty = sig.params[i][1]
                if pty.kind == "cls":
                    # an object argument is given by its number
                    decls.append(f"long long a{i}k; std::cin >> a{i}k; auto &a{i} = objects_{pty.name}[a{i}k];")
                else:
                    t = {"istream": "std::istringstream", "ostream": "std::ostringstream"}.get(pty.kind,
                                                                                          cpp_value_type(q, self.instance))
                    decls.append(f"{t} a{i}; difftest::rd(a{i});")
                names.append(f"a{i}")
            if info is None:
                targs = [self.instance[t.removesuffix("_value_type")] if t.removesuffix("_value_type") in sig.containers
                         else self.instance[t] for t in sig.tparams]
                # Hidden friends are found by argument-dependent lookup only.
                hidden_friend = sig.node.get("lean_hidden_friend", False)
                if hidden_friend:
                    # Class template parameters do not make its friend a function template.
                    targs = []
                callee = ("" if hidden_friend else "cp::") + sig.cpp_name + (f"<{', '.join(targs)}>" if targs else "")
                key = f"call {sig.lean_name.removeprefix('cp.')}"
                call = f"{callee}({', '.join(names)})"
            elif sig.is_ctor:
                key = f"new {sig.lean_name.removeprefix('cp.')}"
                call = None
            else:
                key = f"do {sig.lean_name.removeprefix('cp.')}"
                call = f"objects_{info.name}[k].{sig.cpp_name}({', '.join(names)})"
            cmd, label = key.split(" ", 1)
            lines.append(f'    if (cmd == "{cmd}" && name == "{label}") {{')
            lines.append('      {')
            if cmd == "do":
                lines.append("        long long k; std::cin >> k;")
            for d in decls:
                lines.append("        " + d)
            if cmd == "new":
                lines.append(f"        objects_{info.name}.emplace_back({', '.join(names)});")
                lines.append("        std::cout << \"new\\n\";")
            else:
                if sig.ret.kind == "cls":
                    lines.append(f"        objects_{sig.ret.name}.push_back({call});")
                    lines.append("        std::cout << \"ok obj\";")
                elif sig.ret.kind != "void":
                    ref = "&" if sig.ret.kind in ("istream", "ostream") else ""
                    lines.append(f"        auto {ref}r = {call};")
                    lines.append("        std::cout << \"ok\"; difftest::pr(r);")
                else:
                    lines.append(f"        {call};")
                    lines.append("        std::cout << \"ok\";")
                for i, (pname, pty, is_ref) in enumerate(sig.params):
                    if is_ref:
                        if pty.kind == "cls":
                            lines.append('        std::cout << " objref";')
                        else:
                            lines.append(f"        difftest::pr(a{i});")
                lines.append("        std::cout << '\\n';")
            lines.append("        continue;")
            lines.append("      }")
            lines.append("    }")
        lines.append("    return 3;")
        lines.append("  }")
        lines.append("}")
        return "\n".join(lines) + "\n"

    # ------------------------------------------------------------------ Lean
    @staticmethod
    def field_is_observable(ty):
        if ty.kind in ("vec", "pair"):
            return all(Harness.field_is_observable(t) for t in ty.args)
        return ty.kind in ("int", "u32", "u64", "bool", "tparam", "ordering")

    def lean_type_inst(self, ty):
        if ty.kind in ("istream", "ostream"):
            return "Proofs." + lt.lean_type(ty)
        return lt.lean_type(lt.subst(ty, list(self.lean_instance), [lt.Ty("tparam", v) for v in self.lean_instance.values()]))

    def lean_driver(self) -> str:
        classes = [item for kind, item in self.tr.order if kind == "class"]
        streams = ""
        if self.has_streams:
            ops = LEAN_CHARACTER_STREAM_OPS if self.stream_character else (
                LEAN_UNSIGNED_STREAM_OPS if self.stream_unsigned else LEAN_SIGNED_STREAM_OPS)
            streams = LEAN_STREAM_PRELUDE.replace("@@NUMERIC_OPS@@", ops)
            input_value = "{ tokens }"
            if self.stream_character:
                input_value = ('{ tokens, chars := (String.intercalate " " (tokens.map '
                               'fun token => match token with | none => "x" | some n => toString n)).toList }')
            streams = streams.replace("@@INPUT_VALUE@@", input_value)
            streams = streams.replace("@@BYTE_READER@@", LEAN_CHARACTER_BYTE_READER if self.stream_character else "")
            raw_input = "      none"
            if self.stream_character:
                raw_input = ("      let (n, rest) ← (Rd.rd ts.tail : Option (Int × List String))\n"
                             "      if n < 0 then none else do\n"
                             "        let (chars, rest) ← streamBytes n.toNat rest\n"
                             "        some (({ tokens := [], chars } : StreamInput), rest)")
            streams = streams.replace("@@RAW_INPUT@@", raw_input)
            streams = streams.replace("@@MIN@@", str(-(2 ** (self.stream_bits - 1))))
            maximum = 2 ** (self.stream_bits if self.stream_unsigned else self.stream_bits - 1) - 1
            streams = streams.replace("@@MAX@@", str(maximum))
            streams = streams.replace("@@CAPACITY@@", str(2 ** self.stream_bits))
            streams = streams.replace("@@TYPE@@", "Int" if self.stream_unsigned and self.stream_bits < 32
                                      else "UInt" + str(self.stream_bits))
            streams = streams.replace("@@CHAR_SIGNED@@", "false" if self.stream_unsigned else "true")
            concrete_ops = []
            for direction, source, carrier in self.source_stream_contracts:
                bits = 32 if source in ('int', 'unsigned_int') else 64
                unsigned = source.startswith('unsigned_')
                template = LEAN_UNSIGNED_STREAM_OPS if unsigned else LEAN_SIGNED_STREAM_OPS
                read, write = template.split('instance : @StreamWrite', 1)
                if direction == 'Read':
                    operation = read.replace('instance : @StreamRead', f'instance : @SourceStreamRead "{source}"')
                else:
                    operation = f'instance : @SourceStreamWrite "{source}"' + write
                operation = operation.replace('@@TYPE@@', carrier)
                operation = operation.replace('@@MIN@@', str(-(2**(bits-1))))
                operation = operation.replace('@@MAX@@', str(2**(bits if unsigned else bits-1)-1))
                operation = operation.replace('@@CAPACITY@@', str(2**bits))
                concrete_ops.append(operation)
            streams += '\nnamespace DiffTest\nopen Proofs.Cpp\n' + '\n'.join(concrete_ops) + '\nend DiffTest\n'
        # A template's Div/Mod instances are chosen at the concrete call site.
        # Lean's default integer operators use Euclidean division, whereas C++
        # signed arithmetic truncates toward zero. Concrete non-template Int
        # operations are already emitted as Cpp.tdiv/tmod by the translator.
        integer_ops = ""
        packet_integers = any(instance_type(cpp).kind == "int"
                              for fn in self.tr.built_functions.values()
                              for cpp, _, _ in fn.type_trait_bindings)
        if "Int" in self.lean_instance.values() or packet_integers:
            integer_ops = ("local instance cppTemplateDiv : Div Int := ⟨Int.tdiv⟩\n"
                           "local instance cppTemplateMod : Mod Int := ⟨Int.tmod⟩\n")
        numeric_traits = []
        signed_bits = {"char": 8, "signed char": 8, "short": 16, "short int": 16,
                       "int": 32, "std::int32_t": 32, "int32_t": 32,
                       "long": 64, "long int": 64, "long long": 64, "long long int": 64,
                       "ll": 64, "std::int64_t": 64, "int64_t": 64}
        for parameter in self.numeric_trait_parameters:
            cpp = self.instance[parameter]
            carrier = self.lean_instance[parameter]
            if cpp in signed_bits:
                value = f'Proofs.Cpp.intNumericTraits "{parameter}" {signed_bits[cpp]} true'
            elif cpp in SMALL_UNSIGNED_BINDINGS:
                value = f'Proofs.Cpp.intNumericTraits "{parameter}" {SMALL_UNSIGNED_BINDINGS[cpp]} false'
            elif carrier in ("UInt32", "UInt64"):
                value = f'Proofs.Cpp.u{32 if carrier == "UInt32" else 64}NumericTraits "{parameter}"'
            else:
                raise lt.Unsupported(f"numeric traits differential binding {cpp}")
            numeric_traits.append(f'local instance cppTraits_{parameter} : Proofs.Cpp.NumericTraits "{parameter}" {carrier} := {value}')
        constraints = set()
        type_traits = []
        for parameter in self.type_trait_parameters:
            signed, int128 = type_traits_binding(self.instance[parameter])
            carrier = self.lean_instance[parameter]
            type_traits.append(f'local instance cppTypeTraits_{parameter} : Proofs.Cpp.TypeTraits "{parameter}" {carrier} := '
                               f'⟨{str(signed).lower()}, {str(int128).lower()}⟩')
        requirements = [r for info in classes
                        for r in lt.class_requirements(lt.class_ty(info), self.tr.classes)]
        requirements += [r for info, sig in self.callables()
                         if sig.public and not (info is not None and sig.is_static)
                         for r in self.tr.built_functions[id(sig)].reqs.items]
        requirements += [r for kind, sig in self.tr.order if kind == "fn" and sig.initializes_globals
                         for r in self.tr.built_functions[id(sig)].reqs.items]
        for requirement in requirements:
            if requirement.startswith("Cpp.TemplateConstraint "):
                condition = requirement.removeprefix("Cpp.TemplateConstraint ")
                condition = re.sub(r'"[^"\\]*(?:\\.[^"\\]*)*"|\b[A-Za-z_][A-Za-z_0-9]*\b',
                                   lambda m: self.lean_instance.get(m[0], m[0]), condition)
                condition = condition.replace("Cpp.TypeTraits.", "Proofs.Cpp.TypeTraits.")
                constraints.add(condition)
        facts = [f"local instance cppConstraint_{i} : Proofs.Cpp.TemplateConstraint {c} := ⟨by decide⟩"
                 for i, c in enumerate(sorted(constraints))]
        remainder_bindings = []
        for parameter in self.mod_to_u32_parameters:
            if parameter not in self.instance:
                raise lt.Unsupported(f"missing integral remainder binding {parameter}")
            value = lt.mod_to_uint32_binding(self.instance[parameter], parameter).replace("Cpp.", "Proofs.Cpp.")
            remainder_bindings.append(f'local instance cppModToUInt32_{parameter} : '
                                      f'Proofs.Cpp.ModToUInt32 "{parameter}" {self.lean_instance[parameter]} := {value}')
        lines = [f"import {self.lean_module}", LEAN_PRELUDE, streams, integer_ops, *numeric_traits, *type_traits, *remainder_bindings, "open Proofs.Cpp.Gen", *facts, "",
                 "structure Objects where"]
        for info in classes:
            cty = self.lean_type_inst(lt.Ty("cls", info.name, tuple(lt.Ty("tparam", t) for t in info.tparams)))
            lines.append(f"  o_{info.name} : Array {cty} := #[]")
        if self.tr.globals:
            lines.append(f"  globalState : Option {self.tr.global_state_name} := none")
        if not classes:
            lines.append("  unused : Unit := ()")
        lines.append("")
        if self.tr.globals:
            # Class-only commands do not observe globals. Materialize their
            # model state when first used, retaining every previously created
            # object. Native C++ still performs its normal startup; separate
            # startup/global tests check the initialization itself.
            lines.append("def initializeObjects (objs : Objects) : IO Objects := do")
            lines.append("  match objs.globalState with")
            lines.append("  | some _ => pure objs")
            lines.append("  | none =>")
            lines.append(f"    match (cp.{self.tr.initializer_name} : Proofs.Cpp.M {self.tr.global_state_name}) 0 with")
            lines.append('    | none => throw (IO.userError "global initialization failed")')
            lines.append("    | some (state, _) => pure { objs with globalState := some state }")
            lines.append("")
        lines.append("partial def run (ts : List String) (objs : Objects) (out : Array String) : IO (Array String) := do")
        lines.append("  match ts with")
        lines.append("  | [] => pure out")
        for info in classes:
            for name, ty, _ in info.fields:
                if name in info.public_fields and self.field_is_observable(ty):
                    lines.append(f'  | "field" :: "{info.name}.{name}" :: ts => do')
                    lines.append('    let (k, ts) ← DiffTest.arg (α := Int) ts')
                    lines.append(f'    let value := objs.o_{info.name}[k.toNat]!.{lt.lean_name(name)}')
                    lines.append('    run ts objs (out.push ("ok" ++ DiffTest.Pr.pr value))')
        for info, sig in self.callables():
            if (sig.is_static and info is not None) or not sig.public:
                continue
            label = sig.lean_name.removeprefix("cp.")
            if info is None:
                head = f'  | "call" :: "{label}" :: ts => do'
            elif sig.is_ctor:
                head = f'  | "new" :: "{label}" :: ts => do'
            else:
                head = f'  | "do" :: "{label}" :: ts => do'
            lines.append(head)
            if sig.uses_globals:
                lines.append("    let objs ← initializeObjects objs")
            if info is not None and not sig.is_ctor:
                lines.append("    let (k, ts) ← DiffTest.arg (α := Int) ts")
                lines.append(f"    let obj := objs.o_{info.name}[k.toNat]!")
            names = []
            for i, (pname, pty, is_ref) in enumerate(sig.params):
                if pty.kind == "cls":
                    lines.append(f"    let (a{i}k, ts) ← DiffTest.arg (α := Int) ts")
                    lines.append(f"    let a{i} := objs.o_{pty.name}[a{i}k.toNat]!")
                else:
                    lines.append(f"    let (a{i}, ts) ← DiffTest.arg (α := {self.lean_type_inst(pty)}) ts")
                names.append(f"a{i}")
            pols = []
            for pol, methods in sig.policies.items():
                cls = self.policy_class[pol]
                fields = ", ".join(f"{lt.lean_name(m)} := cp.{cls}.{lt.lean_name(m)}" for m in methods)
                pols.append(f"{{ {fields} }}")
            value_names = list(dict.fromkeys([*(info.value_params if info else {}), *sig.value_params]))
            value_args = [f"({lt.lean_name(name)} := {self.lean_instance[name]})" for name in value_names]
            if sig.constraints:
                value_args += [f"({name} := {self.lean_instance[name]})"
                               for name in sig.tparams if name not in sig.value_params]
            call = " ".join([sig.lean_name] + value_args + pols + (["obj"] if info is not None and not sig.is_ctor else []) + names)
            if sig.uses_globals:
                call += " objs.globalState.get!"
            lines.append(f"    match ({call}).run 0 with")
            lines.append('    | none => run ts objs (out.push "fail")')
            lines.append("    | some (r, _) => do")
            if sig.is_ctor:
                value = "r.1" if sig.uses_globals else "r"
                state = ", globalState := some r.2" if sig.uses_globals else ""
                lines.append(f"      run ts {{ objs with o_{info.name} := objs.o_{info.name}.push {value}{state} }} (out.push \"new\")")
                continue
            outputs = sig.outputs()
            parts = []
            for j, o in enumerate(outputs):
                sel = "r" if len(outputs) == 1 else "r" + ".2" * j + (".1" if j < len(outputs) - 1 else "")
                if o == "self":
                    continue
                if o == "@globals":
                    continue
                if o == "ret" and sig.ret.kind == "cls":
                    parts.append('" obj"')
                    continue
                if o != "ret" and next(p[1] for p in sig.params if p[0] == o).kind == "cls":
                    parts.append('" objref"')
                    continue
                parts.append(f"DiffTest.Pr.pr {sel}")
            text = " ++ ".join(['"ok"'] + parts)
            objs = "objs"
            if sig.ret.kind == "cls" and outputs and outputs[0] == "ret":
                sel = "r" if len(outputs) == 1 else "r.1"
                lines.append(f"      let objs := {{ objs with o_{sig.ret.name} := objs.o_{sig.ret.name}.push {sel} }}")
            for i, (pname, pty, is_ref) in enumerate(sig.params):
                if is_ref and pty.kind == "cls":
                    j = outputs.index(pname)
                    sel = "r" if len(outputs) == 1 else "r" + ".2" * j + (".1" if j < len(outputs) - 1 else "")
                    lines.append(f"      let objs := {{ objs with o_{pty.name} := objs.o_{pty.name}.set! a{i}k.toNat {sel} }}")
            if "self" in outputs:
                j = outputs.index("self")
                sel = "r" if len(outputs) == 1 else "r" + ".2" * j + (".1" if j < len(outputs) - 1 else "")
                lines.append(f"      let objs := {{ objs with o_{info.name} := objs.o_{info.name}.set! k.toNat {sel} }}")
            if "@globals" in outputs:
                j = outputs.index("@globals")
                sel = "r" if len(outputs) == 1 else "r" + ".2" * j + (".1" if j < len(outputs) - 1 else "")
                lines.append(f"      let objs := {{ objs with globalState := some {sel} }}")
            lines.append(f"      run ts {objs} (out.push ({text}))")
        lines.append("  | t :: _ => throw (IO.userError s!\"unknown command {t}\")")
        lines.append("")
        lines.append("def main : IO Unit := do")
        lines.append("  let input ← (← IO.getStdin).readToEnd")
        lines.append("  let ts := (input.split (fun c => c.isWhitespace)).toList.map (·.toString) |>.filter (· ≠ \"\")")
        lines.append("  let out ← run ts {} #[]")
        lines.append("  for line in out do IO.println line")
        return "\n".join(lines) + "\n"


def run_diff(source: Path, instance: dict, lean_module: str, cases: str, timeout: float | None = None,
             deps=(), standard="c++17", calls=None):
    """Run both interpreters on `cases` (command text) and require identical output."""
    h = Harness(source, instance, lean_module, deps, standard, calls)
    lake = str(ROOT / ".tools/elan/bin/lake")
    env = os.environ.copy()
    env["ELAN_HOME"] = str(ROOT / ".tools/elan")
    env.pop("LEAN_PATH", None)
    with tempfile.TemporaryDirectory(prefix="diff-") as directory:
        scratch = Path(directory)
        cpp = ROOT / "tests/diff" / f".driver-{os.getpid()}-{source.stem}.cpp"
        cpp.parent.mkdir(parents=True, exist_ok=True)
        try:
            cpp.write_text(h.cpp_driver())
            binary = scratch / "driver"
            subprocess.run(["g++", f"-std={standard}", "-O1", "-fsanitize=address,undefined", "-fno-omit-frame-pointer",
                            str(cpp), "-o", str(binary)], check=True, timeout=timeout)
        finally:
            cpp.unlink(missing_ok=True)
        expected = subprocess.run([str(binary)], input=cases, capture_output=True, text=True, check=True,
                                  timeout=timeout, env={**env, "UBSAN_OPTIONS": "halt_on_error=1",
                                                        "ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1"}).stdout
        lean_file = scratch / "Driver.lean"
        lean_file.write_text(h.lean_driver())
        actual = subprocess.run([lake, "env", "lean", "--run", str(lean_file)], input=cases, capture_output=True,
                                text=True, cwd=ROOT, env=env, timeout=timeout)
        if actual.returncode != 0:
            raise RuntimeError(f"Lean interpreter failed: {(actual.stdout + actual.stderr)[-2000:]}")
        if actual.stdout != expected:
            exp, act = expected.splitlines(), actual.stdout.splitlines()
            for i, (a, b) in enumerate(zip(exp, act)):
                if a != b:
                    raise RuntimeError(f"translation differs from C++ at output line {i + 1}: C++ {a!r}, Lean {b!r}")
            raise RuntimeError(f"translation differs from C++: {len(exp)} C++ lines, {len(act)} Lean lines")
        return len(expected.splitlines())


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("source")
    parser.add_argument("--instance", action="append", default=[], help="T=long long")
    parser.add_argument("--module", required=True)
    parser.add_argument("--emit", choices=("cpp", "lean"))
    parser.add_argument("--cases")
    parser.add_argument("--standard", choices=("c++17", "c++20"), default="c++17")
    args = parser.parse_args()
    inst = dict(item.split("=", 1) for item in args.instance)
    h = Harness(Path(args.source), inst, args.module, standard=args.standard)
    if args.emit == "cpp":
        print(h.cpp_driver())
    elif args.emit == "lean":
        print(h.lean_driver())
    else:
        n = run_diff(Path(args.source), inst, args.module, Path(args.cases).read_text(), standard=args.standard)
        print(f"{n} outputs agree")
