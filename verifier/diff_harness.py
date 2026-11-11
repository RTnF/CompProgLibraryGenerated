"""Differential tests of the C++ -> Lean translation (docs/translation.md).

From the translated signatures this module generates two interpreters of one command language, one in C++
(calling the public header) and one in Lean (running the translated functions), runs both on the same
generated commands and requires identical output. The translator itself is not proved; this test is the
check that its output behaves like the C++ code (docs/trust_policy.md).

Command language (whitespace separated tokens, one command per line):
  call <function> <args...>          a free function; prints its outputs
  new <constructor> <args...>        constructs object number k (0, 1, ... in order of creation)
  do <k> <method> <args...>          calls a member function of object k; prints its outputs
Values: an integer; a bool as 0/1; a vector as its length and its elements; a pair as its two values.
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


def lean_instance_type(cpp: str) -> str:
    ty = lt.parse_type(cpp, set(), set())
    return lt.lean_type(ty)


CPP_PRELUDE = r"""
#include <iostream>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace difftest {
template <class X> void rd(std::vector<X> &v);
template <class A, class B> void rd(std::pair<A, B> &p);
template <class X> void pr(const std::vector<X> &v);
template <class A, class B> void pr(const std::pair<A, B> &p);
template <class X> void rd(X &x) {
  if constexpr (std::is_unsigned_v<X>) { unsigned long long v; std::cin >> v; x = (X)v; }
  else { long long v; std::cin >> v; x = (X)v; }
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


class Harness:
    def __init__(self, source: Path, instance: dict, lean_module: str):
        self.source = source
        self.instance = instance             # template parameter -> C++ type
        self.lean_module = lean_module
        tr = lt.Translator(lt.source_decls(source), source.read_bytes())
        tr.translate()
        self.tr = tr
        self.lean_instance = {k: lean_instance_type(v) for k, v in instance.items()}
        for k, v in instance.items():
            ty = lt.parse_type(v, set(), set())
            if ty.kind == "vec":   # a container parameter T: its element type is T_value_type
                self.lean_instance[f"{k}_value_type"] = lt.lean_type(ty.args[0])

    def callables(self):
        out = []
        for kind, item in self.tr.order:
            if kind == "fn":
                out.append((None, item))
            else:
                for sig in item.methods:
                    out.append((item, sig))
        return out

    def param_quals(self, sig):
        return [p.get("type", {}).get("qualType", "") for p in lt.inner(sig.node) if p.get("kind") == "ParmVarDecl"]

    # ------------------------------------------------------------------ C++
    def cpp_class(self, info):
        args = [self.instance[t] for t in info.tparams]
        return f"cp::{info.name}" + (f"<{', '.join(args)}>" if args else "")

    def cpp_driver(self) -> str:
        include = os.path.relpath(self.source.resolve(), (ROOT / "tests/diff").resolve())
        lines = [f'#include "../../experiments/library/cpp/template/small_template.hpp"',
                 f'#include "{include}"', CPP_PRELUDE, "int main() {", "  std::string cmd, name;"]
        classes = [item for kind, item in self.tr.order if kind == "class"]
        for info in classes:
            lines.append(f"  std::vector<{self.cpp_class(info)}> objects_{info.name};")
        lines.append("  while (std::cin >> cmd >> name) {")
        for info, sig in self.callables():
            if (sig.is_static and info is not None) or not sig.public:
                continue
            quals = self.param_quals(sig)
            decls, names = [], []
            for i, q in enumerate(quals):
                t = cpp_value_type(q, self.instance)
                decls.append(f"{t} a{i}; difftest::rd(a{i});")
                names.append(f"a{i}")
            if info is None:
                targs = [self.instance[t.removesuffix("_value_type")] if t.removesuffix("_value_type") in sig.containers
                         else self.instance[t] for t in sig.tparams]
                callee = f"cp::{sig.cpp_name}" + (f"<{', '.join(targs)}>" if targs else "")
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
                if sig.ret.kind != "void":
                    lines.append(f"        auto r = {call};")
                    lines.append("        std::cout << \"ok\"; difftest::pr(r);")
                else:
                    lines.append(f"        {call};")
                    lines.append("        std::cout << \"ok\";")
                for i, (pname, pty, is_ref) in enumerate(sig.params):
                    if is_ref:
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
    def lean_type_inst(self, ty):
        return lt.lean_type(lt.subst(ty, list(self.lean_instance), [lt.Ty("tparam", v) for v in self.lean_instance.values()]))

    def lean_driver(self) -> str:
        classes = [item for kind, item in self.tr.order if kind == "class"]
        lines = [f"import {self.lean_module}", LEAN_PRELUDE, "open Proofs.Cpp.Gen", "",
                 "structure Objects where"]
        for info in classes:
            cty = self.lean_type_inst(lt.Ty("cls", info.name, tuple(lt.Ty("tparam", t) for t in info.tparams)))
            lines.append(f"  o_{info.name} : Array {cty} := #[]")
        if not classes:
            lines.append("  unused : Unit := ()")
        lines.append("")
        lines.append("partial def run (ts : List String) (objs : Objects) (out : Array String) : IO (Array String) := do")
        lines.append("  match ts with")
        lines.append("  | [] => pure out")
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
            if info is not None and not sig.is_ctor:
                lines.append("    let (k, ts) ← DiffTest.arg (α := Int) ts")
                lines.append(f"    let obj := objs.o_{info.name}[k.toNat]!")
            names = []
            for i, (pname, pty, is_ref) in enumerate(sig.params):
                lines.append(f"    let (a{i}, ts) ← DiffTest.arg (α := {self.lean_type_inst(pty)}) ts")
                names.append(f"a{i}")
            call = " ".join([sig.lean_name] + (["obj"] if info is not None and not sig.is_ctor else []) + names)
            lines.append(f"    match ({call}).run 0 with")
            lines.append('    | none => run ts objs (out.push "fail")')
            lines.append("    | some (r, _) =>")
            if sig.is_ctor:
                lines.append(f"      run ts {{ objs with o_{info.name} := objs.o_{info.name}.push r }} (out.push \"new\")")
                continue
            outputs = sig.outputs()
            parts = []
            for j, o in enumerate(outputs):
                sel = "r" if len(outputs) == 1 else "r" + ".2" * j + (".1" if j < len(outputs) - 1 else "")
                if o == "self":
                    continue
                parts.append(f"DiffTest.Pr.pr {sel}")
            text = " ++ ".join(['"ok"'] + parts)
            objs = "objs"
            if "self" in outputs:
                j = outputs.index("self")
                sel = "r" if len(outputs) == 1 else "r" + ".2" * j + (".1" if j < len(outputs) - 1 else "")
                objs = f"{{ objs with o_{info.name} := objs.o_{info.name}.set! k.toNat {sel} }}"
            lines.append(f"      run ts {objs} (out.push ({text}))")
        lines.append("  | t :: _ => throw (IO.userError s!\"unknown command {t}\")")
        lines.append("")
        lines.append("def main : IO Unit := do")
        lines.append("  let input ← (← IO.getStdin).readToEnd")
        lines.append("  let ts := (input.split (fun c => c.isWhitespace)).toList.map (·.toString) |>.filter (· ≠ \"\")")
        lines.append("  let out ← run ts {} #[]")
        lines.append("  for line in out do IO.println line")
        return "\n".join(lines) + "\n"


def run_diff(source: Path, instance: dict, lean_module: str, cases: str, timeout: float | None = None):
    """Run both interpreters on `cases` (command text) and require identical output."""
    h = Harness(source, instance, lean_module)
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
            subprocess.run(["g++", "-std=c++17", "-O1", "-fsanitize=address,undefined", "-fno-omit-frame-pointer",
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
    args = parser.parse_args()
    inst = dict(item.split("=", 1) for item in args.instance)
    h = Harness(Path(args.source), inst, args.module)
    if args.emit == "cpp":
        print(h.cpp_driver())
    elif args.emit == "lean":
        print(h.lean_driver())
    else:
        n = run_diff(Path(args.source), inst, args.module, Path(args.cases).read_text())
        print(f"{n} outputs agree")
