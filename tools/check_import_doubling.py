"""Check the original doubling header and the public implementation under C++23."""
import subprocess
import tempfile
from pathlib import Path

from check_import_element_count import ROOT, run_cpp_test
from check_public import FLAGS, check_compiler
from offline import disable_network


def main():
    disable_network()
    check_compiler()
    with tempfile.TemporaryDirectory(prefix="doubling-original-") as directory:
        source = Path(directory) / "original.cpp"
        source.write_text('#include "experiments/library/cpp/array/doubling.hpp"\n')
        subprocess.run(["g++", *FLAGS, "-I", str(ROOT), "-I",
            str(ROOT / "experiments/library/cpp"), "-fsyntax-only", str(source)],
            cwd=ROOT, check=True)
    print("original doubling compiles under C++23", flush=True)
    run_cpp_test("tests/imports/doubling.cpp", "doubling and bit width")


if __name__ == "__main__":
    main()
