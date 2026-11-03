"""Reproduce the original C++17 error and test the retained repair candidate."""
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
        result = subprocess.run(["g++", *FLAGS, "-I", str(ROOT), "-I",
            str(ROOT / "experiments/library/cpp"), "-fsyntax-only", str(source)],
            cwd=ROOT, capture_output=True, text=True)
        if result.returncode == 0 or "bit_width" not in result.stderr or "not declared" not in result.stderr:
            raise RuntimeError("original doubling C++17 incompatibility was not reproduced")
    print("original doubling C++17 bit_width incompatibility reproduced", flush=True)
    run_cpp_test("tests/imports/doubling.cpp", "doubling C++17 repair and bit width")


if __name__ == "__main__":
    main()
