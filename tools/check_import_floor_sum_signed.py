"""Compare the preserved signed implementation with independent 128-bit sums."""

from check_import_element_count import run_cpp_test
from check_public import check_compiler
from offline import disable_network


def main():
    disable_network()
    check_compiler()
    run_cpp_test("tests/imports/floor_sum_signed.cpp",
                 "original signed floor_sum direct sums and boundary conversions")


if __name__ == "__main__":
    main()
