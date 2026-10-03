"""Check header-only archive contents and compile using only its headers."""

from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

from check_public import FLAGS, check_compiler
from offline import disable_network
from public import PUBLIC


def check(archive_path):
    disable_network()
    check_compiler()
    expected = {"library/" + path.relative_to(PUBLIC).as_posix(): path.read_bytes()
                for path in PUBLIC.rglob("*.hpp")}
    with tempfile.TemporaryDirectory(prefix="headers-only-") as directory:
        scratch = Path(directory)
        with zipfile.ZipFile(archive_path) as archive:
            if sorted(archive.namelist()) != sorted(expected):
                raise RuntimeError("archive must contain exactly the public .hpp files")
            for name, contents in expected.items():
                if archive.read(name) != contents:
                    raise RuntimeError(f"archive differs from source: {name}")
            archive.extractall(scratch)
        for names in [[name] for name in sorted(expected)] + [sorted(expected)]:
            source = scratch / "check.cpp"
            source.write_text("\n".join(f'#include "{name}"' for name in names)
                              + "\nint main() {}\n")
            binary = scratch / "check"
            subprocess.run(["g++", *FLAGS, "-I", str(scratch), "-I", str(scratch / "library"),
                            str(source), "-o", str(binary)], cwd=scratch, check=True)
            subprocess.run([str(binary)], cwd=scratch, check=True)
    print("header-only archive contents and compilation passed")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: python3 tools/check_header_package.py ARCHIVE")
    try:
        check(sys.argv[1])
    except (OSError, RuntimeError, subprocess.CalledProcessError, zipfile.BadZipFile) as error:
        raise SystemExit(str(error)) from error
