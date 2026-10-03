"""Package only registered library headers, without repository dependencies."""

import argparse
import hashlib
from pathlib import Path
import re
import zipfile

from public import PUBLIC, registry, repo_file


def package(output: Path):
    entries = registry()
    headers = sorted(PUBLIC.rglob("*.hpp"))
    if not headers:
        raise ValueError("no public headers to distribute")
    for data in entries.values():
        source = repo_file(f"library/{data['source']}")
        if hashlib.sha256(source.read_bytes()).hexdigest() != data["source_sha256"]:
            raise ValueError(f"unverified source change: {source}")
    # A header-only download must not need experiments/, tests/ or repo tools.
    for source in headers:
        for include in re.findall(r'^\s*#\s*include\s*"([^"]+)"',
                                  source.read_text(), re.MULTILINE):
            candidates = [(source.parent / include).resolve(), (PUBLIC / include).resolve()]
            if not any(path in headers for path in candidates):
                raise ValueError(f"include outside the header distribution: {source}: {include}")
    output = output.resolve()
    if output.is_relative_to(PUBLIC):
        raise ValueError("write distribution archives outside library/")
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for source in headers:
            info = zipfile.ZipInfo("library/" + source.relative_to(PUBLIC).as_posix(),
                                   date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, source.read_bytes())
    print(f"packaged {len(headers)} header(s): {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    try:
        package(parser.parse_args().output)
    except ValueError as error:
        raise SystemExit(str(error)) from error
