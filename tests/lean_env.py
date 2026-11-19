"""The pinned `lake` and its environment for tests that run Lean."""
import os
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
# The tests import the shared tools (offline, check_public) through this module.
if str(ROOT / "tools") not in sys.path:
    sys.path.insert(0, str(ROOT / "tools"))


def lean_environment():
    environment = os.environ.copy()
    local = ROOT / ".tools/elan/bin/lake"
    if local.is_file():
        environment["ELAN_HOME"] = str(ROOT / ".tools/elan")
        return str(local), environment
    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("lake is required for Lean tests")
    return lake, environment
