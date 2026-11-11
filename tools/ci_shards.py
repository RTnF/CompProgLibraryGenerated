"""Split the public checks into CI shards of similar measured duration.

The plan depends only on the task labels and the committed weights (`tools/ci_weights.json`), so every shard of a CI
run computes the same partition and the shards together run each task exactly once. Weights are seconds measured in
CI; `update` refreshes them from downloaded job logs (lines `check passed after <s>s: <label>`). A label without a
measurement uses the default of its longest matching prefix in `default_seconds` (key "" is the fallback).

Long test files listed under `split_methods` run one unittest method per task, so no single task bounds the CI wall
clock. Their methods are read from the source (classes that derive directly from `unittest.TestCase`); a file with
any other test-class layout is rejected rather than partially covered.
"""

import argparse
import ast
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
WEIGHTS = ROOT / "tools/ci_weights.json"
PASSED = re.compile(r"check passed after ([0-9.]+)s: (\S+)")


def load_weights(path=WEIGHTS):
    data = json.loads(path.read_text())
    if set(data) != {"default_seconds", "split_methods", "seconds"} or "" not in data["default_seconds"]:
        raise ValueError("invalid CI weights fields")
    return data


def test_methods(path):
    """`Class.method` ids of the unittest methods defined in `path`."""
    tree = ast.parse(Path(path).read_text(), str(path))
    ids = []
    for node in tree.body:
        if not isinstance(node, ast.ClassDef):
            continue
        bases = [ast.unparse(base) for base in node.bases]
        methods = [item.name for item in node.body
                   if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)) and item.name.startswith("test")]
        if bases != ["unittest.TestCase"]:
            if methods:
                raise ValueError(f"{path}: test class {node.name} must derive directly from unittest.TestCase")
            continue
        ids += [f"{node.name}.{method}" for method in methods]
    if not ids:
        raise ValueError(f"{path}: no unittest methods to split")
    return ids


def check_tasks(checks, weights):
    """(label, arguments) of each check; split files yield one entry per test method."""
    split = set(weights["split_methods"])
    tasks = []
    for check in checks:
        if check in split:
            tasks += [(f"check:{check}::{method}", [method]) for method in test_methods(ROOT / check)]
        else:
            tasks.append((f"check:{check}", []))
    return tasks


def check_split_registered(checks, weights):
    unknown = set(weights["split_methods"]) - set(checks)
    if unknown:
        raise ValueError(f"split_methods names unregistered checks: {sorted(unknown)}")


def weight(label, weights, siblings):
    seconds = weights["seconds"]
    if label in seconds:
        return float(seconds[label])
    file_label = label.partition("::")[0]
    if file_label != label and file_label in seconds:
        return float(seconds[file_label]) / siblings[file_label]
    defaults = weights["default_seconds"]
    prefix = max((key for key in defaults if label.startswith(key)), key=len, default="")
    return float(defaults[prefix])


def assign(labels, count, weights):
    """Longest-processing-time-first assignment of labels to `count` shards (deterministic)."""
    if count < 1:
        raise ValueError("shard count must be positive")
    siblings = {}
    for label in labels:
        file_label = label.partition("::")[0]
        siblings[file_label] = siblings.get(file_label, 0) + 1
    loads = [0.0] * count
    shards = {}
    for label in sorted(labels, key=lambda item: (-weight(item, weights, siblings), item)):
        index = min(range(count), key=lambda i: (loads[i], i))
        shards[label] = index
        loads[index] += weight(label, weights, siblings)
    return shards, loads


def parse_shard(text):
    match = re.fullmatch(r"([0-9]+)/([0-9]+)", text)
    if not match or not int(match[1]) < int(match[2]):
        raise ValueError(f"--shard must be INDEX/COUNT with 0 <= INDEX < COUNT: {text}")
    return int(match[1]), int(match[2])


def update(logs, path=WEIGHTS):
    data = load_weights(path)
    measured = {}
    for log in logs:
        for match in PASSED.finditer(Path(log).read_text(errors="replace")):
            seconds, label = float(match[1]), match[2]
            # A cached check reports a near-zero time; keep the last real measurement.
            if seconds >= 1.0:
                measured[label] = round(seconds, 1)
    data["seconds"].update(measured)
    path.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    print(f"updated {len(measured)} weight(s) in {path.relative_to(ROOT)}")


def workflow_shards(text):
    """The shard count of the CI workflow, after checking that its matrix lists exactly 0..count-1."""
    matrices = re.findall(r"^\s*shard:\s*\[([0-9,\s]*)\]\s*$", text, re.M)
    counts = re.findall(r"^\s*SHARDS:\s*'([0-9]+)'\s*$", text, re.M)
    if len(matrices) != 1 or len(counts) != 1:
        raise ValueError("the workflow must define one shard matrix and one SHARDS count")
    listed = [int(item) for item in matrices[0].replace(",", " ").split()]
    count = int(counts[0])
    if listed != list(range(count)):
        raise ValueError(f"shard matrix {listed} does not list 0..{count - 1}")
    return count


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    refresh = commands.add_parser("update", help="refresh weights from CI job logs")
    refresh.add_argument("logs", nargs="+")
    plan = commands.add_parser("plan", help="print the estimated load of each shard")
    plan.add_argument("count", type=int)
    workflow = commands.add_parser("check-workflow", help="check the CI shard matrix against SHARDS")
    workflow.add_argument("path")
    args = parser.parse_args()
    if args.command == "update":
        update(args.logs)
        return
    if args.command == "check-workflow":
        print(f"{workflow_shards(Path(args.path).read_text())} CI shards")
        return
    sys.path.insert(0, str(ROOT / "tools"))
    import check_public
    labels = [label for label, _ in check_public.all_tasks(check_public.registry())]
    _, loads = assign(labels, args.count, load_weights())
    for index, load in enumerate(loads):
        print(f"shard {index}: {load:8.1f}s")
    print(f"tasks {len(labels)}, max {max(loads):.1f}s, total {sum(loads):.1f}s")


if __name__ == "__main__":
    main()
