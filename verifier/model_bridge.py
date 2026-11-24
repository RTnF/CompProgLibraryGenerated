"""Public registration gate for components translated by verifier/lean_translate.py (docs/translation.md).

1. The header and its public declarations are the registered ones (`source_sha256`, `public_declarations`).
2. Translating the header again gives exactly the registered Lean model (`model`).
3. The model imports only the prelude and the models of the registered dependencies, and the proof imports
   the model.
4. The differential test: the translated functions and the C++ code give the same outputs on the commands
   of the component's generator (`diff.cases`), for each registered instance of the template parameters.
"""

import argparse
import subprocess
import sys
from pathlib import Path

from clang_ast import ROOT, check_source_contract
import diff_harness
import lean_translate

sys.path.insert(0, str(ROOT / "tools"))
from offline import disable_network  # noqa: E402


def model_module(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def check_component(name, timeout=None):
    from public import component, repo_file
    metadata = component(name)
    if metadata.get("translation") != "lean_model":
        raise ValueError("component is not registered for the Lean model translation")
    source = repo_file(f"library/{metadata['source']}")
    check_source_contract(source, metadata)
    imports = [model_module(component(dep)["model"]) for dep in metadata["dependencies"]]
    deps = [repo_file(f"library/{component(dep)['source']}") for dep in metadata["dependencies"]]
    standard = metadata["standard"]
    expected = lean_translate.translate_file(source, imports, deps, standard, metadata.get("unverified_functions", []))
    if repo_file(metadata["model"]).read_text() != expected:
        raise ValueError(f"C++/translated Lean model mismatch for {name}; regenerate with verifier/lean_translate.py")
    proof = repo_file(metadata["proof"]).read_text()
    if f"import {model_module(metadata['model'])}" not in proof.splitlines():
        raise ValueError(f"the proof of {name} does not import its model")
    generated = {}

    def commands(args):
        # The generator may take arguments per instance (`case_args`, e.g. the field layout of a bound class).
        if args not in generated:
            generated[args] = subprocess.run([sys.executable, "-I", str(repo_file(metadata["diff"]["cases"])), *args],
                                             capture_output=True, text=True, check=True, cwd=ROOT,
                                             timeout=timeout).stdout
            if not generated[args].strip():
                raise ValueError(f"no differential test commands for {name}")
        return generated[args]

    commands(())
    for raw in metadata["diff"]["instances"]:
        instance = {k: v for k, v in raw.items() if k != "case_args"}
        cases = commands(tuple(raw.get("case_args", "").split()))
        bindings = [(repo_file(f"library/{component(b)['source']}"), model_module(component(b)["model"]))
                    for b in metadata["diff"].get("bindings", [])]
        count = diff_harness.run_diff(source, instance, model_module(metadata["model"]), cases, timeout, deps, standard,
                                      metadata["diff"].get("calls"), bindings, metadata.get("unverified_functions", []))
        print(f"differential test of {name} with {instance}: {count} outputs agree")
    print(f"C++ header, translated Lean model and differential test match: {name}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--component", required=True)
    args = parser.parse_args()
    disable_network()
    check_component(args.component)


if __name__ == "__main__":
    main()
