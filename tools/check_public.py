"""Run every registered public component's checks, locally and in CI."""

import argparse
import os
import signal
from pathlib import Path
import shutil
import subprocess
import sys
import concurrent.futures
import tempfile
import time

import check_cache
from public import ROOT, TEMPLATE, include_check, registry, repo_file, support_registry
from offline import disable_network


FLAGS = ["-std=c++17", "-O2", "-Wall", "-Wextra", "-pedantic"]


# Whole-run wall-clock limit: 80% of the default 5-minute prompt-cache lifetime.
# A full run takes far longer, so pass a larger --timeout-seconds for mode=all.
DEFAULT_TIMEOUT_SECONDS = 240
deadline = None


def remaining_seconds():
    remaining = None if deadline is None else deadline - time.monotonic()
    if remaining is not None and remaining <= 0:
        raise RuntimeError("check_public.py exceeded its time limit")
    return remaining


def run(command, **kwargs):
    """Bound a command and its compiler/exporter/kernel process group."""
    remaining = remaining_seconds()
    with subprocess.Popen(command, cwd=ROOT, start_new_session=True, **kwargs) as child:
        try:
            code = child.wait(timeout=remaining)
        except BaseException as error:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
            if isinstance(error, subprocess.TimeoutExpired):
                raise RuntimeError(f"check_public.py exceeded its time limit while running: {command[:3]}") from error
            raise
        if code:
            raise subprocess.CalledProcessError(code, command)


def check_compiler():
    version = subprocess.check_output(["g++", "-dumpfullversion"], text=True).strip()
    if version != "13.3.0":
        raise RuntimeError(f"expected GCC 13.3.0, found {version}")


def check_local_results_untracked():
    tracked = subprocess.check_output(
        ["git", "ls-files", "--", "benchmarks/local/"], cwd=ROOT, text=True,
    ).strip()
    if tracked:
        raise RuntimeError(f"local benchmark results are tracked by Git: {tracked}")


def flags_tag():
    return " ".join(FLAGS)


def cpp_tasks(entries):
    script = [Path(__file__), ROOT / "tools/public.py", ROOT / "tools/check_cache.py"]
    template = repo_file(TEMPLATE)
    sources = [repo_file(f"library/{data['source']}") for data in entries.values()]

    def common():
        with tempfile.TemporaryDirectory(prefix="public-check-") as directory:
            scratch = Path(directory)
            for names, label in [([], "template"), (list(entries), "all-components")]:
                source = scratch / f"{label}.cpp"
                source.write_text(include_check(names, entries))
                binary = scratch / label
                run(["g++", *FLAGS, "-I", str(ROOT), str(source), "-o", str(binary)])
                run([str(binary)])

    tasks = [("cpp-common", lambda: check_cache.cached_call(
        f"cpp-common [{flags_tag()}]", [*script, template, *check_cache.cpp_closure(sources)], common))]
    for name, data in entries.items():
        tests = [repo_file(test) for test in data["tests"]]
        cases = [repo_file(case[field]) for case in data.get("io_cases", []) for field in ("source", "input", "expected")]
        library = [repo_file(f"library/{data['source']}")]

        def component(name=name, data=data):
            check_component_cpp(name, data, entries)

        tasks.append((f"cpp:{name}", lambda name=name, tests=tests, library=library, cases=cases, component=component:
                      check_cache.cached_call(f"cpp:{name} [{flags_tag()}]",
                                              [*script, template, *check_cache.cpp_closure([*tests, *library, *cases])],
                                              component)))
    return tasks


def check_component_cpp(name, data, entries):
    with tempfile.TemporaryDirectory(prefix="public-check-") as directory:
        scratch = Path(directory)
        for index, test in enumerate(data["tests"]):
            require_template_first(test)
            binary = scratch / f"{name}-test-{index}"
            run(["g++", *FLAGS, str(repo_file(test)), "-o", str(binary)])
            run([str(binary)])
            if data.get("sanitizers", False):
                run(["g++", "-std=c++17", "-O1", "-g", "-Wall", "-Wextra", "-pedantic",
                     "-fsanitize=address,undefined", "-fno-omit-frame-pointer",
                     str(repo_file(test)), "-o", str(binary)])
                environment = os.environ.copy()
                environment["ASAN_OPTIONS"] = "detect_leaks=0:halt_on_error=1"
                environment["UBSAN_OPTIONS"] = "halt_on_error=1:print_stacktrace=1"
                run([str(binary)], env=environment)
        for index, case in enumerate(data.get("io_cases", [])):
            require_template_first(case["source"])
            binary = scratch / f"{name}-io-{index}"
            run(["g++", *FLAGS, str(repo_file(case["source"])), "-o", str(binary)])
            result = subprocess.run(
                [str(binary)], cwd=ROOT,
                input=repo_file(case["input"]).read_bytes(),
                capture_output=True, check=True,
            )
            expected = repo_file(case["expected"]).read_bytes()
            if result.stdout != expected:
                raise RuntimeError(f"I/O case {index} failed for {name}: {result.stdout!r} != {expected!r}")
        included = scratch / f"{name}-included.cpp"
        included.write_text(include_check([name], entries))
        run(["g++", *FLAGS, "-I", str(ROOT), "-fsyntax-only", str(included)])
        print(f"C++ tests and template-first include check passed: {name}")


def require_template_first(test):
    includes = [line.strip() for line in repo_file(test).read_text().splitlines()
                if line.lstrip().startswith("#include")]
    expected = f'#include "../{TEMPLATE}"'
    if not includes or includes[0] != expected:
        raise RuntimeError(f"test must include the library template first: {test}")


def run_traced(name, command):
    remaining = remaining_seconds()
    try:
        check_cache.run_traced(name, command, timeout=remaining)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"check_public.py exceeded its time limit while running: {command[:3]}") from error


def bridge_tasks(entries):
    def check(name, data):
        run_traced(f"bridge:{name}", [sys.executable, str(repo_file(data["bridge"])), "--component", name])
        print(f"C++ AST and Lean model match: {name}")

    return [(f"bridge:{name}", lambda name=name, data=data: check(name, data)) for name, data in entries.items()]


def run_tasks(tasks, jobs):
    """Run independent checks in parallel; the first failure cancels the rest and is re-raised."""
    def timed(label, function):
        started = time.monotonic()
        print(f"check started: {label}", flush=True)
        try:
            result = function()
        except BaseException:
            print(f"check failed after {time.monotonic() - started:.3f}s: {label}", flush=True)
            raise
        print(f"check passed after {time.monotonic() - started:.3f}s: {label}", flush=True)
        return result

    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        futures = {pool.submit(timed, label, function): label for label, function in tasks}
        failure = None
        for future in concurrent.futures.as_completed(futures):
            if future.cancelled():
                continue
            error = future.exception()
            if error is not None and failure is None:
                failure = (futures[future], error)
                for other in futures:
                    other.cancel()
        if failure is not None:
            raise RuntimeError(f"check failed: {failure[0]}: {failure[1]}") from failure[1]


def build_lean():
    """Prepare test imports from the independently built, screened sources."""
    run([sys.executable, str(ROOT / "tools/check_proof_security.py"), "--prepare-test-imports"])


def check_lean():
    # The proof security check is a function of the proof sources, the reviewed contract and the checker tools.
    inputs = [ROOT / name for name in ("Proofs.lean", "Proofs", "verification", "lakefile.toml", "lake-manifest.json",
                                       "lean-toolchain", "verifier/support.toml", "tools/proof_security.py",
                                       "tools/check_proof_security.py", "tools/offline.py", "tools/public.py")]
    inputs += sorted((ROOT / "library").glob("*.toml"))
    inputs += [ROOT / ".tools/lean4export/.lake/build/bin/lean4export", ROOT / ".tools/nanoda_lib/target/release/nanoda_bin"]
    remaining_seconds()
    check_cache.cached_call("proof-security", inputs,
                            lambda: run([sys.executable, str(ROOT / "tools/check_proof_security.py")]))
    remaining_seconds()


def lower_priority():
    """Keep the checks (and their children) from competing with the rest of the machine for CPU and disk."""
    try:
        os.nice(19)
    except OSError:
        pass
    try:
        subprocess.run(["ionice", "-c3", "-p", str(os.getpid())], check=False,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except OSError:
        pass


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("all", "cpp", "bridge"), default="all")
    parser.add_argument("--jobs", type=int, default=1,
                        help="number of independent checks run in parallel (default: 1; the machine's disk is shared, "
                             "so more jobs raise the I/O load)")
    parser.add_argument("--component", action="append", default=[],
                        help="restrict the cpp and bridge checks to these components (repeatable). Meant for the "
                             "development loop together with --mode cpp/bridge; only a full --mode all run is a gate")
    parser.add_argument("--no-cache", action="store_true",
                        help="ignore the cache of earlier successful checks (.cache/check-results.json)")
    parser.add_argument("--timeout-seconds", type=float, default=DEFAULT_TIMEOUT_SECONDS,
                        help="wall-clock limit for the whole run (default: 240, 80%% of the 5-minute cache lifetime)")
    args = parser.parse_args()
    global deadline
    deadline = time.monotonic() + args.timeout_seconds
    check_cache.enabled = not args.no_cache
    disable_network()
    lower_priority()
    entries = registry()
    check_local_results_untracked()
    check_compiler()
    selected = entries
    if args.component:
        unknown = sorted(set(args.component) - set(entries))
        if unknown:
            raise RuntimeError(f"unknown component(s): {unknown}")
        if args.mode == "all":
            raise RuntimeError("--component needs --mode cpp or --mode bridge; the full gate always checks everything")
        selected = {name: data for name, data in entries.items() if name in args.component}
    tasks = []
    if args.mode in ("all", "cpp"):
        tasks += cpp_tasks(selected)
    if args.mode in ("all", "bridge"):
        tasks += bridge_tasks(selected)
    if args.mode == "all":
        tasks += [(f"check:{check}", lambda check=check: run_traced(f"check:{check}", [sys.executable, str(repo_file(check))]))
                  for check in support_registry()["checks"]]
    if args.mode == "all":
        build_lean()
    run_tasks(tasks, args.jobs)
    if args.mode == "all":
        check_lean()
    print(f"public checks passed for {len(selected)} component(s): {args.mode}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
