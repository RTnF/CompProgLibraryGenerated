"""Stop a runaway command before the machine runs out of memory.

The development machine is a WSL2 VM without swap; when a Lean proof or a compiler
exhausts memory the kernel OOM killer (or the whole VM) goes down.  This module
polls the free memory while a command runs in its own process group and, before
that point, terminates the group (SIGTERM, then SIGKILL) and reports the cause, so
the proof can be fixed instead of the machine being restarted.

Library use: ``wait(child, timeout)`` for a ``Popen`` started with
``start_new_session=True``.  Command line:

    python3 tools/memguard.py [--reserve-mb N] [--max-rss-mb M] -- command ...

Limits (MiB) also come from the environment: ``CP_MEM_RESERVE_MB`` is the free
memory to keep (default: the larger of 1536 and 12% of the total memory), and
``CP_MEM_MAX_RSS_MB`` bounds the resident size of one command's process group
(default: no bound beyond the reserve).
"""

import os
import signal
import subprocess
import sys
import time

POLL_SECONDS = 0.5
GRACE_SECONDS = 3.0


class MemoryGuardError(RuntimeError):
    """Raised after a command was stopped for using too much memory."""


def _meminfo():
    values = {}
    with open("/proc/meminfo") as f:
        for line in f:
            key, rest = line.split(":", 1)
            values[key] = int(rest.split()[0]) * 1024
    return values


def default_reserve_bytes():
    env = os.environ.get("CP_MEM_RESERVE_MB")
    if env:
        return int(env) << 20
    total = _meminfo().get("MemTotal", 0)
    return max(1536 << 20, total * 12 // 100)


def default_max_rss_bytes():
    env = os.environ.get("CP_MEM_MAX_RSS_MB")
    return int(env) << 20 if env else None


def available_bytes():
    return _meminfo().get("MemAvailable", 0)


def group_rss_bytes(pgid):
    """Resident size of all processes in the process group ``pgid``."""
    page = os.sysconf("SC_PAGE_SIZE")
    total = 0
    for name in os.listdir("/proc"):
        if not name.isdigit():
            continue
        try:
            with open(f"/proc/{name}/stat") as f:
                stat = f.read()
        except OSError:
            continue
        # Fields after the parenthesised command name; pgrp is field 5, rss field 24.
        fields = stat[stat.rfind(")") + 2:].split()
        if len(fields) > 21 and int(fields[2]) == pgid:
            total += int(fields[21]) * page
    return total


def _stop_group(child):
    for sig, pause in ((signal.SIGTERM, GRACE_SECONDS), (signal.SIGKILL, None)):
        try:
            os.killpg(child.pid, sig)
        except ProcessLookupError:
            break
        if pause is None:
            break
        try:
            child.wait(timeout=pause)
            break
        except subprocess.TimeoutExpired:
            continue
    child.wait()


def wait(child, timeout=None, reserve=None, max_rss=None, label=None):
    """Like ``child.wait(timeout)``, but stop the child's process group on memory pressure.

    Raises ``subprocess.TimeoutExpired`` on timeout (the group is left running, as
    ``Popen.wait`` does) and ``MemoryGuardError`` after stopping the group.
    """
    reserve = default_reserve_bytes() if reserve is None else reserve
    max_rss = default_max_rss_bytes() if max_rss is None else max_rss
    end = None if timeout is None else time.monotonic() + timeout
    while True:
        step = POLL_SECONDS if end is None else min(POLL_SECONDS, max(0.0, end - time.monotonic()))
        try:
            return child.wait(timeout=step)
        except subprocess.TimeoutExpired:
            pass
        if end is not None and time.monotonic() >= end:
            raise subprocess.TimeoutExpired(child.args, timeout)
        avail = available_bytes()
        rss = group_rss_bytes(child.pid) if max_rss is not None or avail < reserve else 0
        if avail < reserve or (max_rss is not None and rss > max_rss):
            _stop_group(child)
            what = label or (child.args[:3] if isinstance(child.args, list) else child.args)
            raise MemoryGuardError(
                f"memguard stopped {what}: group RSS {rss >> 20} MiB, available {avail >> 20} MiB "
                f"(reserve {reserve >> 20} MiB"
                + (f", max RSS {max_rss >> 20} MiB)" if max_rss is not None else ")")
                + "; reduce the memory use instead of raising the limit")


def main(argv):
    reserve = max_rss = None
    args = list(argv)
    while args and args[0] != "--":
        flag = args.pop(0)
        if flag == "--reserve-mb":
            reserve = int(args.pop(0)) << 20
        elif flag == "--max-rss-mb":
            max_rss = int(args.pop(0)) << 20
        else:
            print(f"memguard: unknown option {flag}", file=sys.stderr)
            return 2
    if not args or len(args) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    command = args[1:]
    child = subprocess.Popen(command, start_new_session=True)
    try:
        return wait(child, reserve=reserve, max_rss=max_rss, label=command[:3])
    except MemoryGuardError as error:
        print(error, file=sys.stderr)
        return 137
    except KeyboardInterrupt:
        _stop_group(child)
        return 130


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
