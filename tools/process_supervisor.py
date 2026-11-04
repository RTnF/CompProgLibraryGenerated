"""Bound a verification command and reap descendants across sessions."""
import argparse
import ctypes
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

PR_SET_PDEATHSIG = 1
PR_SET_CHILD_SUBREAPER = 36


class SupervisorInterrupted(BaseException):
    # Audit hooks may swallow ordinary Exceptions; a stop must reach cleanup.
    pass


def capture(command, *, cwd=None, env=None, timeout=None, input=None, **kwargs):
    if input is not None:
        if kwargs.get('stdin') is not None:
            raise ValueError('stdin and input arguments may not both be used')
        kwargs['stdin'] = subprocess.PIPE
    deadline = 'none' if timeout is None else repr(time.monotonic() + timeout)
    with tempfile.TemporaryDirectory(prefix='supervisor-receipt-') as directory:
        receipt = Path(directory)/'result.json'
        wrapped = [sys.executable, str(Path(__file__).resolve()), '--receipt', str(receipt),
                   '--deadline', deadline, '--parent', str(os.getpid()), '--', *command]
        with subprocess.Popen(wrapped, cwd=cwd, env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, start_new_session=True, **kwargs) as worker:
            try:
                output, errors = worker.communicate(input=input)
            except BaseException:
                worker.terminate()
                worker.communicate()
                raise
        if worker.returncode or not receipt.is_file():
            raise RuntimeError('command supervisor did not complete cleanup')
        result = json.loads(receipt.read_text())
        if result['reason'] == 'timeout':
            raise subprocess.TimeoutExpired(command, timeout, output=output, stderr=errors)
        if result['reason'] is not None or not result['cleaned']:
            raise RuntimeError('command supervisor failed: '+str(result.get('error', result['reason'])))
        completed = subprocess.CompletedProcess(command, result['returncode'], output, errors)
        completed.check_returncode()
        return completed


def reap_adopted_children():
    """Only this single-threaded worker's children can appear in this list."""
    children = Path('/proc/self/task')/str(os.getpid())/'children'
    while True:
        try:
            pid, _ = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return
        if pid:
            continue
        # These are unreaped children; their PIDs cannot be reused until waitpid.
        for child in children.read_text().split():
            try:
                os.kill(int(child), signal.SIGKILL)
            except ProcessLookupError:
                pass
        try:
            os.waitpid(-1, 0)
        except ChildProcessError:
            return


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--deadline', required=True)
    parser.add_argument('--parent', type=int, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    root = None
    result = {'reason': 'error', 'returncode': None, 'cleaned': False}

    def interrupted(number, frame):
        raise SupervisorInterrupted('supervisor interrupted')

    try:
        signal.signal(signal.SIGTERM, interrupted)
        signal.signal(signal.SIGINT, interrupted)
        signal.signal(signal.SIGHUP, interrupted)
        signal.signal(signal.SIGCHLD, signal.SIG_DFL)
        libc = ctypes.CDLL(None, use_errno=True)
        libc.prctl.argtypes = [ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong,
                               ctypes.c_ulong, ctypes.c_ulong]
        libc.prctl.restype = ctypes.c_int
        for option, value in [(PR_SET_CHILD_SUBREAPER, 1), (PR_SET_PDEATHSIG, signal.SIGTERM)]:
            if libc.prctl(option, value, 0, 0, 0) != 0:
                raise OSError(ctypes.get_errno(), 'cannot configure command supervisor')
        if os.getppid() != args.parent:
            raise SupervisorInterrupted('parent exited before supervisor setup')
        (Path('/proc/self/task')/str(os.getpid())/'children').read_text()
        remaining = None if args.deadline == 'none' else float(args.deadline)-time.monotonic()
        if remaining is not None and remaining <= 0:
            raise subprocess.TimeoutExpired(command, 0)
        root = subprocess.Popen(command, start_new_session=True)
        remaining = None if args.deadline == 'none' else float(args.deadline)-time.monotonic()
        result['returncode'] = root.wait(timeout=remaining)
        result['reason'] = None
    except subprocess.TimeoutExpired:
        result['reason'] = 'timeout'
    except SupervisorInterrupted:
        result['reason'] = 'interrupted'
    except BaseException as error:
        result['reason'] = 'error'
        result['error'] = type(error).__name__+': '+str(error)
    finally:
        for number in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            signal.signal(number, signal.SIG_IGN)
        if root is not None:
            if root.poll() is None:
                try:
                    os.killpg(root.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            root.wait()
        reap_adopted_children()
        result['cleaned'] = True
        args.receipt.write_text(json.dumps(result)+'\n')


if __name__ == '__main__':
    main()
