"""Transfer successful component checks without caching the final proof audit."""

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / '.cache/check-results.json'
SNAPSHOT = ROOT / '.cache/ci-check-results.json'


def transfer(source, destination):
    rows = json.loads(source.read_text()) if source.is_file() else {}
    if not isinstance(rows, dict):
        raise ValueError('check cache must be an object')
    # check_cache validates each entry against the current inputs and tools
    # before reuse. Never transfer proof-security, including on restore.
    rows = {name: entry for name, entry in rows.items()
            if name.startswith(('cpp:', 'cpp-common [', 'bridge:', 'check:'))}
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_suffix('.tmp')
    temporary.write_text(json.dumps(rows, sort_keys=True) + '\n')
    temporary.replace(destination)
    return len(rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('operation', choices=('restore', 'snapshot'))
    args = parser.parse_args()
    source, destination = ((SNAPSHOT, RESULTS) if args.operation == 'restore'
                           else (RESULTS, SNAPSHOT))
    print(f'{args.operation}: {transfer(source, destination)} reusable checks; final audit excluded')


if __name__ == '__main__':
    main()
