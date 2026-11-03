"""Lean の独立オラクルとの照合の第 3/3 部（tests/test_nested_ir.py の test_regeneration_and_independent_oracle）。

全体は 5 分の制限を超えるため、事例を 3 つに分けて別々の検査にし、結果を別々にキャッシュする。3 つで全事例になる。
"""
import os
import sys
import unittest
from pathlib import Path

os.environ['NESTED_IR_PARTS'] = '3'
os.environ['NESTED_IR_PART'] = '2'
sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_nested_ir
from offline import disable_network

if __name__ == '__main__':
    disable_network()
    unittest.main(module=test_nested_ir, argv=['test', 'NestedIrTests.test_regeneration_and_independent_oracle'])
