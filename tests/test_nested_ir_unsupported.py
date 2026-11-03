"""未対応の形を拒否すること（tests/test_nested_ir.py の 1 テスト）。

1 つのテストが 5 分の制限を超えないように、同じテストを別々の検査に分け、結果を別々にキャッシュする。
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_nested_ir
from offline import disable_network

if __name__ == '__main__':
    disable_network()
    unittest.main(module=test_nested_ir, argv=['test', 'NestedIrTests.test_unsupported_shapes_fail_closed'])
