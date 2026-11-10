"""`tests/test_generic_template_family.py` の `test_original_friend_op_returns_complete_sum_objects_for_every_ty` を単独の検査として実行する。

全体は 5 分の制限を超えるため、検査ごとに別のスクリプトに分けて、結果を別々にキャッシュする。
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_generic_template_family

if __name__ == '__main__':
    unittest.main(module=test_generic_template_family,
                  argv=['test', 'GenericTemplateFamilyTests.test_original_friend_op_returns_complete_sum_objects_for_every_ty'])
