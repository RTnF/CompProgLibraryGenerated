"""`tests/test_generic_template_family.py` の `test_original_scalar_record_constructors_and_id_equal_the_ty_family` を単独の検査として、2 組目の型（unsigned int, long long）で実行する。

全体は 5 分の制限を超えるため、検査ごとに別のスクリプトに分けて、結果を別々にキャッシュする。
"""
import os
import sys
import unittest
from pathlib import Path

os.environ['GENERIC_FAMILY_ALT'] = '1'
sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_generic_template_family

if __name__ == '__main__':
    unittest.main(module=test_generic_template_family,
                  argv=['test', 'GenericTemplateFamilyTests.test_original_scalar_record_constructors_and_id_equal_the_ty_family'])
