"""Unit tests for oracle.py. run_cpython_oracle.sh runs them before the suite."""
import unittest

import oracle


class RunFileTest(unittest.TestCase):

    def test_module_level_skip_skips_every_method(self):
        # test_bytes.py does this in a class body: on a build without _testcapi,
        # import_helper.import_module('_testcapi') raises SkipTest. Class A is
        # already built when T skips, and its method must be skipped too.
        source = (
            "import unittest\n"
            "class A(unittest.TestCase):\n"
            "    def test_a(self): pass\n"
            "class T(unittest.TestCase):\n"
            "    raise unittest.SkipTest('No module named _testcapi')\n"
            "    def test_t(self): pass\n"
        )
        methods = [{"cls": "A", "method": "test_a", "stem": "m.A.test_a"},
                   {"cls": "T", "method": "test_t", "stem": "m.T.test_t"}]
        try:
            result = oracle.run_file("m.py", source, methods)
        except unittest.SkipTest as e:
            # Left uncaught, it would skip this test instead of failing it.
            self.fail(f"run_file let SkipTest escape: {e}")
        self.assertEqual(result["outcomes"],
                         {"m.A.test_a": "skipped", "m.T.test_t": "skipped"})
        self.assertIn("_testcapi", result["detail"]["m.A.test_a"])


if __name__ == "__main__":
    unittest.main()
