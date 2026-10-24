"""Negative controls for the report gate; these tests do not prove the manuscript."""
from pathlib import Path
import tempfile,unittest
from verify_axioms import inspect

class ReportGate(unittest.TestCase):
    def check_report(self,text):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'report.log';p.write_text(text,encoding='utf-8')
            return inspect(p,['target'])
    def test_standard_axioms(self):
        self.assertEqual(self.check_report("'target' depends on axioms: [propext, Classical.choice, Quot.sound]"),
                         {'target':['Classical.choice','Quot.sound','propext']})
    def test_missing_report(self):
        with self.assertRaises(AssertionError):self.check_report('Build completed successfully.')
    def test_extra_axiom(self):
        with self.assertRaises(AssertionError):self.check_report("'target' depends on axioms: [propext, assumption] ")
    def test_reduction_shortcut(self):
        with self.assertRaises(AssertionError):self.check_report("'target' depends on axioms: [ofReduceBool]")
    def test_wrong_endpoint(self):
        with self.assertRaises(AssertionError):self.check_report("'different_target' depends on axioms: [propext]")

if __name__=='__main__':unittest.main()
