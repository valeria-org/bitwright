"""Regression checks for the audit's semantic boundary, not rule proofs."""
import unittest

from valeria_rule_cases import Binding, Instance, Refusal, masked, parse


class TranslationTests(unittest.TestCase):
    def test_meta_width_and_bit_scan_contracts(self):
        instance = Instance(128, {})
        self.assertEqual(instance.meta(parse("meta_shl(1, 128)")), 0)
        self.assertEqual(instance.meta(parse("meta_sub(meta_shl(1, 128), 1)")), (1 << 128)-1)
        self.assertEqual(instance.meta(parse("bsf_meta(8)")), 4)

    def test_signed_negation_guard_needs_value_evidence(self):
        guard = parse("guard_or(expr_cmp(eq, $w, 0), expr_cmp(ne, neg($w), $w))")
        self.assertTrue(Instance(8, {"$w": masked("p", 8, 252, 1)}).guard(guard))
        self.assertFalse(Instance(8, {"$w": 128}).guard(guard))
        with self.assertRaises(Refusal):
            Instance(8, {}).guard(guard)

    def test_known_bits_come_from_constructed_masks(self):
        instance = Instance(16, {"$b": masked("p", 16, 0x0c, 1)})
        self.assertEqual(instance.meta(parse("mask_known_one($b)")), 1)
        self.assertEqual(instance.meta(parse("mask_unknown($b)")), 12)
        self.assertEqual(instance.meta(parse("mask_known_zero($b)")), 0xfff2)

    def test_wide_if_uses_nonzero_truthiness(self):
        text, width, _ = Instance(8, {"$u": 2}).expr(parse("if($u, $a)"))
        self.assertIn("!= 0:8", text)
        self.assertEqual(width, 8)

    def test_counts_are_masked_before_resizing(self):
        instance = Instance(8, {"$a": Binding("a:2", 2), "$b": 35})
        self.assertIn("2:2", instance.expr(parse("shl($a, $b)"))[0])
        self.assertIn("1:2", instance.expr(parse("rol($a, $b)"))[0])
        with self.assertRaises(Refusal):
            instance.expr(parse("sar($a, $b)"))
        with self.assertRaises(Refusal):
            Instance(96, {}).expr(parse("sar($a, 1)"))

    def test_partial_division_and_choice_fail_closed(self):
        with self.assertRaises(Refusal):
            Instance(8, {}).expr(parse("udiv($a, 0)"))
        result = Instance(8, {}).expr(parse("choice(iff(meta_eq(1, 0), $a), $b)"))
        self.assertEqual(result[0], "b")


if __name__ == "__main__":
    unittest.main()
