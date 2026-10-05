#!/usr/bin/env python3
"""Regression checks for a manuscript-free distribution and complete source/audit coverage."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import reader_catalog as catalog


class ReaderValidationTests(unittest.TestCase):
    def data(self):
        return copy.deepcopy(json.loads(catalog.CATALOG.read_text()))

    def test_real_catalog_passes_without_manuscripts(self):
        data = self.data()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "lean-volume4"
            for name in data["lean_inputs"]:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(catalog.ROOT / name, target)
            self.assertFalse((root.parent / "books").exists())
            with patch.object(catalog, "ROOT", root):
                _, _, coverage = catalog.validate(data)
            self.assertEqual(coverage["matched_code_blocks"], 89)
            self.assertEqual(coverage["audited_declarations"], 212)

    def test_private_manuscript_fields_rejected(self):
        data = self.data()
        data["source_files"] = {"books/private/ch19.md": "0" * 64}
        with self.assertRaisesRegex(ValueError, "reader catalog"):
            catalog.validate(data)

    def test_common_source_missing_rejected(self):
        data = self.data()
        del data["lean_inputs"]["Volume4Stage0/FourPoint.lean"]
        with self.assertRaisesRegex(ValueError, "Lean inputs"):
            catalog.validate(data)

    def test_changed_dependency_pin_rejected(self):
        data = self.data()
        data["lean_inputs"]["lake-manifest.json"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Lean inputs"):
            catalog.validate(data)

    def test_source_path_traversal_rejected(self):
        data = self.data()
        data["lean_inputs"]["../private.lean"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "source path"):
            catalog.validate(data)

    def test_missing_and_duplicate_examples_rejected(self):
        for duplicate in (False, True):
            data = self.data()
            if duplicate:
                data["blocks"][-1] = copy.deepcopy(data["blocks"][0])
            else:
                data["blocks"].pop()
            with self.subTest(duplicate=duplicate), self.assertRaisesRegex(ValueError, "reader block"):
                catalog.validate(data)

    def test_inspection_cannot_be_counted_as_proof(self):
        data = self.data()
        next(r for r in data["blocks"] if r["purpose"] == "statement_inspection")["purpose"] = "completed_proof"
        with self.assertRaisesRegex(ValueError, "classification"):
            catalog.validate(data)

    def test_duplicate_audit_declaration_rejected(self):
        data = self.data()
        data["declarations"][-1] = copy.deepcopy(data["declarations"][0])
        with self.assertRaisesRegex(ValueError, "audit declaration"):
            catalog.validate(data)

    def test_missing_and_extra_axiom_output_rejected(self):
        for output in ("", "'A.x' does not depend on any axioms\n'A.y' does not depend on any axioms"):
            with self.subTest(output=output), self.assertRaisesRegex(ValueError, "audit target"):
                catalog.parse_axioms(output, ["A.x"])

    def test_sorry_custom_axioms_and_duplicate_output_rejected(self):
        for output in ("'A.x' depends on axioms: [sorryAx]",
                       "'A.x' depends on axioms: [Custom.assumption]",
                       "'A.x' does not depend on any axioms\n'A.x' does not depend on any axioms"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                catalog.parse_axioms(output, ["A.x"])

    def test_standard_axioms_are_parsed_exactly(self):
        output = "'A.B.c' depends on axioms: [propext, Quot.sound]\n'A.d' does not depend on any axioms"
        self.assertEqual(catalog.parse_axioms(output, ["A.B.c", "A.d"]),
                         {"A.B.c": ["propext", "Quot.sound"], "A.d": []})

    def test_coded_and_plain_diagnostics_rejected(self):
        for output in ("warning: declaration uses sorry", "error(lean.unknownIdentifier): missing"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                catalog.check_diagnostics(output)


if __name__ == "__main__":
    unittest.main()
