#!/usr/bin/env python3
"""Integration tests for migrate, using temporary Lake projects.

Run `lake build migrate`, then `lake env python3 scripts/dev/test_migrate.py`.
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
EXECUTABLE = ROOT / ".lake/build/bin/migrate"
SOURCE = '''import Lean
namespace Nat
def freshNext (n : Nat) : Nat := n + 1
@[deprecated freshNext (since := "2026-01-01")]
def oldNext (n : Nat) : Nat := freshNext n
end Nat
namespace MigrationFixture
def fresh : Nat := 7
@[deprecated fresh (since := "2026-01-01")]
def old : Nat := fresh
@[deprecated old (since := "2026-01-01")]
def older : Nat := old
@[deprecated "Use an appropriate value" (since := "2026-01-01")]
def noReplacement : Nat := 8
-- old is deliberately mentioned in this comment: λ
def label : String := "old"
def localName (old : Nat) : Nat := old
def usage : Nat := old
def qualified : Nat := MigrationFixture.old
def unchanged : Nat := noReplacement
def «unicode_λ» : Nat := old
def chain : Nat := older
def field (n : Nat) : Nat := n.oldNext
example : old = 7 := by simp only [old, fresh]
end MigrationFixture
'''


class MigrateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="physlib-migrate-")
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name)
        (self.project / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
        (self.project / "lakefile.toml").write_text('''name = "MigrationTest"
[[lean_lib]]
name = "First"
[[lean_lib]]
name = "Second"
srcDir = "src"
roots = ["Different"]
''')
        (self.project / "First").mkdir()
        (self.project / "src").mkdir()
        self.first = self.project / "First.lean"
        self.nested = self.project / "First/Nested.lean"
        self.second = self.project / "src/Different.lean"
        for path in [self.first, self.nested, self.second]:
            path.write_text(SOURCE)

    def run_migrate(self, *args, success=True):
        result = subprocess.run(
            [str(EXECUTABLE), *args], cwd=self.project,
            text=True, capture_output=True, env=os.environ.copy(), timeout=120,
        )
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def assert_migrated(self, path):
        text = path.read_text()
        self.assertIn("def usage : Nat := fresh", text)
        self.assertIn("def «unicode_λ» : Nat := fresh", text)
        self.assertIn("def chain : Nat := fresh", text)
        self.assertIn("def field (n : Nat) : Nat := n.freshNext", text)
        self.assertIn("example : fresh = 7 := by simp only [fresh, fresh]", text)
        self.assertIn("def old : Nat := fresh", text)
        self.assertIn("def unchanged : Nat := noReplacement", text)
        self.assertIn("def localName (old : Nat) : Nat := old", text)
        self.assertIn('def label : String := "old"', text)
        self.assertIn("-- old is deliberately mentioned in this comment: λ", text)

    def test_selected_library_and_idempotence(self):
        self.run_migrate("First")
        self.assert_migrated(self.first)
        self.assert_migrated(self.nested)
        self.assertEqual(self.second.read_text(), SOURCE)
        before = self.first.read_bytes()
        result = self.run_migrate("First")
        self.assertEqual(self.first.read_bytes(), before)
        self.assertNotIn("migrated ", result.stdout)

    def test_defaults_discover_all_libraries(self):
        self.run_migrate()
        for path in [self.first, self.nested, self.second]:
            self.assert_migrated(path)

    def test_unknown_library_does_not_edit(self):
        result = self.run_migrate("Missing", success=False)
        self.assertIn("Unknown top-level lean_lib: Missing", result.stderr)
        self.assertEqual(self.first.read_text(), SOURCE)

    def test_module_system(self):
        source = SOURCE.replace(
            "import Lean", "module\npublic import Lean\n\n@[expose] public section", 1,
        )
        self.first.write_text(source)
        self.run_migrate("First")
        self.assert_migrated(self.first)

    def test_escaped_names_and_local_shadowing(self):
        source = '''import Lean
namespace Nat
def «fresh-next» (n : Nat) : Nat := n + 1
@[deprecated «fresh-next» (since := "2026-01-01")]
def oldNext (n : Nat) : Nat := «fresh-next» n
end Nat
def usage (n : Nat) := n.oldNext
def shadow (fresh : Nat) := Nat.oldNext fresh
'''
        self.first.write_text(source)
        self.run_migrate("First")
        text = self.first.read_text()
        self.assertIn("def usage (n : Nat) := n.«fresh-next»", text)
        self.assertIn("def shadow (fresh : Nat) := Nat.«fresh-next» fresh", text)

    def test_failed_replacement_leaves_file_unchanged(self):
        source = '''import Lean
def newValue : String := "changed type"
@[deprecated newValue +typeChanged (since := "2026-01-01")]
def oldValue : Nat := 1
def usage : Nat := oldValue
'''
        self.first.write_text(source)
        result = self.run_migrate("First", success=False)
        self.assertIn("file left unchanged", result.stderr)
        self.assertEqual(self.first.read_text(), source)
        self.assert_migrated(self.nested)

    def test_original_parse_error_leaves_file_unchanged(self):
        source = SOURCE + "\ndef broken : Nat :=\n"
        self.first.write_text(source)
        self.run_migrate("First", success=False)
        self.assertEqual(self.first.read_text(), source)


if __name__ == "__main__":
    unittest.main()
