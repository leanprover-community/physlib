#!/usr/bin/env python3
"""Integration tests for migrate, using temporary Lake projects.

Run `lake build migrate`, then `lake env python3 scripts/dev/test_migrate.py`.
"""

import json
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
def shadowReplacement (fresh : Nat) : Nat := old
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
        env = os.environ.copy()
        env["LEAN_PATH"] = str(self.project / ".lake/build/lib/lean") + os.pathsep + env.get(
            "LEAN_PATH", "",
        )
        result = subprocess.run(
            [str(EXECUTABLE), *args], cwd=self.project,
            text=True, capture_output=True, env=env, timeout=120,
        )
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def assert_migrated(self, path):
        text = path.read_text()
        shadow = next(line for line in text.splitlines() if line.startswith("def shadowReplacement"))
        self.assertIn("MigrationFixture.fresh", shadow)
        text = text.replace("_root_.MigrationFixture.", "")
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

    def build_libraries(self):
        result = subprocess.run(
            ["lake", "build", "First", "Second"], cwd=self.project,
            text=True, capture_output=True, timeout=120,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_cached_references(self):
        self.build_libraries()
        # Restored artifacts can have timestamps older than their matching sources.
        ilean = self.project / ".lake/build/lib/lean/First.ilean"
        content = ilean.read_bytes()
        ilean.unlink()
        ilean.write_bytes(content)
        os.utime(ilean, (1, 1))
        result = self.run_migrate("First")
        self.assertIn(f"{self.first}: migrated", result.stdout)
        self.assertIn(
            "using cached references", result.stdout,
            result.stdout + result.stderr,
        )
        self.assert_migrated(self.first)
        self.assertEqual(self.second.read_text(), SOURCE)

    def test_restored_cache_without_source_hash_entries(self):
        self.build_libraries()
        trace = self.project / ".lake/build/lib/lean/First.trace"
        data = json.loads(trace.read_text())
        data["synthetic"] = True
        data["inputs"] = []
        trace.write_text(json.dumps(data))
        result = self.run_migrate("First")
        self.assertIn("using cached references", result.stdout, result.stdout + result.stderr)
        self.assert_migrated(self.first)

    def test_stale_cache_falls_back_to_elaboration(self):
        self.build_libraries()
        self.first.write_text("-- Shift every cached source range.\n" + SOURCE)
        result = self.run_migrate("First")
        line = next(
            (line for line in result.stdout.splitlines() if line.startswith(str(self.first))),
            result.stdout + result.stderr,
        )
        self.assertIn("using elaboration", line)
        self.assert_migrated(self.first)

    def test_corrupted_cache_falls_back_to_elaboration(self):
        self.build_libraries()
        ilean = self.project / ".lake/build/lib/lean/First.ilean"
        ilean.unlink()
        ilean.write_text("invalid cached references")
        result = self.run_migrate("First")
        line = next(
            (line for line in result.stdout.splitlines() if line.startswith(str(self.first))),
            result.stdout + result.stderr,
        )
        self.assertIn("using elaboration", line)
        self.assert_migrated(self.first)

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
        self.build_libraries()
        result = self.run_migrate("First")
        self.assertIn("using cached references", result.stdout, result.stdout + result.stderr)
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
        self.build_libraries()
        result = self.run_migrate("First")
        self.assertIn("using cached references", result.stdout, result.stdout + result.stderr)
        text = self.first.read_text().replace("_root_.", "")
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
