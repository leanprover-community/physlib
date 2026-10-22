# Placement and imports

Where does the new material live, and what does it import? Uses `request_changes`. File
length is linter-enforced; do not re-report it. `shake` is not yet enforced, so report only
imports whose wrongness is evident from the diff or the dependency topic.

## Placement

- Each declaration belongs in its canonical home: the file whose topic, level, and
  dependencies fit it, near the definition or result it elaborates. If it belongs in an
  earlier `TauCeti/` file, or depends on no later theory and is broadly useful, ask to move it
  there.
- Reject generic placement for declarations whose hypotheses or names are roadmap-specific:
  do not let roadmap-specific lemmas masquerade as reusable by living in a generic file.
- New files join an existing topic subdirectory when one fits. When two files share a
  leading CamelCase component and that component names the common subject they organize
  around, they should be a directory: a PR whose new file would put both `Foo.lean` and
  `FooBar.lean` (or two `Foo*.lean` files) in one directory moves them in the same PR,
  creating `Foo/` with `Foo.lean` as `Foo/Basic.lean` (`Foo/Defs.lean` when
  definitions-only) and each `FooBar.lean` as `Foo/Bar.lean` (mechanical `git mv` plus
  imports; no declaration renames), the new file placed there. `request_changes` when a
  PR instead leaves those siblings flat. When the shared component does not name their
  common subject (a mathematician's name across unrelated subjects, or a generic
  adjective), raise no finding from the shared prefix.
- `private` is not a substitute for correct placement. If a declaration is in the wrong home, ask
  for the move; do not accept hiding it as the fix.
- A relocation updates every in-repository import and deletes the old module path in the same PR.
  Require deletion of forwarding import modules and `deprecated_module` shims; preserving an old
  path for external users is not part of placement.

## Imports

- Flag only an evidently wrong import: unused, or a broad `import Mathlib` where
  specific modules would do. Do not request a direct import for something already
  available transitively; that is redundant and `shake` removes it.

## Verdict

- `request_changes` for a declaration in the wrong home, material that belongs in an earlier
  file, roadmap-specific material hidden in a generic file, a compatibility-only module, or an
  evidently wrong import.
- `approve` when each declaration is in its natural place and no import is unused or
  unnecessarily broad.
