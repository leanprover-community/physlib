# Placement and imports

Where does the new material live, and what does it import? `AGENTS.md` asks to place results in
the appropriate existing file and not to create new files without good reason: for example, a
general result about derivatives on space needed for a classical mechanics proof belongs in
`Space.Derivatives.Basic`, not in the classical mechanics file. `docs/ReviewChecklist.md`
(Level 2) asks whether a reader could find each result from the file structure alone.

## Placement

- Each declaration belongs in its canonical home: the file whose topic, level, and
  dependencies fit it, near the definition or result it elaborates. If it belongs in an
  earlier file (in `Physlib/Mathematics/`, `Physlib/SpaceAndTime/`, or the general file of its
  subject), or depends on no later theory and is broadly useful, suggest moving it there.
- Material in `Physlib/Mathematics/ForMathlib/` should be stated as it would be in Mathlib and
  import only from within that directory.
- Specialised lemmas should not masquerade as reusable by living in a generic file, nor
  general lemmas hide in a specialised one.
- New files join an existing topic subdirectory when one fits, and their names should let a
  reader guess their content. Suggest a better name or location when they do not.
- `private` is not a substitute for correct placement. If a declaration is in the wrong home,
  suggest the move.
- New files need to be imported into `Physlib.lean`, `QuantumInfo.lean` or `PhyslibAlpha.lean`;
  CI checks this, so do not re-report it.

## Imports

- Point out only an evidently wrong import: unused, or a broad `import Mathlib` where specific
  modules would do. Do not suggest a direct import for something already available
  transitively.

## Score guidance

- 2–3 for declarations in the wrong home, material that belongs in an earlier file, a new
  file that could have been avoided, or an evidently wrong import.
- 5 when each declaration is in its natural place and no import is unused or unnecessarily
  broad.
