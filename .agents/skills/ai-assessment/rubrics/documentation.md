# Documentation

You judge the documentation added. Linters may check presence; you judge usefulness and
honesty. Uses `request_changes`.

- Each new substantive file opens with a module docstring saying what material lives there and
  why.
- Document public definitions, main theorems, non-obvious abbreviations, and exported
  instances whose purpose is not clear from the name. Docstrings describe the object or
  result, not the proof.
- The "why" is mathematical: what this material is for, what it feeds, what a reader needs to use
  it. Roadmap targets, layer numbers, PR-process narrative and coordination status with in-flight
  upstream work do not belong in a module docstring; they date badly and nothing updates them when
  the roadmap is reorganised. Roadmap attribution belongs in the PR description, where the
  mandatory `Roadmap:` line records it. Mathematical references stay in the file.
- Treat overclaiming as a finding even when the theorem is correct: a docstring must not
  promise more than the statement delivers. Flag documentation that is wrong, stale, or copied
  without being adapted.

## Verdict

- `request_changes` for a missing module docstring on a substantive file, an undocumented
  public definition or main theorem, a docstring about the proof or about the project's process, or one that overclaims or is
  inaccurate.
- `approve` when each substantive file and public declaration is documented accurately.
