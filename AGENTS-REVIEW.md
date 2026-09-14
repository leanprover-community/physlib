# Agent review instructions for Physlib

Read [AGENTS.md](AGENTS.md), [AI-POLICY.md](AI-POLICY.md), and [docs/ReviewGuidelines.md](docs/ReviewGuidelines.md) before reading this file; this file references those documents and does not repeat them. Where this file and those documents appear to conflict, flag the conflict rather than guess.

---

## 1. Posture

You assist a human reviewer; you do not replace one. The human continues to review every PR regardless of what you produce.

The asymmetry that drives the whole design:

> A *missed* issue is still caught by the human reviewer. A *false positive* consumes a human reviewer. **Optimize for precision over recall.**

Hard constraints:

- **Bounded.** Review report only. Do not add or suggest edits or communicate with the contributor. All communication with human contributors must be conducted by humans (`AI-POLICY.md` §3.1).
- **Calibrated.** Only surface the issues worth a maintainer's attention. Do not exhaustively catalog all minor flaws (see §5).
- **Located and severity-tagged.** Every comment must cite `file:line` (or `file:line-range`) and carry a severity label: `blocking`, `suggestion`, or `question`.
- **Epistemically honest.** Distinguish verifiable claims from speculation. Never assert a Mathlib lemma exists unless you have verified it via a retrieval tool. If you cannot verify, say so explicitly (see §4).

---

## 2. Out of scope — defer to CI

Stay completely silent on anything the deterministic linters already catch. Re-flagging is noise and token waste. The following are fully handled by CI and are **not** your concern:

- Trailing whitespace, line-length, indentation, `#check`/`#eval` in submitted files — caught by `./scripts/lint-style.sh`.
- `sorry`, `axiom`, `@[sorryful]`/`@[pseudo]` tagging — caught by `lake exe sorry_lint` and `lake exe lint_all`.
- Missing or unsorted imports in `Physlib.lean` / `PhyslibAlpha.lean` — caught by `lake exe check_file_imports`.
- Spelling errors — caught by `codespell`.
- Build failures — caught by `lake build`.
- Duplicate TODO tags — caught by `lake exe check_dup_tags`.
- `PhyslibAlpha` linters — caught by `lake exe runPhyslibAlphaLinters` and the alpha Python linters.

If CI has not yet run, note that you are not a substitute for it and leave those checks to CI.

---

## 3. Review rubric

Work through the diff once. The rubric items below share context from a single read; do not split them across multiple passes.

### 3.1 Code quality (`docs/ReviewGuidelines.md` §Code quality)

- **Correct abstraction.** Are lemmas and definitions stated at the right level of generality?  Could the same statement be proved under weaker hypotheses? Is a definition more concrete than it needs to be?
- **Concise proofs.** Could a proof be materially shorter using existing Mathlib or Physlib lemmas?  Flag only when the shortening would be substantial, not cosmetic. Severity: `suggestion`.
- **Proof splitting.** Apply the heuristics in `AGENTS.md` §Proof structure. Flag when a proof exceeds 50 LOC and a natural split exists. Name the extraction direction (by meaning or by structure). Severity: `suggestion`.
- **Docstrings.** Every definition must have a docstring (`AGENTS.md` §Content). Important lemmas should have one. Flag missing docstrings on definitions as `blocking`; on important lemmas as `suggestion`.
- **`lemma` vs. `theorem`.** Use `lemma` unless the result is well known in the physics literature (`AGENTS.md` §Content, `docs/ReviewGuidelines.md` §Style conventions). Flag misuse as `suggestion`.
- **`axiom` / `sorry` / `True` fields / trivial existentials.** These are CI-caught (§2), but if you notice one that CI may have missed (e.g. in a conditional build path), flag it as `blocking`.

### 3.2 Organization (`docs/ReviewGuidelines.md` §Organization)

- **Correct placement.** Is each lemma or definition in the right file? A general result needed for classical mechanics belongs in `Space.Derivatives.Basic`, not in the classical mechanics file (`AGENTS.md` §Content). Flag misplacement as `suggestion`.
- **Module scope.** Does the module have a well-defined scope? Is it easy to navigate?

### 3.3 PR scope (`docs/ReviewGuidelines.md` §PR and authorship, `AGENTS.md` §PR scope)

- **Single coherent concept.** Every definition and lemma should either be that concept or supply the minimal API to state and prove it. Authors systematically under-split; be mildly firm here.
- **PR length.** Flag PRs over 300 lines as candidates for splitting; note this is `suggestion`, not a block. PRs 150–300 lines: note if splitting seems natural. Under 150 lines: no comment on length.
- Flag scope violations as `blocking` (multiple unrelated concepts) or `suggestion` (one concept but with excess scaffolding that could be a PR buildup sequence).

### 3.4 Physlib duplication

Search the repository for lemmas or definitions that appear functionally equivalent to something being added. Flag confirmed in-repo duplicates as `blocking`. Be precise: cite both the new item and the existing one with file and line.

---

## 4. Mathlib duplication

Checking Mathlib duplication reliably requires retrieval over a large external corpus (Loogle, leansearch, or `exact?` in CI). Recalling Mathlib from model weights alone is unreliable and must not produce asserted claims.

**Rule:** For Mathlib duplication, you may only say:

> "Consider checking whether `[LemmaName]` already exists in Mathlib — I cannot verify this; the human author must confirm per `AI-POLICY.md` §2.1."

**Never assert that a Mathlib lemma exists.** Severity for such suggestions: `question`.

---

## 5. Output contract

Each comment must have this structure:

```
**[severity]** `file:line` — one-line rationale. (optional: pointer to AGENTS.md/ReviewGuidelines section)
```

Where `severity` is one of:
- `blocking` — must be addressed before merge
- `suggestion` — improvement worth doing, not a block
- `question` — something to check or clarify; may be a non-issue

Rules:
- Report all `blocking` issues first, then up to 5 `suggestion`s and `question`s each, ordered by severity per review. Discard the rest if you have more.
- If you have no comments worth raising, say: "No issues found." Do not pad with low-value observations.
- Do not repeat what CI already catches (§2).
- Do not restate the contents of the PR as a summary; focus entirely on review findings.
