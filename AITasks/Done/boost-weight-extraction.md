# Prepare the boost-weight product and parity extraction

## Task and output

Perform a read-only mathematical and dependency investigation. Write your findings to
`AITasks/Done/boost-weight-extraction-report.md`. This is preparation for a bounded
post-bump extraction, not implementation or a claim of Lean verification. No prior
chat is needed, and this task does not depend on the coefficient-lifting report.

Determine which boost-weight multiplication, support and parity results currently in
Standard Model files should be reusable general results, and precisely how to extract
them without changing the existing classifications or strengthening their assumptions.

## Source baseline and working rules

This handoff was checked against PR #1415 source commit
`5589e23dde62da95d6f7e4d9467cf63ecc111680` (Lean/Mathlib 4.33.0). A separate task is
integrating upstream's 4.34.0 bump. Use a separate checkout supplied by the human, not
the active bump workspace. Record the actual commit, toolchain, manifest revision and
any relevant dirty source files you inspect. If the PR has advanced, locate the named
declarations and report material differences. Do not invent missing source content.

Read `AGENTS.md`, `AI-POLICY.md` and `docs/ReviewGuidelines.md`.

- Only write the output report. Leave this task file in `ToDo` for human acceptance.
- Do not edit Lean files, imports, dependencies, other reports or the roadmap.
- Do not run Lean probes, builds, cache downloads, dependency updates or linters.
  This task-specific restriction overrides repository default validation instructions.
- Do not stage, commit, push, fetch, switch branches, stash, reset or delete files.
- Do not interrupt workers or contact reviewers. Preserve all pre-existing work.
- Inspect locally available Mathlib source if useful, recording its version. Reserve
  claims about 4.34.0 API availability for that version's actual source or later probes.

## Sources to read

1. `Physlib/Relativity/LorentzGroup/Boosts/WeightGrading.lean`:
   - `Lorentz.BoostWeight.boostWeightSubmodule`
   - `mul_mem_boostWeightSubmodule`, `boostWeightSubmodule_iSupIndep`
   - `mem_boostWeightSubmodule_zero_of_invariant`
   - `mem_of_mem_iSup_of_boostWeight_zero`
   - `WeightDecomposition` and its `copy`/`sup` API
2. `Physlib/Particles/StandardModel/CovAlgebraRealization/YukawaSector/MassDimLTEight.lean`:
   sections A and B, in `Lorentz.BoostWeight.WeightDecomposition`:
   - `mul_le_iSup_convolution`, `mulOfMul`, `mulOfMul_supp`
   - `exists_add_eq_of_mem_mulOfMul_supp`
   - `two_dvd_of_mem_mulOfMul_supp`, `not_two_dvd_of_mem_mulOfMul_supp`
   - `sup_supp`, `map_boostWeightSubmodule_le`
   - `mem_of_invariant_of_mem_sup_of_odd_supp`
   Read the later SM applications to understand their contracts, not to refactor them.
3. `Physlib/Particles/StandardModel/AlgebraRealization/HiggsAlgebraCovRealization/DerivSubmodule/BoostWeightDecomposition.lean`:
   - the general `WeightDecomposition.ofTrivialAction` and its computation rules;
   - the Higgs specializations as consumers and evidence for the general/SM boundary.
4. Supporting interfaces as needed:
   - `Physlib/Relativity/LorentzGroup/Invariants/LorentzCovariance.lean`
   - `Physlib/Relativity/IsLorentzDeriv.lean`
   - `Physlib/Relativity/Fermions/Weyl/BoostWeight.lean`

Search for all actual uses of the candidate declarations. No untracked historical
report or Standard Model table prototype is required.

## Questions to resolve

### 1. Exact extraction inventory

For each candidate, record its full namespace, source location, effective hypotheses,
proof dependencies and consumers. Classify it as:

- pure submodule/finite-support mathematics;
- general Lorentz boost-weight mathematics;
- a Standard Model specialization;
- a possible wrapper of existing library machinery.

Check section variables and `omit` directives; do not mistake the surrounding file's
imports or variables for genuine mathematical prerequisites of a declaration.

### 2. Product construction

Explain how the product decomposition is constructed: its weight-`m` piece is the join
of products of pieces with weights `k + l = m`, its chosen finite support is the sum
of the two chosen supports, and its pieces span `V * W`.

Trace all obligations back to their assumptions, particularly multiplicativity of the
representation, scalar compatibility and distributivity of submodule products over
joins. Preserve factor order: the existing algebra is a ring, not assumed commutative.
Do not introduce a direct-sum grading, homogeneous basis, canonical decomposition or
finite-dimensional ambient module unless actually required by the source contract.

Review whether `mul_le_iSup_convolution` needs its current assumptions or is better
replaced by a library result. Distinguish a useful simplification from gratuitous
generalization. Explain the role of `ofTrivialAction` without expanding into Higgs
derivative constructions.

### 3. Support and parity semantics

Read the fields of `WeightDecomposition` literally. At the reference revision,
`piece_eq_bot` requires vanishing outside `supp`; it does not require each member of
`supp` to have a nonzero piece. Determine the consequences for the current docstrings
and for claims about sums of supports. Do not silently strengthen the structure.

Explain the even/even and even/odd results on this chosen finite support, including
zero submodules and redundant support entries. Distinguish boost-weight parity from
fermionic statistics and from mass dimension; do not conflate them.

### 4. Excluding invariants, including modulo a stable submodule

Explain why Lorentz invariance implies boost weight zero, while weight zero for one
axis does not by itself imply Lorentz invariance.

Trace the proof of `mem_of_invariant_of_mem_sup_of_odd_supp`: quotient action, stability
of `S`, equivariance of `S.mkQ`, images of weight pieces, and elimination of the zero
piece. Determine whether the proof uses oddness only to show the zero piece vanishes.
If so, assess a zero-piece criterion with an odd-support corollary as a small candidate
improvement; do not presuppose that a new API is necessary.

Identify any genuine dependence on the separate invariant-coefficient lifting theorem.
Do not redesign general peeling/composition or classify new representations.

### 5. Homes, imports and consumer impact

Propose minimal destinations and dependency directions. Prefer existing appropriate
modules, notably `Boosts/WeightGrading.lean`, unless a different home has a concrete
mathematical or import justification. General results must not import SM applications.

Inventory the library calls that might replace trivial helpers. Identify declarations
to move unchanged versus candidates requiring a statement/docstring adjustment.
For each adjustment, state how the old consumer contract would still be recovered.
Do not rename or generalize things solely to make the report appear more ambitious.

The source containing the product/parity results is behind the inherited
`StandardModel.JetAlgebra.SectorEquiv.Basic` blocker at the reference revision. A
proof-looking source is not evidence of a successful current build. Explain how a
later standalone generic probe can validate extraction and which original consumer
builds would remain owed. Do not repair or build that blocker.

## Report requirements and completion

Write a focused report with:

1. Source provenance and exact scope inspected.
2. Declaration table: hypotheses, genuine dependencies, proposed home and consumers.
3. Mathematical account of product decomposition, support and quotient/parity logic.
4. Any documentation overclaims or mathematical risks, with exact source references.
5. Bounded extraction proposal, separating required work from optional improvements.
6. Post-bump Lean experiment checklist and stop/go gates.

The experiment checklist should cover destination-only imports, exact old consumer
contracts, preservation of noncommutative factor order, redundant/empty support cases,
zero-piece/odd-support conclusions and principal axiom audits. Identify blocked
production consumers separately from restated application probes.

Separate source-verified facts, mathematical deductions and uncompiled Lean sketches.
Do not claim builds, benchmarks, optimal assumptions or formal verification. Provide
counterevidence and unresolved choices where appropriate. The report should let a
fresh agent begin a narrowly scoped 4.34.0 spike or implementation after human review.

Finish in chat with the report path and material findings/uncertainties. Confirm that
only the report was added or changed. Report delivery is not implementation acceptance.
