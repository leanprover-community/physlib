# Prepare the shared invariant-coefficient lifting investigation

## Task and output

Perform a read-only mathematical and dependency investigation. Write your findings to
`AITasks/Done/invariant-coefficient-sharing-report.md`. This is preparation for a later
Lean spike, not implementation or a claim of Lean verification. No prior chat is needed.

The aim is to identify one natural theorem from which the existing Lorentz and gauge
invariant-coefficient lifting results follow without stronger hypotheses.

## Source baseline and working rules

This handoff was checked against PR #1415 source commit
`5589e23dde62da95d6f7e4d9467cf63ecc111680` (Lean/Mathlib 4.33.0). A separate task is
integrating upstream's 4.34.0 bump. Use a separate checkout supplied by the human, not
the active bump workspace. Record the actual commit, toolchain, manifest revision and
any relevant dirty source files you inspect. Do not assume the current PR head matches
this reference. If declarations have moved, locate them and report the difference; if
essential sources are unavailable, report that limitation rather than inventing them.

Read `AGENTS.md`, `AI-POLICY.md` and `docs/ReviewGuidelines.md`.

- Only write the output report. Leave this task file in `ToDo` for human acceptance.
- Do not edit Lean files, imports, dependencies, other reports or the roadmap.
- Do not run Lean probes, builds, cache downloads, dependency updates or linters.
  This task-specific restriction overrides repository default validation instructions.
- Do not stage, commit, push, fetch, switch branches, stash, reset or delete files.
- Do not interrupt workers or contact reviewers. Preserve all pre-existing work.
- Inspect locally available Mathlib source if useful, recording its version. Absence
  from that snapshot is not proof of absence from Mathlib 4.34.0.

## Sources to read

1. `Physlib/Relativity/LorentzGroup/Invariants/Basic.lean`:
   - `Lorentz.Invariants.contractₗ`
   - `Lorentz.Invariants.exists_invariantCoeff`
   - `actMat`, `actMatₗ`, `inner_actMat`, `exists_invariantCoeff_matrix`
   - `exists_isInvariantCoeff_of_mem_span`
2. `Physlib/Particles/StandardModel/GaugeGroup/Invariants/Basic.lean`:
   - `StandardModel.Family.contractₗ`, `actₗ`, `inner_actₗ`
   - `sum_star_mul_of_transpose`, `exists_invariant_coeff`
   - section C's `exists_mem_add_of_mem_sup`, `exists_smul_add_of_mem_sup`
3. For existing supporting APIs and representative callers:
   - `Physlib/Relativity/LorentzGroup/Invariants/LorentzCovariance.lean`
   - `Physlib/Mathematics/LinearCombination.lean`
   - the three `Invariants/Is*Weyl.lean` modules
   - `StandardModel/GaugeGroup/Invariants/IsSU2BiFundamental.lean` and
     `IsSU3FunAntiFun.lean` (under `Physlib/Particles/`)

Search for actual callers; this list is a starting point, not a complete inventory.
No untracked historical report or Standard Model table prototype is required.

## Questions to resolve

### 1. Exact contract comparison

Transcribe the two principal statements with their effective section variables,
typeclasses and universes. Tabulate all differences, including conclusion ordering.

Both seek coefficients in a finite family `T : ι → B` such that
`x = ∑ i, c i • T i` and every supplied coefficient map fixes `c`.
The family may be linearly dependent; neither uniqueness nor injectivity is promised.

At the reference commit, the Lorentz lifting theorem accepts an arbitrary index type
`G` and an adjoint-closure witness for each map. The gauge theorem has `[Group G]` and
an explicit inverse-adjoint identity on coefficients. Inspect the actual assumptions:
do not infer action laws, invertibility or unitarity solely from comments calling `A`
an action. Explain which laws are assumed, which follow and which are unused.

Track where the proof needs complex scalars, finite coefficient dimension, orthogonal
decomposition and the `WithLp` conversions. Distinguish the inner product on coefficient
space from the target `B`; do not impose an inner product or finite dimension on `B`.

### 2. Common proof mechanism

Give a precise proof correspondence, with source declaration/line references:

- The contraction map `q`, its kernel `K`, and the intertwining equation.
- Why the coefficient maps preserve `K`.
- Why the adjoint condition makes `Kᗮ` invariant.
- Why replacing a preimage by its component in `Kᗮ` preserves its image.
- Why the change under a transformation lies in both `K` and `Kᗮ`, hence is zero.

Explain the distinction between an invariant expression and an arbitrary coefficient
description of it. Analyse a dependent family and the empty-index boundary on paper.
Do not assume invariant lifting for arbitrary representations.

### 3. Candidate abstraction and library reuse

Identify existing Mathlib/Physlib results that may supply the argument or its steps.
Give exact declarations and checked source versions, not guesses about available APIs.

Propose the smallest natural common statement. Compare a theorem about an intertwining
linear map with a theorem directly about component families only where this affects
reuse and usability. Explain how each existing theorem would specialize it, matching
every hypothesis. The specializations must not depend on the old proofs they replace.

Provide candidate signatures as uncompiled sketches, clearly labelled. Preserve the
existing complex finite-family setting unless a directly useful relaxation is justified.
Distinguish sufficient assumptions from necessity or minimality; do not claim either
without a mathematical argument. No infinite-dimensional or semisimplicity framework.

### 4. Placement, consumers and boundary

Recommend a suitable existing mathematics home, or justify a small new module. Show
the intended import direction, keeping the general theorem independent of Lorentz and
Standard Model application imports. Identify which wrappers and matrix adapters remain
useful, which duplicated proofs disappear and which public callers need adjustment.

Inspect the two generic quotient/peeling lemmas only to explain their relationship to
lifting and whether they belong nearby. Do not redesign `StandardModel.Peeling.Step`,
prototype peeling, or expand into gauge classifications or boost-weight extraction.

### 5. Post-bump experiment plan

Specify a short ordered list of Lean 4.34.0 probes that would settle the remaining
questions: intended destination imports, both original contracts, dependent and empty
families, actual consumer application shapes, and principal axiom audits. Distinguish
compiling a restated application from compiling its original production consumer.

The inherited `StandardModel.JetAlgebra.SectorEquiv.Basic` failure blocks some SM
consumers at the reference revision. Do not repair or build it; name any validation
obligations it prevents and do not assume its status on another revision.

## Report requirements and completion

Keep the report focused and self-contained. Include:

1. Source provenance and scope actually inspected.
2. Exact contract table and common proof map.
3. Existing library machinery and candidate statement(s).
4. Derivation of both specializations, with unresolved steps explicitly labelled.
5. Placement/consumer map and bounded proposed implementation scope.
6. Post-bump experiments, risks and questions requiring human judgement.

Separate source-verified facts, mathematical deductions and untested Lean proposals.
Do not report timings, builds, axiom audits or successful elaboration: none is run in
this task. Report counterevidence as readily as supporting evidence. A reasoned
recommendation is welcome; do not force a shared design if it is not justified.

Finish in chat with the report path and material findings/uncertainties. Confirm that
only the report was added or changed. Human review, then a post-bump Lean spike, is the
acceptance gate before implementation.
