# Moving QuantumInfo into PhyslibAlpha

A primitives-first plan. All counts are measured on commit `397ac36a` (9 November 2026), with Lean
and Mathlib at v4.35.0.

## Summary

This plan moves `QuantumInfo/` into `PhyslibAlpha/`. Along the way, each primitive (a basic object
the rest of the library is built on) either becomes the single definition of that object or is
rebuilt on a definition that already exists.

QuantumInfo was developed apart from Physlib. Its Hermitian matrices, states, effects, measurements,
channels, qubit gates and operator-monotonicity results now have counterparts in core Physlib,
PhyslibAlpha or Mathlib. Moving 40,000 lines first and reconciling afterwards would carry those
duplicates through every move, so this plan reconciles them first. Below, *core* means the
`Physlib/` library, *Alpha* means `PhyslibAlpha/`, and a *bridge* is a definition or lemma that
connects two existing objects without changing either.

**Scope.** The move into PhyslibAlpha is a preliminary step, and this plan covers only that step. It
does not propose moving any of this code into `Physlib/`; whether and how that happens later is a
separate discussion. Core appears here as a source of definitions to reuse. The plan changes core in
only three small ways, each needed by this work: `ComplexLaplaceTransform` goes to core, because a
core file imports it and core cannot import Alpha; `𝓗[d]` loses an unused `[DecidableEq d]`, so that
`Ket` can build on it; and core's references to QuantumInfo (its Qubit API map and tooling) are
updated.

Two different orders are involved:

- **Files move leaves-first.** `noAlphaImports` forbids `Physlib/` and `QuantumInfo/` from importing
  `PhyslibAlpha/`, so a file can move only after every file that imports it has moved. Moving
  `HermitianMat/Basic.lean` first would break QuantumInfo; moving `SteinsLemma.lean` first breaks
  nothing.
- **Primitives are settled first.** That rule restricts moves only. QuantumInfo may already import
  core, and Alpha may already import QuantumInfo, so most reconciliation can land before any file
  moves.

| Phase | Work | PRs (approx.) |
| --- | --- | --- |
| 0 | Agree the decisions in this document; write the move script | 0 |
| 1 | Make Alpha use core's state framework instead of its own copy | 3 |
| 2 | Add bridges from QuantumInfo's objects to the existing ones | 7 |
| 3 | Replace duplicated primitives inside QuantumInfo | 8 |
| 4 | Clean up in place: style, docstrings, namespaces, renames | 5 |
| 5–10 | Move files, leaves first, then retire the `QuantumInfo` library | 49 |
| 11 | Finish the reconciliation that needs the files to be in Alpha | 5 |

The main findings behind this order:

- **The bridges are small.** Trial versions of the main ones compile against this commit
  (Appendix B). `HermitianMat d ℂ` is definitionally core's `Observable (Matrix d d ℂ)`, and core's
  order-unit structure applies to it through a two-line instance.
- **The largest obstacle is outside QuantumInfo.** Alpha carries its own copy of core's state
  framework, so core states and Alpha measurements cannot yet be used together (Phase 1).
- **QuantumInfo is a general library with Stein's lemma on top.** `SteinsLemma.lean` transitively
  imports 62 of the other 80 files (36.2k of 40.3k lines). Over half of the library (22.5k lines,
  `ForMathlib/`) is matrix analysis with no physics.

D6 gates Phase 1 and D1 gates the `Ket` rebuild in Phase 3. The other decisions are needed before
the phase that uses them.

## Where QuantumInfo stands

QuantumInfo is 81 files and 40,313 lines. It is a default build target; Alpha is not.

| Area | Lines | Content |
| --- | --- | --- |
| `ForMathlib/HermitianMat/` | 8,118 | `HermitianMat`, Loewner order, trace, inner product, CFC, log/exp, rpow, sqrt, projectors, Schatten norms, Lieb concavity, Peierls |
| `ForMathlib/HayataGroup/` | 7,481 | Operator inequalities vendored from Hayata-Yamasaki-Group/lean-quantum: Löwner–Heinz, Jensen operator inequality, generalized perspective, Lieb–Ando; stated on `ℋ →L[ℂ] ℋ`, not matrices |
| `ForMathlib/` (rest) | 6,894 | `Matrix` lemmas, majorization, trace norm, isometries, Sion minimax, lim sup/inf, a `commutes` tactic |
| `Entropy/` | 5,694 | von Neumann, sandwiched Rényi and relative entropy, SSA, DPI |
| `Channels/` | 3,675 | `MatrixMap`, Choi/Kraus, the nine-structure bundled hierarchy up to `CPTPMap`, duals, pinching |
| `States/` | 3,449 | `Ket`/`Bra`, `MState`, qubit gates, Bloch sphere, ensembles, entanglement, fidelity, trace distance |
| `ResourceTheory/` | 3,195 | Free-state theories, optimal hypothesis-testing rate, generalized quantum Stein's lemma |
| `ClassicalInfo/` | 1,206 | `Prob`, `Mixable`, `ProbDistribution`, Shannon entropy, discrete channels |
| `Capacity/`, `Measurements/`, `Operators/` | 601 | Channel capacities, POVMs, unitary conjugation |

The dependency spine is linear: `ForMathlib`, then `HermitianMat`, `Braket`, `MState`, `Channels`,
`Entropy` and `ResourceTheory`. `MState` is the choke point.

QuantumInfo is not isolated from the other libraries. Three connections exist today:

- `Physlib/StatisticalMechanics/MicroCanonicalEnsemble/ThermoQuantities.lean` imports
  `QuantumInfo.ForMathlib.ComplexLaplaceTransform`. That file cannot move to Alpha, because core
  depends on it.
- `PhyslibAlpha/QuantumMechanics/QubitGates.lean` imports `QuantumInfo.States.Pure.Qubit`.
- `States/Mixed/Fidelity.lean` and `ClassicalInfo/Capacity.lean` import
  `Physlib.Meta.Informal.Basic`.

Fifteen files have no importers in any library. Three are unused helpers (`ForMathlib/ULift`,
`ForMathlib/Unitary`, `ForMathlib/Superadditive`), one is pending D3
(`JensenOperatorInequalityIVtoV`), and eleven are finished leaves such as Stein's lemma and SSA.

Debt the Alpha gate will see:

| Check | Count |
| --- | --- |
| Style errors from `lint-style.py` (line length 1,751; `" ;"` 213; indentation 128; other 136) | 2,228 |
| Files over the 1,500-line limit (`Entropy/Relative` 2,450; `LownerHeinzCore` 2,412; `SteinsLemma` 2,123; `ForMathlib/Matrix` 1,596; `Entropy/DPI` 1,595) | 5 |
| Files exempt from linters through `LinterExemption.txt` | 71 of 81 |
| `theorem` declarations | 393 |
| Public definitions with underscores in their names | about 50 (plus 11 private) |
| Definitions and structures without a docstring (estimate) | about 60 of 380 |
| `maxHeartbeats` overrides | 67 |
| Global (unscoped) notations | 11 |

There are no axioms and no `sorry`s in code (six occurrences, all in comments). `docs/QI_DOC.md`
(1,619 lines) has drifted: it cites `traceRight_of_purify`, but the code has `MState.purify_spec`.

## Repository constraints

1. **Import direction.** `noAlphaImports` rejects any `Physlib/` or `QuantumInfo/` file that imports
   `PhyslibAlpha/`. Nothing forbids QuantumInfo from importing core or Alpha from importing
   QuantumInfo, and both already happen.
2. **Unique names across the three libraries.** `auxillary_script_test` imports `Physlib`,
   `QuantumInfo` and `PhyslibAlpha` together and fails on any duplicate declaration. A move is
   collision-free; copy-then-delete across two PRs is not. Each PR moves and deletes in one commit.
3. **The Alpha lint gate has no escape hatch.** `runPhyslibAlphaLinters` runs with an empty nolints
   list, so QuantumInfo's exemption list does not apply. Files must also pass
   `alphaPythonLinters.sh` (100-character lines, no `" ;"`, terminal `simp` only, at most 1,500
   lines per file), `module_doc_lint`, `alphaFileImports`, `theorem_lint` and `pseudo_lint`.
4. **`AGENTS.md` content rules.** `lemma` unless the result is well known in the literature, every
   definition documented, proofs under about 50 lines, results in their most general home.
5. **Alpha placement mirrors core.** One-look review checks that a file sits in the right place
   within Alpha, "mirroring its place in Physlib".
6. **Alpha is not maintained.** When Alpha breaks, the break is recorded and the file commented out
   of `PhyslibAlpha.lean`. Stein's lemma is kept green on every Mathlib bump today; after the move
   that needs a named owner (D5).
7. **AI policy.** A human certifies every line, writes every PR description and answers every
   reviewer. Much of this plan is mechanical and suits agents; the review loop does not.
8. **Hard-coded references.** 31 files outside `QuantumInfo/` name the library, including
   `lakefile.toml`, `Physlib/Meta/Basic.lean`, the CI workflows and most linter scripts. The
   retirement PR must update all of them.

## Primitives

### Principles

- **One concept, one definition.** Where Mathlib or Physlib already defines an object, QuantumInfo's
  version becomes a thin layer over it or is joined to it by a bridge.
- **Reuse in this order:** Mathlib, core, Alpha, then QuantumInfo's own code.
- **Abstract frameworks come from Physlib, concrete finite-dimensional objects from QuantumInfo.**
  `MState` stays the concrete density matrix; core's `𝓢[ℝ, E]` stays the abstract state.
- **Matrices stay the working representation.** The 22.5k lines of matrix analysis are stated on
  matrices, and core's abstract results are generic in the observable space, so they apply to
  matrices directly. One equivalence connects matrices to operators on `𝓗[d]`, which is where
  Alpha's operator-level results live. PR #1578 explores the opposite choice (D1).
- **`HermitianMat` stays a separate `def`.** It carries the Hilbert–Schmidt norm, while `selfAdjoint`
  of a matrix C⋆-algebra carries the operator norm. The `def` keeps the two apart, and conversions
  are `rfl`.

### The state framework exists twice

`UnitalPositiveLinearMap` is declared separately in `Physlib/ProbabilisticTheory/Channel/Basic.lean`
(at the root) and in `PhyslibAlpha/ProbabilisticTheory/Channel/Basic.lean` (inside
`ProbabilisticTheory`). In total, 113 declarations in 13 Alpha modules have a same-named copy in core
that differs only by that namespace (counting generated ones such as recursors). They include
`𝓢[·,·]`, `dist`, `IsPure`, `optimalSuccessProb` and `Observable`.

`OrderUnitSpace` and `Effect` are shared. States are not: Alpha imports its own `State`, `Channel`
and `Weight` files 44 times and core's never. A file that imports both gets an ambiguity error on
`𝓢[·,·]`, so a single bridge file cannot use core states and Alpha measurements together.

Recent PRs (#1789, #1954, #1955, #1958 and draft #1959) have been adding this framework to core, and
#1958 deleted the corresponding Alpha file, so this looks transitional. This plan makes core's types
canonical, since Alpha sits downstream of Physlib (D6).

### Reuse map

*Compiled* means checked in a throwaway Lean file against this commit (Appendix B); none of that code
is in the repository yet. *Read* means compared by reading the definitions only.

| Concept | QuantumInfo | Reuse | Action | Phase | Status |
| --- | --- | --- | --- | --- | --- |
| Hilbert space, kets | `Ket d`, `Bra d` on `d → ℂ` | core `𝓗[d]` | Rebuild on unit vectors of `𝓗[d]`, keeping the `Ket` API as lemmas. First drop `[DecidableEq d]` from `𝓗[d]`: `Ket` does not assume it and only `basisFun` uses it | 3 | Relaxed `𝓗[d]` compiled. `Ket` rebuild not attempted (36 uses of `.vec`, 21 of `normalized'`) |
| Operators | `Matrix d d ℂ` | Mathlib `toEuclideanCLM`, `conjStarAlgEquiv` | Add `Matrix d d ℂ ≃⋆ₐ[ℂ] (𝓗[d] →L[ℂ] 𝓗[d])`, the one connection to `ofVec`, `ofDensity`, `traceₚ` and `TraceClass` | 2 | Compiled |
| Observables | `HermitianMat d ℂ` | core `Observable (Matrix d d ℂ)`, `selfAdjoint.instArchimedeanOrderUnitSpace` | Same type by `rfl`. Add the two-line order-unit instance | 2 | Compiled; order, group and module agree by `rfl` |
| States | `MState d` | core `𝓢[ℝ, HermitianMat d ℂ]` | Add `MState.toState`, built from `exp_val` | 2 | Compiled; core's `dist` and Helstrom bound apply |
| Distance, discrimination | `TrDistance` | core `dist`, `optimalSuccessProb` | Prove `dist = 2 * TrDistance` on `MState`, so the Helstrom bound transfers | 2 | Lemma not yet proved |
| Effects | `{m // 0 ≤ m ∧ m ≤ 1}` in `OptimalHypothesisRate` | core `Effect (HermitianMat d ℂ)` | Bridge | 2 | Read |
| Measurements | `POVM X d` | Alpha `Measurement.ofAtoms` | Add `POVM.toMeasurement`; keep `POVM.measure` and `measurementMap`. Resolve the name clash with Alpha's `ProbabilisticTheory.POVM` | 2 | Compiled |
| Positive maps | `PUMap`, `CPUMap`, `CPTPMap.dual` | core `→ₚ₁[ℝ]`, `restrictObservables`; Alpha `QuantumChannel` | Bridges | 2 | `QuantumChannel` accepts plain `Matrix`, with no `CStarMatrix`; bridges not written |
| Trace norm | `Matrix.traceNorm` | Alpha `TraceClass.traceNorm` | Bridge through the matrix–operator equivalence | 2 | Read |
| Classical objects | `ProbDistribution`, `DMChannel`, `Hₛ` | Alpha `FiniteClassicalSystem.stateEquiv`, `Classical/Channel`; core `CanonicalEnsemble.shannonEntropy` | Bridges | 2 | Read |
| Operator monotonicity | `log_mono`, `log_concave`, `rpow_le_rpow_of_posDef`, `rpow_le_rpow_of_le` | Mathlib `CFC.log_le_log`, `CFC.concaveOn_log`, `CFC.rpow_le_rpow` | Replace the hand-written proofs and keep the statements, over `ℂ` (their only use) | 3 | Compiled. Removes up to about 650 lines of `LogExp` and `Rpow` |
| Qubit gates | `X`, `Y`, `Z` | core `pauliMatrix` | Define from `pauliMatrix`. Alpha's `ry` and `multiplex` join them at the move | 3 | Compiled; equal by `rfl` |
| Product kets | `Ket.prod`, `Ket.piProd` | Alpha `prodVec`, `piProdVec` | Define through Alpha's products once `Braket` is in Alpha. `piProdVec` must first be generalized to dependent families | 11 | Read |
| Kraus, Stinespring | `Channels/CPTP.lean` | Alpha `QuantumMechanics/StinespringDilation.lean` and `ProbabilisticTheory/CStarAlgebra/Stinespring/` | One API: the general C⋆ theorem, with the finite-dimensional forms as special cases | 11 | Read |
| Density matrices, partial trace | `MState`, `traceLeft`, `traceRight` | Replaces Alpha's `densityMatrix`, `tr₂` | Retire Alpha's versions in favour of QuantumInfo's | 11 | Read |
| Convex combinations | `Mixable` | Mathlib `Convexity.ConvexSpace`; core `State.mix`, `Effect.mix` | Decision D2 | 11 | Not tested |
| Probabilities | `Prob` | Mathlib `unitInterval` | Done in #2041. Whether to retire the name is D2 | n/a | Merged |

### What stays as it is

- **The vendored operator-inequality block.** It already calls Mathlib where Mathlib applies, and
  Mathlib still lists operator convexity of `rpow` as a TODO, so it cannot be replaced yet (D3).
- **Sion minimax, majorization, Choi matrices, the quantum entropies and the resource theory.** A
  search of Mathlib, core and Alpha found no counterparts, so these simply move.

## Target layout

The code splits into five layers, each importing only the layers below it and the Physlib code
beside it. A result lives in its most general home: a matrix fact in `Mathematics`, a fact about any
finite quantum system in `QuantumMechanics`, and only information-theoretic content in
`QuantumInformation`. Paths below are relative to `PhyslibAlpha/`.

1. **Mathematics**, in `Mathematics/`. No physics.
   - `Matrix/`: `ForMathlib/Matrix.lean` split by topic, plus `Isometry`, `TraceNorm`, `Majorization`.
   - `Matrix/HermitianMat/`: `HermitianMat n 𝕜`, its order, trace, Hilbert–Schmidt inner product,
     CFC, `log`/`exp`/`rpow`/`sqrt`, projectors, Schatten norms, Lieb concavity, Peierls. The
     `commutes` tactic moves with it (its only client).
   - `OperatorInequality/`: the vendored block on `ℋ →L[ℂ] ℋ`, with `LownerHeinzCore` split below
     1,500 lines.
   - `Convex/Minimax/`, `Order/LimSupInf`, `Analysis/ContinuousSup`, `SpecialFunctions/NegMulLog`.
2. **Classical information**, in `QuantumInformation/Classical/`: `Prob`, `ProbDistribution`,
   `Mixable`, Shannon entropy, discrete memoryless channels, classical capacity.
3. **Finite quantum systems**, in `QuantumMechanics/HilbertSpaces/FiniteTarget/` and
   `QuantumMechanics/Qubit/`, next to `𝓗[d]`, `prodVec` and core's Qubit API map.
   - `Ket.lean`, `Ket/Product.lean`: kets, bras, products, entanglement, maximally entangled state,
     global phase.
   - `MState/`: `Basic`, `Product`, `PartialTrace`, `Purification`, with unitary conjugation folded
     in.
   - `Operators.lean` (already in Alpha) gains the matrix–operator equivalence.
   - `Qubit/`: gates, controlled gates, Bloch sphere, absorbing `QubitGates.lean`.
4. **Channels and states as resources**, in `QuantumInformation/`: `Channels/` (`MatrixMap`,
   `Properties`, `Bundled`, `CPTP/`, `Dual`, `Pinching`, `DegradableOrder`), `States/` (`Ensemble`,
   `Entanglement`, `Fidelity`, `TraceDistance`) and `Measurement/POVM`.
5. **Information measures and operational results**, in `QuantumInformation/`: `Entropy/`
   (`VonNeumann`, `Relative/`, `SSA`, `DPI/`), `HypothesisTesting/`, `ResourceTheory/` (`FreeState`,
   `SteinsLemma/`) and `Capacity/`.

Bridges to Physlib go in `ProbabilisticTheory/Examples/HermitianMatrices.lean`, beside the existing
`Examples/Qubit.lean`. Each directory with a coherent API gets an `API-map.md` (per
`docs/API_MAP_GUIDE.md`): `QuantumInformation/`, `QuantumInformation/Channels/`,
`QuantumInformation/Entropy/` and `Mathematics/Matrix/HermitianMat/`. Together they replace
`docs/QI_DOC.md`.

## Naming and namespaces

Identifiers keep their short names and gain a namespace, so proof churn is confined to `namespace`
and `open` lines. All of this happens in Phase 4, inside QuantumInfo, so that later moves are pure
renames of paths.

- **Namespaces.** Layer 1 keeps Mathlib namespaces (`Matrix`, `HermitianMat`,
  `ContinuousLinearMap`), and the vendored files keep theirs. Layer 3 joins `QuantumMechanics`.
  Layers 2, 4 and 5 go under `QuantumInformation`. Today `Ket`, `Bra`, `MState`, `Prob`, `Mixable`,
  `Channel`, `POVM`, `Ensemble`, `TrDistance`, `Sᵥₙ` and `qRelativeEnt` all live at the root.
- **Forced renames.** Definitions with underscores become lowerCamelCase, with dependent lemma names
  following Mathlib convention: `choi_matrix` to `choiMatrix`, `of_choi_matrix` to `ofChoiMatrix`,
  `of_kraus` to `ofKraus`, `CPTP_of_choi_PSD_Tr` to `CPTPMap.ofChoiPSD`, `Ket.to_bra` to `Ket.toBra`,
  `uniform_superposition` to `Ket.uniformSuperposition`, `pinching_map` to `pinchingMap`,
  `convex_roof` to `convexRoof`. Proof-internal definitions in `SteinsLemma` (`σ₁_mineig`, `σ₁_c`)
  become `private` or local.
- **Notation.** The 11 global notations become scoped: `𝐔[n]`, `∘ₘ`, `⊗ᶜᵖ`, `D̃_α(ρ‖σ)`, `𝐃(ρ‖σ)`,
  `Q̃_α(ρ‖σ)`, `⊗ᵠ`, `⊗ᴹ`, `⊗ᴹ^`, and the two `p [x ↔ y]` mixing notations, which are the most
  likely to clash with Physlib syntax.
- **`theorem` versus `lemma`.** Of the 393 `theorem`s, keep the keyword only for literature results
  and list them under `[PhyslibAlpha]` in `Theorems.txt`, each with a docstring. Candidates:
  `choi_PSD_iff_CP_map`, `MState.purify_spec`, `Sᵥₙ_strong_subadditivity`, `Sᵥₙ_subadditivity`,
  `sandwichedRenyiEntropy_DPI`, `qRelativeEnt_joint_convexity`, `HermitianMat.log_mono`,
  `HermitianMat.log_concave`, `sion_minimax`, `GeneralizedQSteinsLemma`,
  `limit_hypotesting_eq_limit_rel_entropy`, plus the Löwner–Heinz and Lieb–Ando statements.
- **No deprecation aliases.** Physlib has none today. Downstream users get a generated old-name to
  new-name map with the retirement PR.

## Phases

Every PR must leave `lake build Physlib QuantumInfo PhyslibAlpha`, `lint_all`,
`runPhyslibAlphaLinters`, `alphaPythonLinters.sh`, `theorem_lint` and `auxillary_script_test` green.
Phases 1, 2, 3 and 11 are design work and are where reviewer attention should go. Phases 4 to 10 are
mechanical and suit agent-assisted work, with review latency as the main cost.

**Phase 0: agreement and tooling (no code).** Settle the decisions below with the maintainers and
QuantumInfo's main contributors, including that moved files are judged on the linters and file
limits, with proof splitting as follow-up. Write a move script: `git mv`, import rewrite, entries in
`PhyslibAlpha.lean` and `QuantumInfo.lean`, `Theorems.txt` section moves, `LinterExemption.txt`
removals.

**Phase 1: one state framework (about 3 PRs).** Point Alpha at core's `UnitalPositiveLinearMap`,
`𝓢[·,·]`, `dist`, `Observable`, `Weight` and related declarations, and delete the duplicates. This
adds nothing to core. Alpha-only additions, such as `ProbabilisticTheory.Channel`, stay in Alpha on
top of core. Extensions
declared under `ProbabilisticTheory.UnitalPositiveLinearMap`, such as `ofDensity`, move to the root
namespace so that dot notation keeps working; 32 Alpha files open that namespace. Coordinate with the
ongoing work adding this framework to core. If this phase slips, Phase 2 can still proceed, because
the bridges to core states and to Alpha measurements compile in separate files (Appendix B).

**Phase 2: bridges (about 7 PRs, additive).** All new code lives in Alpha and imports QuantumInfo
and core. No existing definition changes. `QubitGates.lean` is the precedent for this import.

1. The equivalence `Matrix d d ℂ ≃⋆ₐ[ℂ] (𝓗[d] →L[ℂ] 𝓗[d])`, in `FiniteTarget/Operators.lean`.
2. `ArchimedeanOrderUnitSpace (HermitianMat d ℂ)` and `MState.toState`, in
   `Examples/HermitianMatrices.lean`.
3. `dist = 2 * TrDistance` on `MState`, with the Helstrom bound for `MState` as a corollary.
4. `POVM.toMeasurement` and the effect form of the hypothesis-testing test set.
5. `PUMap` and `CPUMap` to `→ₚ₁[ℝ]`, and `CPTPMap.dual` to `QuantumChannel`.
6. `Matrix.traceNorm` with `TraceClass.traceNorm`.
7. `ProbDistribution` with `𝓢[ℝ, FiniteClassicalSystem _]`, `DMChannel` with `Classical/Channel`,
   and `CanonicalEnsemble.shannonEntropy` with `Hₛ`.

**Phase 3: replace primitives in place (about 8 PRs).** These build on Mathlib or core, which
QuantumInfo can already import.

1. Delete the three unused helpers and move `ComplexLaplaceTransform` into core (the one file that
   cannot go to Alpha; see Scope).
2. Replace the hand-written proofs of operator monotonicity with Mathlib's (2 PRs: log, rpow).
3. Drop `[DecidableEq d]` from the type `𝓗[d]` in core.
4. Rebuild `Ket` and `Bra` on `𝓗[d]`, restating the old API as lemmas so most proofs survive (2 or
   3 PRs, after D1).
5. Define `X`, `Y`, `Z` from `pauliMatrix`, updating core's Qubit API map in the same PR, since
   `api_map_lint` checks it.

**Phase 4: clean up in place (about 5 PRs).** Fix the 2,228 style errors, scope the 11 global
notations, add the missing docstrings, and apply the namespaces and renames above. Update
`QubitGates.lean` and core's Qubit API map where those names change. After this phase a move PR is
close to a pure path change that git and reviewers recognize as a rename.

**Phases 5–10: moves (48 PRs and the retirement PR).** Each row of Appendix A is one PR. A file may
move once every file importing it has moved, and the appendix order satisfies that rule (checked by
script against the import graph).

- **Phase 5, leaves (10 PRs):** Stein's lemma, split in three, SSA, capacity, `DegradableOrder`,
  entanglement, trace distance, qubit files, Bargmann invariant, classical capacity and channels.
- **Phase 6, operational layer (7 PRs):** hypothesis testing, free states, pinching, DPI, POVM,
  fidelity, `ContinuousSup`.
- **Phase 7, entropy core (5 PRs):** relative entropy, von Neumann entropy, ensembles, lim sup/inf,
  Sion minimax.
- **Phase 8, channels (6 PRs):** duals, CPTP, bundled and unbundled maps, `MatrixMap`, unitary
  conjugation.
- **Phase 9, states and classical primitives (6 PRs):** `MState`, `Braket`, exchange relations,
  Shannon entropy, distributions, `Prob`.
- **Phase 10, mathematics and retirement (14 PRs, then 1):** `HermitianMat`, the vendored block,
  trace norm, majorization, matrix lemmas, small helpers. The final PR removes the `QuantumInfo`
  library and every hard-coded reference to it, and publishes the rename map.

**Phase 11: what needs the files in Alpha (about 5 PRs).** QuantumInfo cannot import Alpha, so these
wait until the files have moved: define `Ket.prod` and `Ket.piProd` through `prodVec` and
`piProdVec`; unify the Kraus and Stinespring APIs; retire `densityMatrix` and `tr₂`; apply the D2
outcomes; add the four API maps and delete `docs/QI_DOC.md`.

## Decisions needed

| | Question | Options | Recommendation | Needed before |
| --- | --- | --- | --- | --- |
| D1 | What happens to PR #1578? It restates density matrices, kets and channels on Hermitian operators, adds `StdBasis`, `HermitianOp`, `DensityOp`, `PartialTrace` and `OpMap`, and touches 58 of the 81 files (last commit 24 August 2026, on Lean v4.33). | (a) Land it first, then move. (b) Park it, move `master`, and re-land its additive files in Alpha, with `MState d` as an abbreviation of `DensityOp`. (c) Rebase it onto the moved tree. | (b), unless its author commits to landing it within a window fixed in Phase 0. The operator layer should then target `𝓗[d]` and use the equivalence from Phase 2. (c) is the worst case: every path and namespace changes under it. | Phase 3 |
| D2 | Keep `Prob`, `Mixable` and `ProbDistribution`, or switch to Mathlib's `unitInterval`, `Convexity.ConvexSpace` and `stdSimplex`/`PMF`? | Keep; replace; keep with equivalences. | `Prob` is already an alias of `unitInterval` (#2041); keep the name during the move. In Phase 11, evaluate `ConvexSpace` against the joint-convexity and ensemble statements. | Phase 11 |
| D3 | Vendored operator-inequality block: keep or dissolve into `HermitianMat`? | Keep as a block; dissolve. | Keep, under `Mathematics/OperatorInequality/`, with attribution in headers and module docs, as for Alpha's vendored `Mathematics/TauCeti/`. The upstream licence is Apache-2.0. | Phase 5 |
| D4 | Finite-dimensional states under `QuantumMechanics/HilbertSpaces/FiniteTarget/` or under `QuantumInformation/`? | Split as above; all in `QuantumInformation/`. | Split. It matches the TODO in `FiniteTarget/Basic.lean` and core's Qubit API map. Confirm with the TODO's author. | Phase 4 |
| D5 | Who keeps Stein's lemma building once it leaves a default build target? | Accept Alpha policy; name an owner for Mathlib bumps. | Name an owner. | Phase 5 |
| D6 | Which state framework is canonical? | Core's; Alpha's. | Core's, because Alpha sits downstream of Physlib. Agree who carries out Phase 1 with the author of the recent core PRs. | Phase 1 |
| D7 | Is a new top-level `QuantumInformation/` acceptable in Alpha, given that core has no such directory and Alpha placement mirrors core? | (a) Add it. (b) Place everything under `QuantumMechanics/`. | (a). The project scope in the README includes quantum information, and a separate area keeps information-theoretic results apart from general quantum mechanics. | Phase 4 |

## Risks

| Risk | Mitigation |
| --- | --- |
| Phase 1 depends on work others are doing in the same files | D6 settles ownership first; Phase 2 can proceed without it, in separate files |
| A bridge exposes a real mismatch between two definitions | Bridges land first, before any file moves, so a mismatch changes the plan rather than undoing moves |
| Rebuilding `Ket` touches a definition that every state file depends on | Restate the old API as lemmas so most proofs survive; wait for D1 |
| Stein's lemma loses CI protection in Alpha and gets commented out after a Mathlib bump | D5: a named owner; track the 67 `maxHeartbeats` overrides, since bumps break there first |
| Collision with in-flight QuantumInfo PRs: #1578 (58 files), #1073 (12), #1098 (10), #2008 (3), #1139 (1) | Announce a freeze per directory one phase ahead; land or rebase open PRs before their files move |
| One-look reviewers apply the 50-line proof guideline to `SteinsLemma`, `Entropy/Relative`, `Entropy/DPI` and `LownerHeinzCore` | Agree in Phase 0 that moves are judged on the linters and file limits; track proof splitting per file |
| Move PRs are too large to review | Phase 4 removes style noise and renames first; one file or one tight cluster per PR |
| Renames break downstream code | Generated rename map in the retirement PR; downstream bumps once, after Phase 10 |
| A bridge or reconciliation reintroduces a duplicate name | `auxillary_script_test` catches it; such PRs delete the duplicate in the same commit |
| Alpha's build cost grows by 40k lines of heavy matrix analysis | Measure Alpha's build time after Phase 10 |

## Appendix A: file mapping

All 81 files, in order, one row per PR. A script check against the import graph found no row that
moves a file before all of its importers. Sources are relative to `QuantumInfo/`, and `…/` abbreviates
the directory of the preceding entry or, for the vendored block, `ForMathlib/HayataGroup/TraceInequality/`.
Targets are relative to `PhyslibAlpha/` unless a full path is given.

| # | Phase | QuantumInfo source | Lines | Target |
| --- | --- | --- | --- | --- |
| 1 | 3 | `ForMathlib/ULift`, `ForMathlib/Unitary`, `ForMathlib/Superadditive` | 226 | delete (no importers) |
| 2 | 3 | `ForMathlib/ComplexLaplaceTransform` | 329 | `Physlib/Mathematics/ForMathlib/ComplexLaplaceTransform` (core: imported by `ThermoQuantities`) |
| 3 | 5 | `ResourceTheory/SteinsLemma` | 2,123 | `QuantumInformation/ResourceTheory/SteinsLemma/{Lemma6, Lemma7, Basic}` |
| 4 | 5 | `Entropy/SSA` | 1,306 | `QuantumInformation/Entropy/SSA` |
| 5 | 5 | `Capacity/Capacity`, `Capacity/Capacity_doc` | 325 | `QuantumInformation/Capacity/Basic` |
| 6 | 5 | `Channels/DegradableOrder` | 60 | `QuantumInformation/Channels/DegradableOrder` |
| 7 | 5 | `States/Entanglement` | 336 | `QuantumInformation/States/Entanglement` |
| 8 | 5 | `States/Mixed/TraceDistance` | 56 | `QuantumInformation/States/TraceDistance` |
| 9 | 5 | `States/Pure/Qubit`, `States/Pure/BlochSphere` | 384 | `QuantumMechanics/Qubit/{Gates, BlochSphere}`, absorbing Alpha's `QubitGates.lean` |
| 10 | 5 | `States/Pure/BargmannInvariant` | 120 | `QuantumMechanics/HilbertSpaces/FiniteTarget/BargmannInvariant` |
| 11 | 5 | `ClassicalInfo/Capacity`, `ClassicalInfo/Channel` | 135 | `QuantumInformation/Classical/{Capacity, Channel}` |
| 12 | 5 | `…/JensenOperatorInequalityIVtoV` | 289 | `Mathematics/OperatorInequality/JensenOperatorInequalityIVtoV`, or delete (D3) |
| 13 | 6 | `ResourceTheory/HypothesisTesting` | 571 | `QuantumInformation/HypothesisTesting/Basic` |
| 14 | 6 | `ResourceTheory/FreeState` | 501 | `QuantumInformation/ResourceTheory/FreeState` |
| 15 | 6 | `Channels/Pinching` | 415 | `QuantumInformation/Channels/Pinching` |
| 16 | 6 | `Entropy/DPI` | 1,595 | `QuantumInformation/Entropy/DPI/{Basic, JointConvexity}` |
| 17 | 6 | `Measurements/POVM` | 191 | `QuantumInformation/Measurement/POVM` |
| 18 | 6 | `States/Mixed/Fidelity` | 140 | `QuantumInformation/States/Fidelity` |
| 19 | 6 | `ForMathlib/ContinuousSup` | 264 | `Mathematics/Analysis/ContinuousSup` |
| 20 | 7 | `Entropy/Relative` | 2,450 | `QuantumInformation/Entropy/Relative/{SandwichedRenyi, LimitAtOne, Basic}` |
| 21 | 7 | `Entropy/VonNeumann` | 343 | `QuantumInformation/Entropy/VonNeumann` |
| 22 | 7 | `States/Ensemble` | 412 | `QuantumInformation/States/Ensemble` |
| 23 | 7 | `ForMathlib/LimSupInf`, `ForMathlib/Filter` | 599 | `Mathematics/Order/LimSupInf` |
| 24 | 7 | `ForMathlib/Minimax`, `ForMathlib/SionMinimax` | 918 | `Mathematics/Convex/Minimax/{Basic, Sion}` |
| 25 | 8 | `Channels/Dual` | 508 | `QuantumInformation/Channels/Dual` |
| 26 | 8 | `Channels/CPTP` | 835 | `QuantumInformation/Channels/CPTP/{Basic, Stinespring}` |
| 27 | 8 | `Channels/Bundled` | 478 | `QuantumInformation/Channels/Bundled` |
| 28 | 8 | `Channels/Unbundled` | 926 | `QuantumInformation/Channels/Properties` |
| 29 | 8 | `Channels/MatrixMap` | 453 | `QuantumInformation/Channels/MatrixMap` |
| 30 | 8 | `Operators/Unitary` | 85 | `QuantumMechanics/HilbertSpaces/FiniteTarget/MState/Basic` (merged) |
| 31 | 9 | `States/Mixed/MState` | 1,408 | `QuantumMechanics/HilbertSpaces/FiniteTarget/MState/{Basic, Product, PartialTrace, Purification}` |
| 32 | 9 | `States/Pure/Braket` | 593 | `QuantumMechanics/HilbertSpaces/FiniteTarget/{Ket, Ket/Product}` |
| 33 | 9 | `ForMathlib/ExchangeRelations` | 165 | `Mathematics/ForMathlib/ExchangeRelations` |
| 34 | 9 | `ClassicalInfo/Entropy`, `ClassicalInfo/ForMathlib/…/NegMulLog` | 188 | `QuantumInformation/Classical/Entropy`, `Mathematics/SpecialFunctions/NegMulLog` |
| 35 | 9 | `ClassicalInfo/Distribution` | 328 | `QuantumInformation/Classical/Distribution` |
| 36 | 9 | `ClassicalInfo/Prob` | 555 | `QuantumInformation/Classical/Prob` |
| 37 | 10 | `ForMathlib/HermitianMat`, `ForMathlib/HermitianMat/LiebConcavity` | 552 | `Mathematics/Matrix/HermitianMat/LiebConcavity` (umbrella retired) |
| 38 | 10 | `…/LiebAndoTrace`, `…/OperatorGeometricMean`, `…/HilbertSchmidtOperatorSpace` | 2,234 | `Mathematics/OperatorInequality/{LiebAndoTrace, OperatorGeometricMean, HilbertSchmidtOperatorSpace}` |
| 39 | 10 | `…/GeneralizedPerspectiveFunction`, `…/JensenOperatorInequality`, `…/JensenOperatorInequalityIImpIV`, `…/BlockDiagonal` | 2,267 | `Mathematics/OperatorInequality/{GeneralizedPerspectiveFunction, JensenOperatorInequality, JensenOperatorInequalityIImpIV, BlockDiagonal}` |
| 40 | 10 | `…/LownerHeinzTheorem`, `…/LownerHeinzCore` | 2,691 | `Mathematics/OperatorInequality/LownerHeinz/{Basic, Core}` (Core split) |
| 41 | 10 | `ForMathlib/HermitianMat/Schatten`, `…/Rpow`, `…/Peierls` | 1,884 | `Mathematics/Matrix/HermitianMat/{Schatten, Rpow, Peierls}` |
| 42 | 10 | `ForMathlib/MatrixNorm/TraceNorm` | 493 | `Mathematics/Matrix/TraceNorm` |
| 43 | 10 | `ForMathlib/HermitianMat/Sqrt`, `…/LogExp`, `…/Proj` | 1,348 | `Mathematics/Matrix/HermitianMat/{Sqrt, LogExp, Proj}` |
| 44 | 10 | `ForMathlib/HermitianMat/CFC` | 1,438 | `Mathematics/Matrix/HermitianMat/CFC` |
| 45 | 10 | `ForMathlib/HermitianMat/Unitary`, `…/Jordan`, `…/NonSingular`, `…/Inner`, `…/CompoundMatrix` | 1,055 | `Mathematics/Matrix/HermitianMat/{Unitary, Jordan, NonSingular, Inner, CompoundMatrix}` |
| 46 | 10 | `ForMathlib/HermitianMat/Order`, `…/Trace`, `…/Reindex`, `…/Basic`, `ForMathlib/IsMaximalSelfAdjoint` | 1,905 | `Mathematics/Matrix/HermitianMat/{Order, Trace, Reindex, Basic, IsMaximalSelfAdjoint}` |
| 47 | 10 | `ForMathlib/Tactic/Commutes`, `…/Commutes/Attribute` | 201 | `Mathematics/Matrix/HermitianMat/Tactic/Commutes` |
| 48 | 10 | `ForMathlib/Majorization`, `ForMathlib/Isometry` | 1,655 | `Mathematics/Matrix/{Majorization, Isometry}` |
| 49 | 10 | `ForMathlib/Matrix` | 1,596 | `Mathematics/Matrix/{Hermitian, PosSemidef, Order, Kronecker, PartialTrace}` |
| 50 | 10 | `ForMathlib/Misc`, `ForMathlib/LinearEquiv`, `ForMathlib/ContinuousLinearMap` | 384 | `Mathematics/ForMathlib/{Misc, LinearEquiv, ContinuousLinearMap}` |

## Appendix B: compile checks

These blocks compile with `lake env lean` against commit `397ac36a`. They are feasibility checks, not
proposed code: names, namespaces and docstrings are still to be decided. They are two separate files
because of the duplicated state framework described above.

Dropping `[DecidableEq d]` was checked separately, on a copy of
`Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/Basic.lean`: only `basisFun` and
`basisFun_apply` need it.

Core only:

```lean
import QuantumInfo.States.Mixed.MState
import QuantumInfo.States.Pure.Qubit
import Physlib.ProbabilisticTheory.CStarAlgebra.OrderUnit
import Physlib.ProbabilisticTheory.StarAlgebra.State
import Physlib.ProbabilisticTheory.State.Discrimination
import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
import Physlib.Relativity.PauliMatrices.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder QuantumMechanics
open ProbabilisticTheory

variable {d : Type*} [Fintype d] [DecidableEq d]

-- `HermitianMat` and core's `Observable` are the same type.
example : HermitianMat d ℂ = Observable (Matrix d d ℂ) := rfl

-- Core's order-unit structure applies, and agrees with what `HermitianMat` already carries.
noncomputable instance instAOUS : ArchimedeanOrderUnitSpace (HermitianMat d ℂ) :=
  inferInstanceAs (ArchimedeanOrderUnitSpace (selfAdjoint (Matrix d d ℂ)))

example : (instAOUS (d := d)).toOrderedVectorSpace.toPartialOrder =
    (inferInstance : PartialOrder (HermitianMat d ℂ)) := rfl
example : (instAOUS (d := d)).toOrderedVectorSpace.toAddCommGroup =
    (inferInstance : AddCommGroup (HermitianMat d ℂ)) := rfl
example : (instAOUS (d := d)).toOrderedVectorSpace.toModule =
    (inferInstance : Module ℝ (HermitianMat d ℂ)) := rfl

-- An `MState` is a core state, so core's distance and Helstrom bound apply to it.
noncomputable def toState (ρ : MState d) : 𝓢[ℝ, HermitianMat d ℂ] :=
  UnitalPositiveLinearMap.ofLinearMap
    { toFun := ρ.exp_val
      map_add' := ρ.exp_val_add
      map_smul' := fun r A => ρ.exp_val_smul r A }
    (fun _ h => ρ.exp_val_nonneg h) ρ.exp_val_one

noncomputable example (ρ σ : MState d) : ℝ :=
  UnitalPositiveLinearMap.dist (toState ρ) (toState σ)

example (ρ σ : MState d) :=
  UnitalPositiveLinearMap.optimalSuccessProb_half_half_eq (toState ρ) (toState σ)

-- The equivalence between matrices and operators on `𝓗[d]`.
noncomputable def matToOp : Matrix d d ℂ ≃⋆ₐ[ℂ] (𝓗[d] →L[ℂ] 𝓗[d]) :=
  (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).trans
    QuantumMechanics.FiniteHilbertSpace.isometryEquivEuclidean.symm.conjStarAlgEquiv

-- Mathlib gives the operator-monotonicity results directly.
example {A B : HermitianMat d ℂ} (hA : A.mat.PosDef) (hAB : A ≤ B) : A.log ≤ B.log :=
  CFC.log_le_log (a := A.mat) (b := B.mat) hAB hA.isStrictlyPositive

example {x y : HermitianMat d ℂ} (hx : x.mat.PosDef) (hy : y.mat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x.log + b • y.log ≤ (a • x + b • y).log :=
  (CFC.concaveOn_log (A := Matrix d d ℂ)).2 hx.isStrictlyPositive hy.isStrictlyPositive ha hb hab

lemma mat_rpow {X : HermitianMat d ℂ} (hX : 0 ≤ X) (q : ℝ) : (X ^ q).mat = X.mat ^ q := by
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.mat_cfc, CFC.rpow_eq_cfc_real (a := X.mat) hX]

example {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hAB : A ≤ B) {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) : A ^ q ≤ B ^ q := by
  show (A ^ q).mat ≤ (B ^ q).mat
  rw [mat_rpow hA, mat_rpow (hA.trans hAB)]
  exact CFC.rpow_le_rpow ⟨hq.le, hq1⟩ hAB

-- The qubit gates are core's Pauli matrices.
example : (Qubit.X : Matrix Qubit Qubit ℂ) = PauliMatrix.pauliMatrix (Sum.inr 0) := rfl
example : (Qubit.Y : Matrix Qubit Qubit ℂ) = PauliMatrix.pauliMatrix (Sum.inr 1) := rfl
example : (Qubit.Z : Matrix Qubit Qubit ℂ) = PauliMatrix.pauliMatrix (Sum.inr 2) := rfl
```

Alpha:

```lean
import QuantumInfo.Measurements.POVM
import Physlib.ProbabilisticTheory.CStarAlgebra.OrderUnit
import PhyslibAlpha.ProbabilisticTheory.Measurement.Finite
import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.QuantumChannel
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open ProbabilisticTheory

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable instance instAOUS : ArchimedeanOrderUnitSpace (HermitianMat d ℂ) :=
  inferInstanceAs (ArchimedeanOrderUnitSpace (selfAdjoint (Matrix d d ℂ)))

-- A `POVM` is an Alpha `Measurement`.
noncomputable def povmToMeasurement {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (Λ : _root_.POVM X d) : Measurement X (HermitianMat d ℂ) :=
  Measurement.ofAtoms (fun x => ⟨Λ.mats x, Λ.nonneg x, by
    rw [← Λ.normalized]
    exact Finset.single_le_sum (f := Λ.mats) (fun y _ => Λ.nonneg y) (Finset.mem_univ x)⟩)
    Λ.normalized

-- Alpha's channel type accepts plain matrices.
example : Type _ := QuantumChannel (Matrix d d ℂ) (Matrix d d ℂ)
```
