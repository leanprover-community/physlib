# The spectral theorem and W⋆-algebras: a roadmap

This is the design document for bringing unbounded-operator theory and W⋆-algebras into `Basic/`,
adapted from the much larger `Unbounded/` tree at
`physlib-dev/unbounded-alpha-public/PhyslibAlpha/QuantumMechanics/Unbounded` (144 files, ~54,800
lines, same author, same Lean toolchain and Mathlib pin as this repo — so no API-drift risk, but a
real *language*-drift risk: that tree predates `Basic/`'s level system and is built on its own
copy of the old `OperatorAlgebra` class, the same scaffolding the `OperatorAlgebra/` salvage this
session replaced). Recorded here as the reference for that adaptation work; see the bottom for
status.

## The one rule that matters

**Adapt, don't copy.** The `Unbounded/` tree has its own `class OperatorAlgebra (A : Type*) extends
CStarAlgebra A, PartialOrder A, StarOrderedRing A` and its own `Observable`/`PositiveElement`/
`Effect` abbrevs (`OperatorAlgebra/Basic.lean`) — a near-exact duplicate of the class this session
already deleted from the *old* `OperatorAlgebra/` tree in favor of `Basic/`'s bare per-file
typeclasses. Every ported file must have that class stripped and replaced with:

- `Basic/StarAlgebra/Observable.lean`'s `Observable A`/`PositiveObservable A`, not a locally
  redeclared equivalent;
- `Basic/OrderUnit/State/Basic.lean`'s `𝓢[A]`, not a locally redeclared `State A`;
- `Basic/OrderUnit/Effect/Basic.lean`'s `Effect A`;
- the genuine minimal hypotheses for each file, worked out fresh the way every salvage agent this
  session was told to (many `Unbounded/` files already only touch a concrete Hilbert space `H`
  directly, not the abstract `OperatorAlgebra A` bundle at all — those need no adaptation on this
  front, just a level check).

Where `Basic/` already has a concept the source file reinvents (GNS, Jordan, Restrict, Trace,
SelfAdjoint, Symmetry, the trace-class `Effect`/`EffectValuedMeasure` machinery) — reuse it, don't
re-derive it. Where the ported content is genuinely new, give it a clean home in the level
hierarchy following the existing "concept-subfolder within a level, once ≥2 files" convention —
not a flat copy of the source tree's own folder names.

## A free foundation already in this repo

`Unbounded/`'s `OperatorAlgebra/Core/` and `Operators/Core/` sit on top of a base layer of
unbounded-operator theory (`LinearPMap`-based symmetric/self-adjoint operators) that lives in the
separate `Physlib` package — and **that package is already vendored in this repo**
(`Physlib/QuantumMechanics/Operators/{Unbounded.lean, SpectralTheory/{Basic,SelfAdjoint,Symmetric,
SpectralMeasure}.lean}`, ~2380 lines), the same package `HilbertSpace/Dynamics/{Automorphism,
Hamiltonian}.lean` already depend on (`OneParameterSubgroups.Unitary`). So the truly foundational
unbounded-operator vocabulary — is this a symmetric operator, an essentially-self-adjoint one, what
is its adjoint — needs no porting at all. What's actually new in `Unbounded/` is the *heavy*
content built on top: the spectral theorem's existence proof, Stone's theorem, W⋆-algebra preduals.

## Where things land

Two new levels, following the existing `OrderUnit → StarAlgebra → CStarAlgebra → HilbertSpace`
spine:

- **`HilbertSpace/Unbounded/`** — a new subfolder of `HilbertSpace/` (alongside `Dynamics/`,
  `State/`), for content genuinely about densely-defined unbounded operators on a *specific*
  Hilbert space `H`. This is where the spectral theorem itself lives.
- **`WStarAlgebra/`** — a new *top-level* folder, one level more concrete than `CStarAlgebra/`
  (needs a predual, not just the C⋆-identity) but abstract (no Hilbert space yet) — mirroring how
  `CStarAlgebra/` sits below `StarAlgebra/`. The *concrete* `B(H)` realization of the predual
  (trace-class operators) is Hilbert-space-specific and belongs in a new `HilbertSpace/TraceClass/`
  instead — the same abstract/concrete split already used throughout `Basic/`.

## Part 1: the spectral theorem

Source content, in *real* dependency order (corrected after checking actual imports — the first
pass at this list had Cayley before its own prerequisite; confirmed independent of `WStarAlgebra`,
so this part needs no W⋆-algebra work first):

0. **The spectral-measure type itself** (`Operators/SpectralTheory/WeakSpectralMeasure/{A,B}.lean`,
   ~2233 lines): `WOTSpectralMeasure` — a projection-valued measure valued in the weak-operator
   topology on `H`. Built on `Physlib.QuantumMechanics.Operators.SpectralTheory.SpectralMeasure`
   (already vendored, see above) plus Mathlib's own `WeakOperatorTopology`/vector-measure
   machinery — no `OperatorAlgebra`-class adaptation needed, this is genuinely Hilbert-space-level
   already. Everything below depends on this type existing first (`Spec/Cayley.lean` uses it via
   `Affil/Concrete.lean`), which is why it's step 0, not folded into "Stone's theorem" as first
   drafted.
1. **Cayley-transform construction** (`OperatorAlgebra/Spec/{Cayley,CayleyInverse,
   CayleyCertificate,CayleySpectralData/{P1,P2},BoundedSelfAdjointData}.lean`, ~3350 lines): turn a
   self-adjoint unbounded operator into a bounded unitary via the Cayley transform, whose spectral
   theorem is the tractable case.
2. **The bounded-unitary spectral theorem** (`OperatorAlgebra/Spec/UnitaryInfrastructure/
   {P1,P2}.lean`, ~2245 lines) and pulling it back through the Cayley transform
   (`EigenvectorSpectralAtom.lean`, `SpectralDecomposition.lean`, ~585 lines) to the original
   unbounded operator.
3. **Stone's theorem and the spectral integral** (`Operators/SpectralTheory/{Stone,
   SpectralIntegral/{P1,P2},TypeDecomposition}.lean`, ~2870 lines): generator ↔ one-parameter
   unitary group (already partly present via `Physlib`'s `UnitaryOneParameterGroup`, used by
   `HilbertSpace/Dynamics/*` — check for overlap before porting), reconstructing
   $T = \int \lambda \, dE(\lambda)$, and pure-point/absolutely-continuous/singular-continuous type
   decomposition.
4. **The payoff — closing `OrderUnit/Effect/Integral.lean`'s Scope 3**: that file's own docstring
   names "recovering a self-adjoint operator from its own spectral measure" as future work. Once
   the spectral theorem exists concretely, the honest question is whether the *weak-operator*
   spectral measure this construction produces can be connected to `Basic/`'s *effect-valued
   measure* framework (`OrderUnit/Effect/EffectValuedMeasure.lean`, and the finite-clopen-point
   connection `CStarAlgebra/SpectralMeasure.lean` already built this session) — a genuine synthesis
   theorem, not just two isolated constructions, but only attempted once it is honestly provable
   (matching this session's standing rule against forcing a shaky connection).

Rough total: ~11,300 lines of source content, concentrated in genuinely hard analysis (this is the
single deepest piece of mathematics in the whole `Unbounded/` tree). Expect this to need several
sequential (not parallel — the dependency chain above is close to linear) agent dispatches, each
independently verified the way every port this session has been, and realistically to span more
than one session.

## Part 2: W⋆-algebras

Independent of Part 1 in the source tree (`WStarAlgebra*.lean` never imports `Spec/`/`Flow/`).

1. **The abstract class and predual pairing** (`OperatorAlgebra/WStarAlgebra.lean`,
   `WStarAlgebra/{RankOnePairing,TracePairingNorm}.lean`, ~490 lines) → `WStarAlgebra/Basic.lean`:
   `class WStarAlgebra (A) extends [CStarAlgebra-level hypotheses]` with a predual, adapted off
   `CStarAlgebra/` rather than off the source's own `OperatorAlgebra`.
2. **Trace-pairing surjectivity** (`WStarAlgebra/TracePairingSurj.lean`, 545 lines): the Riesz-type
   theorem that the predual pairing is onto — the hard direction.
3. **The concrete `B(H)` realization** (`OperatorAlgebra/{TraceClass.lean,TraceClass/*}.lean`, ~16
   files, ~3900 lines: the trace-class Banach space, Hilbert–Schmidt operators, the trace pairing
   `B(H) → 𝒮₁(H)'`) → `HilbertSpace/TraceClass/`, plus `WStarAlgebra/{FiniteDimensional,
   InfiniteDim}.lean` (~220 lines) showing `B(H)` is a genuine instance of the abstract class from
   step 1. This is a natural, much richer sequel to `HilbertSpace/Trace.lean` (built earlier this
   session, which only has the bare trace functional, not the full Banach-space/predual structure).

Rough total: ~5150 lines. Smaller and more self-contained than Part 1 — a reasonable place to
start, or to run in parallel with early Part 1 work once both are scoped.

## Sequencing

Independent in the source, so order is a real choice, not forced:

- **W⋆-algebras first** is lower-risk and faster to a landed result — it doesn't touch unbounded
  operators at all, and `HilbertSpace/TraceClass/` extends work already in this repo
  (`HilbertSpace/Trace.lean`).
- **The spectral theorem first** is the deeper payoff (closes a named gap, is the mathematical
  heart of the source tree) but is a long, mostly-linear dependency chain — less parallelizable,
  more session-spanning.

Neither blocks the other. Not yet decided which to dispatch first — see Status.

## Status (updated as formalization proceeds)

Both tracks' true first steps are done, independently verified (fresh build, zero sorries/
warnings, checked for reuse and naming collisions), wired into `PhyslibAlpha.lean`, and committed.

- **Part 1, step 0** (`WOTSpectralMeasure`) — **built**, in `HilbertSpace/Unbounded/{Basic,
  ScalarMeasure,Conjugation,BoundedIntegral,BoundedIntegralAlgebra,StoneUnitaryGroup,
  WeakIntegral}.lean` (~2657 lines). Reuses `Physlib`'s norm-topology `SpectralMeasure` via a real
  bridge (`SpectralMeasure.toWOT`) rather than duplicating it. Also reaches slightly ahead of
  step 0's own scope into part of step 3 for free: the bounded weak-operator spectral integral and
  the strongly continuous unitary group generated by a real spectral measure (Stone's theorem's
  representation-level half) are already here. Step 1 (Cayley-transform construction) is next.
- **Part 2, step 1** (abstract `WStarAlgebra` class) — **built**, in `WStarAlgebra/Basic.lean`.
  **Real collision found and fixed**: Mathlib already has its own `WStarAlgebra` (`Mathlib.
  Analysis.VonNeumannAlgebra.Basic`), `Prop`-valued (mere existence of a predual, deliberately not
  choosing one). The ported notion is data (one *chosen* predual, needed since the weak-⋆ topology
  depends on which one) — related but different, renamed `WStarAlgebraStructure` to avoid the name
  clash. Connecting the two formally (our predual identification is linear, Mathlib's is
  conjugate-linear) is documented as real, unattempted work, not forced. Step 2 (trace-pairing
  surjectivity) needs `TraceClass H` first — not yet started.

**Lesson for the rest of this port, worth remembering**: check for Mathlib name collisions on
each new top-level declaration before treating a standalone build as sufficient — `lake build` on
a file's own dependency closure doesn't surface a collision that only exists once the file joins
the full `PhyslibAlpha.lean` aggregate; the `WStarAlgebra` clash only showed up at that last step.
