# Boost-weight product and parity extraction: investigation report

Read-only investigation. No Lean was elaborated, built, linted, cached or probed; no Lean
file, import, dependency, other report or roadmap file was edited. The only file added by
this task is this report.

Claims below are tagged:

- **[S]** source-verified — read directly from the files and line numbers cited.
- **[M]** mathematical deduction from **[S]** facts, done on paper, not machine-checked.
- **[K]** uncompiled Lean sketch — illustrative only, never elaborated.

---

## 1. Source provenance and exact scope inspected

**[S]** Working tree `/Users/josephsmith/LocalGithub/JTSphyslib`, branch `AddPotentialAlgebra`.

| item | value |
| --- | --- |
| HEAD | `7db2baf182932c35fcb5ed5d00b5f321049ae906` (`docs: add AI task folder and some AI analysis tasks`, 2026-09-21) |
| handoff reference commit | `5589e23dde62da95d6f7e4d9467cf63ecc111680` |
| relation | reference is an ancestor of HEAD |
| `git diff 5589e23d..HEAD --stat` | three files, all under `AITasks/` — **no `.lean` file differs** |
| dirty files at start | `Draft.md` only (3 insertions, 1 deletion); not a Lean source, not inspected for content |
| `lean-toolchain` | `leanprover/lean4:v4.33.0` |
| `lake-manifest.json` | manifest version `1.2.0`; `mathlib` rev `db584cd6d46c92f209a44c0f1c829460d327499d`, inputRev `v4.33.0` |
| git worktrees | one — this checkout is not the bump workspace and holds no 4.34.0 material |

**[S]** Every declaration named in the handoff is present at the reference revision, byte for
byte. Nothing had to be relocated and no material difference from the handoff's description
was found. Mathlib claims below were read from `.lake/packages/mathlib` at rev `db584cd6`
(v4.33.0) and are asserted **only** for that snapshot.

Read in full: `Physlib/Relativity/LorentzGroup/Boosts/WeightGrading.lean` (246 lines),
`Physlib/Particles/StandardModel/CovAlgebraRealization/YukawaSector/MassDimLTEight.lean` (386),
`Physlib/Particles/StandardModel/AlgebraRealization/HiggsAlgebraCovRealization/DerivSubmodule/BoostWeightDecomposition.lean` (339).
Read in relevant part: the general `Lorentz.BoostWeight.WeightDecomposition` blocks of
`IsFermionSector/DerivSubmodule/BoostWeightDecomposition.lean` and
`IsGaugeSector/DerivSubmodule/BoostWeightDecomposition.lean`;
`HiggsAlgebraCovRealization/Basic.lean` lines 1122–1232 (`IsDerivativeCollection`,
`boostDecomp`, `trivialWeightDecomposition`);
`CovAlgebraRealization/FermionGaugeSector/MassWeight.lean`;
`Relativity/LorentzGroup/Invariants/LorentzCovariance.lean`;
`Relativity/Fermions/Weyl/BoostWeight.lean` (section A);
`Relativity/IsLorentzDeriv.lean` (header); `Relativity/LightConeDeriv.lean` (declaration index).
Consumer inventory by repository-wide grep, not from the handoff's starting list. Import
closures by a static parse of `import` lines (script kept in the scratchpad, not added to the
repository).

**Not inspected:** the interiors of the fermion and gauge sector files beyond their general
blocks and their `derivSubmoduleBoostWeight*` contracts; `Relativity/LorentzGroup/Boosts/`
siblings other than `Axis.lean:152`.

### 1.1 The build blocker, verified statically

**[S]** `StandardModel.JetAlgebra.SectorEquiv.Basic` is genuinely in the import closure of
every file holding the candidate declarations. The chain, each link read from the importing
file's header:

```
CovAlgebraRealization/YukawaSector/MassDimLTEight.lean
  → IsFermionSector/DerivSubmodule/BoostWeightDecomposition.lean      (line 13, private import)
  → AlgebraRealization/HiggsAlgebraCovRealization/Basic.lean          (line 10)
  → JetAlgebra/CovJetAlgebra/Higgs.lean                               (line 9)
  → JetAlgebra/CovJetAlgebra/Basic.lean → JetAlgebra/Realization.lean
  → AlgebraRealization/Basic.lean → JetAlgebra/TransformsIn.lean
  → JetAlgebra/MassWeightPoly.lean → JetAlgebra/Generators.lean
  → JetAlgebra/Invariants.lean → JetAlgebra/LorentzAction.lean
  → JetAlgebra/SectorEquiv/Structure.lean → JetAlgebra/SectorEquiv/Basic.lean
```

**[S]** Closure check across the relevant files:

| file | behind the blocker? |
| --- | --- |
| `Relativity/LorentzGroup/Boosts/WeightGrading.lean` | **no** (closure 58 Physlib files, no `StandardModel/`) |
| `Relativity/LorentzGroup/Invariants/LorentzCovariance.lean` | **no** (62, no `StandardModel/`) |
| `Relativity/Fermions/Weyl/BoostWeight.lean` | **no** (62) |
| `Relativity/IsLorentzDeriv.lean` | **no** (59) |
| `CovAlgebraRealization/YukawaSector/MassDimLTEight.lean` | **yes** |
| `.../YukawaSector/Basic.lean` | **yes** |
| `HiggsAlgebraCovRealization/Basic.lean` | **yes** |
| `HiggsAlgebraCovRealization/DerivSubmodule/BoostWeightDecomposition.lean` | **yes** |
| `IsFermionSector/DerivSubmodule/BoostWeightDecomposition.lean` | **yes** |
| `IsGaugeSector/DerivSubmodule/BoostWeightDecomposition.lean` | **yes** |
| `CovAlgebraRealization/FermionGaugeSector/MassWeight.lean` | **yes** (via the same chain) |

**[M]** Consequence for this report: *every* source fragment in §2 except `WeightGrading.lean`
itself sits behind the blocker. A proof-looking body in those files is not evidence that it
elaborates at this revision. I have read them as mathematics and as a specification of the
intended contracts, not as verified Lean. This is the single largest caveat on everything
below, and it is also the strongest practical argument *for* the extraction: **[M]** 18
declarations with no Standard Model content are currently unbuildable for reasons that have
nothing to do with them.

I did not attempt to repair, diagnose or build the blocker, per the handoff.

---

## 2. Extraction inventory

### 2.0 The full picture: general API scattered across four Standard Model files

The handoff names one block. **[S]** Repository-wide grep for
`namespace Lorentz.BoostWeight.WeightDecomposition` finds **four** such blocks inside
`Physlib/Particles/StandardModel/`, holding 18 declarations between them, none of which
mentions the Standard Model:

| file | lines | declarations |
| --- | --- | --- |
| `CovAlgebraRealization/YukawaSector/MassDimLTEight.lean` | 53–205 | 9 (the handoff's list) |
| `IsFermionSector/DerivSubmodule/BoostWeightDecomposition.lean` | 49–113 | 4 (`ofWeightBasis`, `iSupFintype`, `iSupFintype_piece`, `ofAxisTwo`) |
| `AlgebraRealization/HiggsAlgebraCovRealization/DerivSubmodule/BoostWeightDecomposition.lean` | 40–77 | 3 (`ofTrivialAction`, `ofTrivialAction_piece`, `ofTrivialAction_supp`) |
| `IsGaugeSector/DerivSubmodule/BoostWeightDecomposition.lean` | 42–70 | 2 (`iSupOfSupp`, `iSupOfSupp_piece`) |

**[M]** Each block is prefixed by the identical variable line
`variable {K : Type*} [Field K] [Algebra ℝ K] {M : Type*} [AddCommGroup M] [Module K M]`,
i.e. the generality of `WeightGrading.lean` itself. **[S]** The pattern is deliberate: each
sector file opens with a general block, closes it, and only then enters
`namespace StandardModel`. The structure of the repository already records the judgement that
this material is general; only its *location* is wrong.

I report the 18 for completeness but, per the handoff's scope discipline, §5 proposes moving
only a bounded subset, with the rest named as follow-on work.

### 2.1 Declaration table — the handoff's nine

Namespace for all nine: `Lorentz.BoostWeight.WeightDecomposition`.
Surrounding variables, **[S]** `MassDimLTEight.lean:69–70`:
`{K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [Ring A] [Algebra K A]`,
`{rep : Representation K SL(2,ℂ) A} {i : Fin 3} {V W : Submodule K A}`.
Abbreviation used below: `hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y`.

| # | declaration | line | effective hypotheses (after `omit`/usage analysis) | genuine proof dependencies | class | consumers |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `mul_le_iSup_convolution` | 75 | **`omit [Algebra ℝ K]` at line 72.** Needs only `{K} {A} [Ring A] [Algebra K A]` and `(p q : ℤ → Submodule K A)`. **[M]** `[Field K]` is inherited, not used — `Submodule.iSup_mul`/`mul_iSup` are stated at `[CommSemiring R]`. No `rep`, no `i`, no boost weight. | `Submodule.iSup_mul`, `Submodule.mul_iSup`, `iSup_le`, `le_iSup_of_le` | **pure submodule mathematics**; **wrapper of library machinery** | 1 internal (line 108). No external consumer. |
| 2 | `mulOfMul` | 87 | full block + `hmul` + `d₁ d₂` | `mul_mem_boostWeightSubmodule` (WeightGrading:87), `mul_le_iSup_convolution`, `Submodule.mul_le`, `mul_bot`, `bot_mul`, `mul_mem_mul`, `Finset.add_mem_add`, the four `WeightDecomposition` fields | **general Lorentz boost-weight mathematics** (needs an algebra structure on the carrier) | `MassDimLTEight.lean:178, 198, 199`; **`CovAlgebraRealization/FermionGaugeSector/MassWeight.lean:81`** |
| 3 | `mulOfMul_supp` | 114 | as 2 | `rfl` | accessor | `MassDimLTEight.lean:126` |
| 4 | `exists_add_eq_of_mem_mulOfMul_supp` | 121 | as 2, `hmul` implicit | `mulOfMul_supp`, `Finset.mem_add` | **wrapper of library machinery** | lines 136, 146 |
| 5 | `two_dvd_of_mem_mulOfMul_supp` | 131 | as 2, `hmul` implicit, + parity of both supports | 4, `dvd_add` | general (parity of a Finset sumset) | `MassDimLTEight.lean:267` |
| 6 | `not_two_dvd_of_mem_mulOfMul_supp` | 141 | as 2, `hmul` implicit, + even/odd supports | 4, `dvd_add_right` | general (as 5) | `MassDimLTEight.lean:247, 266`; **`FermionGaugeSector/MassWeight.lean:88`** |
| 7 | `sup_supp` | 151 | `{K} [Field K] [Algebra ℝ K] {A} … {rep} {i} {V W}` — **[M]** but `sup` itself is defined in `WeightGrading.lean:226` at `{M} [AddCommGroup M] [Module K M]`; the `[Ring A] [Algebra K A]` here is inherited and unused | `rfl` | **orphan accessor** — belongs beside `sup_piece` (WeightGrading:236–238) | `MassDimLTEight.lean:309` |
| 8 | `map_boostWeightSubmodule_le` | 170 | declares its own `{M N} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] {repM} {repN}`; `[Field K] [Algebra ℝ K]` inherited and **genuinely required** (they are prerequisites of `boostWeightSubmodule` itself). **[M]** `[Ring A] [Algebra K A]` inherited and unused. | `boostWeightSubmodule` membership unfolding, `map_smul` | **general Lorentz boost-weight mathematics** | line 191 only |
| 9 | `mem_of_invariant_of_mem_sup_of_odd_supp` | 182 | declares its own `{M} [AddCommGroup M] [Module ℂ M] {repLorentz} {j} {V}`. **[M]** `ℂ` is a *specialisation*, not a requirement — see §2.3. `[Ring A]`, `[Algebra K A]`, `[Field K]`, `[Algebra ℝ K]` all inherited and unused at `ℂ`. | 8; `mem_of_mem_iSup_of_boostWeight_zero` (WeightGrading:176); `mem_boostWeightSubmodule_zero_of_invariant` (WeightGrading:132); `Representation.quotient` (Mathlib `RepresentationTheory/Basic.lean:333`); **`Lorentz.quotient_apply_mkQ`** (`LorentzCovariance.lean:182–185`, proved `rfl`); `Submodule.{map_mono, mem_sup, map_iSup, mem_map_of_mem, map_bot, mem_bot, ker_mkQ, Quotient.mk_eq_zero}` | **general Lorentz boost-weight mathematics** | `MassDimLTEight.lean:293, 305`; **`FermionGaugeSector/MassWeight.lean:112`** |

**[S] Section-variable warning, discharged.** The handoff asks not to mistake the surrounding
file's variables for genuine prerequisites. Three concrete instances found:

- `mul_le_iSup_convolution` carries an explicit `omit [Algebra ℝ K] in` (line 72) but still
  inherits `[Field K]`, which it does not use.
- `sup_supp` inherits `[Ring A] [Algebra K A]` although `WeightDecomposition.sup` is defined
  without them.
- `mem_of_invariant_of_mem_sup_of_odd_supp` inherits the whole algebra block while working in
  a bare module `M`.

**[M]** None of these is a soundness problem; all three would simply become cleaner in a
destination file whose variable block matches the mathematics.

### 2.2 The remaining nine general declarations

| declaration | file:line | hypotheses | class | consumers |
| --- | --- | --- | --- | --- |
| `ofTrivialAction` | Higgs BWD:49 | `rep`, `htriv : ∀ g x, rep g x = x`, `i` | general | Higgs BWD:127, 132 (and :69, :85 via `ofTrivialAction_piece`) |
| `ofTrivialAction_piece` | Higgs BWD:67 | as above | accessor (`rfl`) | Higgs BWD:69, 70, 85, 86 |
| `ofTrivialAction_supp` | Higgs BWD:73 | as above | accessor (`rfl`) | none outside its file |
| `ofWeightBasis` | Fermion BWD:58 | `[Fintype ι]`, a `Module.Basis ι K M` of weight vectors, a weight function, **a supplied `s` with `∀ j, wt j ∈ s`** | general | Fermion BWD (2 sites) |
| `iSupFintype` | Fermion BWD:78 | `[Fintype ι]`, a family of decompositions | general | Fermion BWD (2 sites) |
| `iSupFintype_piece` | Fermion BWD:92 | as above | accessor (`rfl`) | Fermion BWD |
| `ofAxisTwo` | Fermion BWD:99 | a decomposition of `⊤` along axis `2` | general | Fermion BWD (4 sites) |
| `iSupOfSupp` | Gauge BWD:52 | arbitrary (possibly infinite) `ι`, **a supplied common `s` with `∀ a, (d a).supp ⊆ s`** | general | Gauge BWD (2 sites) |
| `iSupOfSupp_piece` | Gauge BWD:65 | as above | accessor (`rfl`) | Gauge BWD |

**[M]** `iSupFintype` and `iSupOfSupp` are the same construction with two different support
strategies — a `biUnion` over a finite index, versus a user-supplied common bound for an
arbitrary index. **[M]** `iSupFintype` is derivable from `iSupOfSupp` by taking
`s := Finset.univ.biUnion fun a => (d a).supp`, so a single home would let one be a corollary
of the other. Neither is in the handoff's scope and I do not propose merging them here; the
observation belongs in the follow-on note.

**[M] Import feasibility, if `WeightGrading.lean` were the destination** (all **[S]** on the
locations):

- `ofAxisTwo` needs `SL2C.boostAxis_eq_conj` (`Boosts/Axis.lean:152`, already imported at
  `WeightGrading.lean:8`) and `SL2C.rotationZToAxis` (`SL2C/AxisRotations.lean:136`, imported
  by `Axis.lean:8`). **No new Physlib import.**
- `mulOfMul` needs pointwise `+` on `Finset ℤ`; **[S]** `WeightGrading.lean:11` already imports
  `Mathlib.Algebra.Group.Pointwise.Finset.Basic`, and **[S]** no pointwise `Finset` operation
  appears anywhere in `WeightGrading.lean`'s 246 lines (its only `Finset` uses are
  `add_sum_erase`, `erase_eq`, `mem_union_left/right`, `sum_insert`, `mem_insert_self`,
  `insert_eq_self`, `sum_update_of_mem`, `ne_of_mem_erase`, `mem_of_mem_erase`). **[M]** That
  import is therefore currently carrying no weight in that file, and the one thing it would be
  needed for is `mulOfMul.supp`. I read this as deliberate pre-positioning for the move; I
  cannot confirm it is unused without a build, so it is probe P0b.
- `mem_of_invariant_of_mem_sup_of_odd_supp` needs `Representation.quotient`, **[S]** in
  `Mathlib.RepresentationTheory.Basic:333`, already imported at `WeightGrading.lean:9`.
- `mulOfMul` needs `Submodule` multiplication (`Mathlib/Algebra/Algebra/Operations.lean`).
  Whether that is already in `WeightGrading.lean`'s transitive Mathlib closure I **cannot
  determine without elaborating**; assume an explicit import is needed (probe P0a).
- `ofWeightBasis` needs `Module.Basis`; likely transitively present via
  `Mathlib.LinearAlgebra.Eigenspace.Basic`, but unverified (probe P0a).

### 2.3 The one cross-file dependency, and what it is not

**[S]** `mem_of_invariant_of_mem_sup_of_odd_supp`'s proof calls `quotient_apply_mkQ`
(`MassDimLTEight.lean:199`). That lemma lives in
`Relativity/LorentzGroup/Invariants/LorentzCovariance.lean:182–185`:

```
lemma quotient_apply_mkQ {B : Type*} [AddCommGroup B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (g : SL(2,ℂ)) (y : B) :
    repLorentz.quotient S (fun g y hy => hS g y hy) g (S.mkQ y) = S.mkQ (repLorentz g y) := rfl
```

**[S]** It is proved by `rfl`, and **[S]** it is stated at `ℂ`. **[M]** Two consequences.

1. **This is why `mem_of_invariant_of_mem_sup_of_odd_supp` is stated at `ℂ`.** Every other
   ingredient of that proof is `K`-generic. The `ℂ` is inherited from a helper lemma's
   accidental specialisation, not from the mathematics. Restating the helper at `K` (or
   inlining its `rfl`) would let the parity theorem be `K`-generic like the rest of
   `WeightGrading.lean`. **[M]** I flag this as a *consistency* fix, not a generalisation for
   its own sake: it makes the declaration match the file it would move into.
2. **[S]** `MassDimLTEight.lean` reaches `LorentzCovariance.lean` through
   `Physlib.Relativity.LorentzGroup.Invariants.RankFour` (line 10), and
   `LorentzCovariance.lean` imports `Invariants/Basic.lean`, which is the home of
   `exists_invariantCoeff`.

**Answer to the handoff's question 4 on dependence upon the invariant-coefficient lifting
theorem: there is none.** **[M]** No declaration in §2.1 or §2.2 calls `exists_invariantCoeff`,
`exists_invariantCoeff_matrix`, `exists_isInvariantCoeff_of_mem_span`, `contractₗ`, `actMat`,
or anything else from the coefficient-lifting development. The *only* thread between the two
subjects is the `rfl` lemma above, which is about quotient representations and has no
coefficient content. The two tasks are genuinely independent, as the handoff states.

**[M]** This matters for the extraction: if the parity theorem moved to `WeightGrading.lean`
naively, `WeightGrading.lean` would have to import `LorentzCovariance.lean`, dragging in
`Invariants/Basic.lean`, `LightConeDeriv.lean` and `Mathematics/LinearCombination.lean` — a
large and entirely spurious dependency, and one that would point the boost-weight file at the
coefficient-lifting file for a `rfl`. **The recommended fix is to inline it**: the proof step
becomes `fun g => congrArg S.mkQ (hinv g)` or `fun g => by rw [show … = … from rfl, hinv g]`.

---

## 3. The mathematics

### 3.1 The product decomposition

**[S]** `mulOfMul` (MassDimLTEight.lean:87–108) builds, from `d₁ : WeightDecomposition rep i V`
and `d₂ : WeightDecomposition rep i W`, a `WeightDecomposition rep i (V * W)` with

```
piece m := ⨆ (k : ℤ) (l : ℤ) (_ : k + l = m), d₁.piece k * d₂.piece l
supp    := d₁.supp + d₂.supp                                  -- pointwise Finset sum
```

**[M]** The four obligations and where each hypothesis is spent:

- **`piece_le m`** — that the weight-`m` piece really has weight `m`. Reduces by
  `Submodule.mul_le` to: `a ∈ d₁.piece k`, `b ∈ d₂.piece l`, `k + l = m` implies
  `a * b ∈ boostWeightSubmodule rep i m`. **[S]** This is exactly
  `mul_mem_boostWeightSubmodule` (`WeightGrading.lean:87–93`), whose proof is
  `rep Λ (x*y) = rep Λ x * rep Λ y = (t^a • x)(t^b • y) = t^(a+b) • (x*y)`. The three
  ingredients: **multiplicativity of the representation** (`hmul`, the only hypothesis
  `mulOfMul` adds beyond the two decompositions); **scalar compatibility**
  (`smul_mul_smul_comm`, which needs `A` to be an algebra over `K`, supplied by
  `[Algebra K A]`); and **`zpow_add₀`** on `algebraMap ℝ K t`, which needs that scalar nonzero
  — supplied by the private `algebraMap_ne_zero` (`WeightGrading.lean:67–68`) and hence by
  `[Field K]` (injectivity of a ring hom out of a field) and `[Algebra ℝ K]`.
- **`piece_eq_bot m hm`** — that pieces vanish off `d₁.supp + d₂.supp`. **[S]** The proof
  (lines 97–101) case-splits on `k ∈ d₁.supp`: if yes, then `l ∉ d₂.supp` (else `k + l = m`
  would be in the sumset, by `Finset.add_mem_add`), so the right factor is `⊥` and
  `Submodule.mul_bot` finishes; if no, the left factor is `⊥` and `Submodule.bot_mul` finishes.
  **[M]** Note both `mul_bot` and `bot_mul` are used, and neither is derivable from the other
  without commutativity — the proof is already written to be order-safe.
- **`iSup_piece`** — that the pieces join to `V * W`. **[S]** `le_antisymm` of two inequalities
  (lines 102–108). The `≤` direction: each `d₁.piece k * d₂.piece l ≤ V * W` by
  `Submodule.mul_mem_mul` and `d₁.iSup_piece`/`d₂.iSup_piece`. The `≥` direction: rewrite
  `V * W` as `(⨆ k, d₁.piece k) * (⨆ l, d₂.piece l)` and apply `mul_le_iSup_convolution`.

**[M] Factor order is preserved throughout, and must be.** `A` is `[Ring A]`, not
`[CommRing A]`. Every step keeps `d₁` on the left of `d₂`: the piece is
`d₁.piece k * d₂.piece l` (never `d₂.piece l * d₁.piece k`); `mul_mem_boostWeightSubmodule`
takes its arguments in the order `hx : x ∈ …a`, `hy : y ∈ …b` and concludes about `x * y`; and
`mul_le_iSup_convolution` rewrites with `Submodule.iSup_mul` first and `Submodule.mul_iSup`
second, i.e. it peels the left factor first. **[M]** The weight index `m = k + l` *is*
commutative (`ℤ`), which is what makes `supp` symmetric, but the submodules are not, and
`mulOfMul d₁ d₂` and `mulOfMul d₂ d₁` decompose *different* submodules (`V * W` versus
`W * V`). Any restatement must not "simplify" by symmetrising.

**[M] Associativity is also load-bearing at the consumer.** **[S]**
`higgsSqFermionBoostWeight` (MassDimLTEight.lean:252–261) is
`mulOfMul hmul (mulOfMul hmul dH dH') dF`, decomposing
`derivSubmodule a * derivSubmodule b * derivSubmodule c`. That type-checks only because Lean
parses `x * y * z` as `(x * y) * z` and the nesting is left. A restated `mulOfMul` that
changed argument order, or a "convenience" ternary version, would break this silently at the
elaboration level rather than the mathematical one.

**[M] What is *not* needed, and must not be introduced.** No direct-sum grading
(`DirectSum.Decomposition`, `SetLike.GradedMonoid`); no homogeneous basis; no canonical or
unique decomposition; no finite-dimensionality of `A`; no `iSupIndep` hypothesis. The
construction is purely about joins of submodule products. **[S]** Independence *is* available
(`boostWeightSubmodule_iSupIndep`, `WeightGrading.lean:125`) and *is* used elsewhere
(`mem_of_mem_iSup_of_boostWeight_zero`), but `mulOfMul` never touches it. Introducing a graded
structure would be the classic over-abstraction here: it would demand that the pieces be
*equal* to the weight spaces rather than contained in them, which is false for the sector
submodules (§3.2).

### 3.2 `mul_le_iSup_convolution`: keep, strengthen, or replace?

**[S]** The statement is

```
(⨆ k, p k) * (⨆ l, q l) ≤ ⨆ (m : ℤ) (k : ℤ) (l : ℤ) (_ : k + l = m), p k * q l
```

and the proof is four lines: `Submodule.iSup_mul`, `iSup_le`, `Submodule.mul_iSup`, then
three `le_iSup_of_le` to land at `(m, k, l, rfl)`.

**[M] Assessment.** The current hypotheses are *more* than needed (§2.1 row 1: `[Field K]` and
`[Algebra ℝ K]` are both inert, the latter explicitly omitted, the former not). But the
interesting observation is that the statement is the weaker half of an **equality**:

**[M]** `(⨆ k, p k) * (⨆ l, q l) = ⨆ k, ⨆ l, p k * q l` by
`Submodule.iSup_mul` (Mathlib `Algebra/Algebra/Operations.lean:297`) and
`Submodule.mul_iSup` (:300), and `⨆ k, ⨆ l, p k * q l = ⨆ m, ⨆ k, ⨆ l, ⨆ (_ : k + l = m), p k * q l`
by reindexing the double join along the surjection `(k, l) ↦ k + l` — each `(k,l)` appears
exactly once on the right, under `m = k + l`.

**[S]** And the *other* inequality is proved separately, inline, at `MassDimLTEight.lean:103–106`
(the first branch of `iSup_piece`'s `le_antisymm`). **[M]** So the file currently proves both
halves of one identity in two places, in two styles. Stating the equality once and taking
`le_antisymm` for free is a genuine simplification — it removes a duplicated argument and names
the fact.

**[M] Replace by a library result?** No: I found no Mathlib lemma of this convolution shape.
`Submodule.iSup_mul` and `Submodule.mul_iSup` are the two halves of the *unindexed* step, and
the reindexing is the part Physlib must supply. So the recommendation is **keep the lemma,
strengthen it to an equality, drop the inert typeclasses, and give it a home where it reads as
what it is** — a statement about submodule products and joins with no boost weight, no
representation and no `ℤ` structure beyond addition. **[M]** Stated at a general additive index
it would read:

**[K]** (uncompiled sketch)
```lean
lemma Submodule.iSup_mul_iSup_eq_iSup_add {R A ι : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [AddMonoid ι] (p q : ι → Submodule R A) :
    (⨆ k, p k) * (⨆ l, q l) = ⨆ (m : ι) (k : ι) (l : ι) (_ : k + l = m), p k * q l
```
**[M] Counter-consideration.** That is a Mathlib-shaped statement in a `Submodule` namespace,
and putting it in Physlib means Physlib carries a lemma that arguably belongs upstream.
Generalising the index from `ℤ` to `AddMonoid ι` is speculative — nothing needs it. **[M] My
recommendation is the middle course**: strengthen to an equality, keep it at `ℤ` and keep the
`Submodule R A` generality it already has, and place it in the destination file with a comment
that it is a candidate for upstreaming. Do not chase the `AddMonoid` version.

### 3.3 The role of `ofTrivialAction`

**[S]** `ofTrivialAction rep htriv i : WeightDecomposition rep i ⊤` with
`piece k := if k = 0 then ⊤ else ⊥` and `supp := {0}`, for any `rep` acting as the identity
(`Higgs BWD:49–63`).

**[M]** Its role in the architecture is to be the *base case* of the weight bookkeeping. The
general machine that produces sector decompositions is **[S]** `IsDerivativeCollection.boostDecomp`
(`HiggsAlgebraCovRealization/Basic.lean:1158–1201`), which takes a symbol map whose derivative
slots rotate as Lorentz vectors plus a decomposition `hw` of the *value space* `W`, and returns
a decomposition of the span of the symbols, with weights
`(∑ j, lightConeWeight (c j)) + (weight in W)`. A Lorentz-trivial value space contributes
nothing, and `ofTrivialAction` is the statement of "nothing". **[S]** The Higgs file uses it
exactly so: `higgsValueWeight` and `barHiggsValueWeight` (`Higgs BWD:125–132`) are
`ofTrivialAction` at the dual and conjugate-dual of the trivial representation on `HiggsVec`,
and are fed straight into `boostDecomp` at lines 226 and 233. I do not expand further into the
Higgs derivative constructions, per the handoff.

**[S] A concrete duplication that the extraction would remove.**
`HiggsAlgebraCovRealization.trivialWeightDecomposition` (`HiggsAlgebraCovRealization/Basic.lean:1213–1227`)
is a 14-line `where`-block for `WeightDecomposition (1 : Representation ℂ SL(2,ℂ) ℂ) i ⊤` whose
`piece`, `supp`, `piece_eq_bot` and `iSup_piece` are **character-for-character the same** as
`ofTrivialAction`'s, differing only in `piece_le` (`simp` versus
`rw [htriv, zpow_zero, one_smul]`). **[S]** `ofTrivialAction`'s own docstring (`Higgs BWD:46–48`)
says so: *"`HiggsAlgebraCovRealization.trivialWeightDecomposition` is the case `M = K`."*
**[M]** They are not shared today because `ofTrivialAction` lives in a file that imports
`HiggsAlgebraCovRealization/Basic.lean`, so the dependency runs the wrong way. **[S]** But
`HiggsAlgebraCovRealization/Basic.lean:14` already imports
`Physlib.Relativity.LorentzGroup.Boosts.WeightGrading`. **[M]** So moving `ofTrivialAction` into
`WeightGrading.lean` immediately makes `trivialWeightDecomposition` a one-liner
(`ofTrivialAction 1 (fun _ _ => rfl) i`, modulo whether `(1 : Representation …) g x = x` is
`rfl` — **[S]** the existing proof discharges the analogous goal with `simp`, so `rfl` may not
suffice and `fun g x => by simp` may be needed). It has **[S]** 6 references across 3 files, so
this is a real, if small, payoff.

### 3.4 `supp` semantics: read the field literally

**[S]** The structure (`WeightGrading.lean:198–206`):

```
structure WeightDecomposition (rep : Representation K SL(2,ℂ) M) (i : Fin 3) (V : Submodule K M) where
  piece : ℤ → Submodule K M
  supp : Finset ℤ
  piece_le : ∀ k, piece k ≤ boostWeightSubmodule rep i k
  piece_eq_bot : ∀ k ∉ supp, piece k = ⊥
  iSup_piece : (⨆ k, piece k) = V
```

**[M] `piece_eq_bot` is a one-way condition.** It says `supp` *contains* the set of weights
with a nonzero piece. It does **not** say the reverse: `k ∈ supp` is entirely compatible with
`piece k = ⊥`. So `supp` is a *declared bound*, not the support, and the structure has no
field forcing minimality. Two decompositions with the same `piece` and different `supp` are
both legal and are different terms.

**[S] This is not hypothetical — it is how the library uses it.** Three constructions
deliberately over-declare:

- `ofWeightBasis` (`Fermion BWD:58–61`) takes `s` and `hs : ∀ j, wt j ∈ s` as *inputs*: the
  caller supplies any superset.
- `iSupOfSupp` (`Gauge BWD:52–54`) takes `s` and `hs : ∀ a, (d a).supp ⊆ s`: again any
  superset, and its docstring says so ("a common finite set of weights containing every
  member's support is supplied").
- `boostDecomp` (`HiggsAlgebraCovRealization/Basic.lean:1165–1166`) sets
  `supp := (Finset.univ ×ˢ hw.supp).image fun p => (∑ j, lightConeWeight (p.1 j)) + p.2`, an
  image over **all** light-cone multi-indices `c : Fin n → Fin 4` with no check that the
  corresponding `lightConeDeriv F i c` has nonzero range. **[M]** For a sector whose symbols
  satisfy relations, or at `n = 0` where the four `c` collapse, this is visibly redundant.

**[M] Consequences, and none of them is a soundness problem.**

1. **The parity arguments stay valid.** Over-declaring `supp` makes the hypotheses
   `∀ k ∈ supp, 2 ∣ k` and `∀ k ∈ supp, ¬ 2 ∣ k` *harder to satisfy*, and makes the conclusion
   of `piece_eq_bot` apply to *fewer* `k`. Both directions are safe: nothing concludes
   "`k ∈ supp`, therefore `piece k ≠ ⊥`". I checked all nine declarations for such a step and
   found none.
2. **`supp` is not an invariant of the decomposed submodule.** `mulOfMul_supp`'s value
   `d₁.supp + d₂.supp` depends on the *terms* `d₁`, `d₂`, not just on `V` and `W`. Any future
   lemma of the form "`V * W` has such-and-such weights" must be stated about a given
   decomposition, never about the submodule.
3. **Empty and redundant boundary cases.** **[M]** If `d₁.supp = ∅` then all `d₁.piece k = ⊥`,
   so `V = ⊥`, and `d₁.supp + d₂.supp = ∅` (the pointwise sum of Finsets is an image of a
   product, empty if either factor is), and `V * W = ⊥`. Consistent. If `0 ∈ d.supp` but
   `d.piece 0 = ⊥`, then `mem_of_invariant_of_mem_sup_of_odd_supp` is *inapplicable* (its
   `hodd` fails at `0`) even though its conclusion holds. That is exactly the gap §4.2
   proposes closing.

**[M] Do not add a minimality field.** Strengthening `piece_eq_bot` to an iff would break
`ofWeightBasis`, `iSupOfSupp` and `boostDecomp`, all of which would then owe a nontriviality
proof for every declared weight — in `boostDecomp`'s case, a proof that a light-cone symbol
range is nonzero, which is genuinely hard and sector-specific. The current design is right;
only the prose is wrong (§4.1).

### 3.5 Parity on the declared support

**[S]** Two lemmas, both routed through `exists_add_eq_of_mem_mulOfMul_supp`:

- `two_dvd_of_mem_mulOfMul_supp`: even ⊞ even ⊆ even, by `dvd_add`.
- `not_two_dvd_of_mem_mulOfMul_supp`: even ⊞ odd ⊆ odd, by `dvd_add_right`.

**[M]** Both are statements about the *declared* supports, so they inherit §3.4's over-approximation
harmlessly: an even bound plus an odd bound is an odd bound. They hold for zero submodules
(vacuously, empty sumset) and survive redundant entries (a redundant even entry contributes
redundant odd sums). **[M]** Note there is no "odd ⊞ odd ⊆ even" lemma, and none is needed: the
four surviving Yukawa products each have **exactly one** fermion factor, so odd ⊞ odd never
arises. **[S]** `higgsSqFermionBoostWeight` nests even ⊞ even first and only then ⊞ odd
(`MassDimLTEight.lean:263–270`).

**[M] Three gradings that must not be conflated**, since the handoff asks:

| grading | carrier | values | where |
| --- | --- | --- | --- |
| **boost weight** | a representation of `SL(2,ℂ)`, one grading per spatial axis `i : Fin 3` | `ℤ`, additive under multiplication | `boostWeightSubmodule rep i w` |
| **mass weight / mass dimension** | the algebra `B` via `massWeightPoly : B →ₐ[ℂ] Polynomial B` | `ℕ` | `sectorMassWeight`, `massWeightSubmodule` |
| **fermionic statistics** | — | — | **nowhere in this development** |

**[M]** The parity argument is entirely about the first. The theorem it proves is about the
second: **[S]** `mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup` and
`…_seven_sup` (`MassDimLTEight.lean:287–313`) say that *mass* weights 5 and 7 carry no Lorentz
invariant, and they get there by showing that every product occurring at those mass weights has
odd *boost* weight. The link between the two gradings is not a grading morphism; it is the
sector-specific enumeration of which products occur at which mass weight
(`sectorMassWeight_higgs_fermion_five`, `…_seven`), which is Standard Model content and stays
in the Standard Model file.

**[M] Statistics play no role whatsoever.** `A` is `[Ring A]`; nothing anticommutes, no
superalgebra, no `ℤ/2`-grading of the algebra. **[S]** The fermion file's docstring calls the
odd support *"the boost-weight shadow of the spin-statistics split"*
(`IsFermionSector/DerivSubmodule/BoostWeightDecomposition.lean:566–567`). **[M]** That is
physics prose about *why* the weights come out odd — half-integer spin gives an odd Weyl
contribution `±1` on top of the even `±2, 0` from derivative slots — and it is a correct
gloss, but a reader must not infer that any statistics hypothesis is in play. Worth a
clarifying half-sentence if that docstring is ever touched; not a defect.

### 3.6 Invariance, weight zero, and the quotient

**Why invariance forces boost weight zero.** **[S]** `mem_boostWeightSubmodule_zero_of_invariant`
(`WeightGrading.lean:132–137`): if `rep g x = x` for every `g`, then in particular for
`boostAxis i t ht`, so `rep (boostAxis i t ht) x = x = (algebraMap ℝ K t) ^ 0 • x`. Two lines,
no content beyond `zpow_zero` and `one_smul`.

**Why the converse fails.** **[M]** `boostWeightSubmodule rep i 0` only constrains the
one-parameter boost subgroup along a *single* axis `i`. Everything commuting with that
constraint is free. Concretely, in the vector representation, **[S]** `lightConeWeight` takes
the value `0` on the two transverse light-cone directions of axis `i`
(`Relativity/.../BoostWeightDecomposition.lean:78`,
`lightConeWeight_eq_two_or_neg_two_or_zero`, and the Higgs file's gloss at lines 28–30:
"`+2` for `D₀ - Dᵢ`, `-2` for `D₀ + Dᵢ` and `0` for the two transverse directions"). **[M]**
So the axis-`i` weight-zero space of a rank-one tensor is two-dimensional, spanned by the two
directions transverse to `i`; rotations about the `i`-axis mix those two directions and fix
neither. Hence a weight-zero vector that is not invariant. **[M]** The gap is structural: the
weight-zero space is the fixed space of a one-parameter subgroup, and `SL(2,ℂ)` is six
real-dimensional. The implication runs one way only, which is precisely why the theorem is
phrased as an *exclusion* (no invariants where weight zero is impossible) and never as a
classification.

**The quotient step, traced.** **[S]** `mem_of_invariant_of_mem_sup_of_odd_supp`
(`MassDimLTEight.lean:182–203`), in order:

1. **`hzero`** (line 187): `d.piece 0 = ⊥`, from `d.piece_eq_bot 0` and `hodd 0 _ ⟨0, rfl⟩`
   (i.e. `2 ∣ 0`, contradicting oddness at `0`).
2. **stability ⇒ a quotient representation**: `repLorentz.quotient S (fun g y hy => hS g y hy)`
   (Mathlib `RepresentationTheory/Basic.lean:333`). **[M]** `hS` is exactly the hypothesis
   Mathlib's `le_comap` form needs, restated membership-wise.
3. **equivariance of `S.mkQ`** (line 191): supplied as `fun _ _ => rfl` to
   `map_boostWeightSubmodule_le`. **[M]** The quotient representation is *defined* so that this
   is definitional; that is the content of `quotient_apply_mkQ` (§2.3).
4. **`hle`** (lines 188–191): images of pieces stay of pure weight —
   `(d.piece m).map S.mkQ ≤ boostWeightSubmodule (quotient …) j m`, by `Submodule.map_mono` on
   `d.piece_le m` followed by `map_boostWeightSubmodule_le`.
5. **`hmem`** (lines 192–196): `S.mkQ x` lies in the join of the images. From
   `x = y + z` with `y ∈ V`, `z ∈ S` (`Submodule.mem_sup`), `S.mkQ z = 0`, and
   `d.iSup_piece` plus `Submodule.map_iSup`.
6. **`hinv'`** (lines 197–199): the class of `x` is invariant for the quotient representation.
   This is the `quotient_apply_mkQ` call.
7. **the kill** (lines 200–202): `mem_of_mem_iSup_of_boostWeight_zero hle hmem (…zero_of_invariant hinv' j)`
   puts `S.mkQ x` in `(d.piece 0).map S.mkQ`, which is `⊥` by `hzero` and `Submodule.map_bot`.
8. **conclusion** (line 203): `S.mkQ x = 0` means `x ∈ ker S.mkQ = S`.

**[M] Why stability of `S` cannot be dropped.** Without it there is no quotient representation
at step 2, so steps 4–7 have nothing to act on. **[S]** The gauge file makes the same point in
prose for its own peeling lemma (`GaugeGroup/Invariants/Basic.lean:182–184`): *"an unstable
line has no invariant but `0`, while its sum with the span may well carry invariants outside
the span."* The same counterexample applies here.

**[M] Where the weight machinery actually bites** is step 7, and only there: the job of
`mem_of_mem_iSup_of_boostWeight_zero` (`WeightGrading.lean:176–188`) is to convert "lies in a
join of pure-weight spaces **and** has weight zero" into "lies in the weight-zero one". Its own
proof rests on `boostWeightSubmodule_iSupIndep` (line 125), which rests on the weight-`k` space
sitting in the `2^k` eigenspace of the boost at parameter `2` and on `k ↦ 2^k` being injective.
**[M]** That is the single place where independence of the weight spaces is used in the whole
parity argument.

---

## 4. Documentation overclaims and mathematical risks

### 4.1 `supp` described as "the weights that occur" — five places

**[S]** All of the following describe `supp` as the set of weights *occurring*, which §3.4
shows is not what the structure guarantees:

| # | text | location |
| --- | --- | --- |
| O1 | `/-- The finite set of weights that occur. -/` (the field docstring itself) | `WeightGrading.lean:203` |
| O2 | *"a finitely supported family of subspaces of pure boost weight"* | `WeightGrading.lean:25–26` (module doc) — **[M]** this one is defensible: "finitely supported" in the `Finsupp` sense means vanishing off a finite set, which is exactly `piece_eq_bot`. No change needed. |
| O3 | `/-- The weights occurring in a convolution are the sums of the weights occurring in the two factors. -/` | `MassDimLTEight.lean:111–112` |
| O4 | `/-- A weight of a convolution splits as a weight of the left factor plus a weight of the right one. -/` | `MassDimLTEight.lean:119–120` |
| O5 | `/-- The weights of a join of two decompositions are the weights of the two. -/` and `/-- **The boost weights occurring in the Higgs derivative submodules** -/` | `MassDimLTEight.lean:149`; `Higgs BWD:129–130` |

**[M] Severity: documentation only.** Every *statement* is correct; only the prose promises
more. The fix is to speak of "the declared weights" or "the recorded support" rather than
"the weights that occur", and to say in O1 that `supp` is any finite set outside which the
pieces vanish, not necessarily the smallest. **[M]** O3's statement `supp = d₁.supp + d₂.supp`
is an exact equality and is fine; it is the word "occurring" that over-promises, twice in one
sentence.

**[M] Why this matters beyond tidiness.** A future contributor reading O1 could reasonably
write a lemma of the form `k ∈ d.supp → d.piece k ≠ ⊥` and find it unprovable, or worse,
*assume* it in a proof sketch. Since `boostDecomp` demonstrably over-declares (§3.4), such a
lemma would be false for the actual sector decompositions.

### 4.2 The oddness hypothesis is stronger than the proof needs

**[S]** In `mem_of_invariant_of_mem_sup_of_odd_supp`, `hodd` occurs exactly twice in the file:
once as the binder (line 184) and once in the proof (line 187, producing `hzero`). I checked
the remaining 16 lines of the proof (188–203) and `hodd` does not appear. **[M]** Therefore the
proof uses oddness **only** to establish `d.piece 0 = ⊥`, exactly as the handoff anticipates.

**[M] The natural statement is the zero-piece one**, with oddness as a corollary:

**[K]** (uncompiled sketch)
```lean
/-- A submodule whose weight-zero piece is trivial carries no Lorentz invariant beyond a
  Lorentz-stable submodule `S`: an invariant of the join with `S` already lies in `S`.
  Invariance forces boost weight zero, and there is nothing of weight zero on offer. -/
lemma mem_of_invariant_of_mem_sup_of_piece_zero
    (d : WeightDecomposition repLorentz j V) (hzero : d.piece 0 = ⊥)
    (S : Submodule ℂ M) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : M}
    (hx : x ∈ V ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := …

/-- A submodule all of whose declared boost weights are odd has trivial weight-zero piece,
  since zero is even. -/
lemma mem_of_invariant_of_mem_sup_of_odd_supp
    (d : WeightDecomposition repLorentz j V) (hodd : ∀ k ∈ d.supp, ¬ (2 : ℤ) ∣ k)
    (S : Submodule ℂ M) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : M}
    (hx : x ∈ V ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S :=
  mem_of_invariant_of_mem_sup_of_piece_zero d
    (d.piece_eq_bot 0 fun hmem => hodd 0 hmem ⟨0, rfl⟩) S hS hx hinv
```

**[M]** The old consumer contract is recovered **exactly** — same name, same explicit and
implicit argument order, same conclusion — so **[S]** all three call sites
(`MassDimLTEight.lean:293, 305`; `FermionGaugeSector/MassWeight.lean:112`) are untouched. The
corollary's proof is the single line that currently sits at line 187.

**[M] Is the stronger version worth having?** Honest answer: **no current consumer needs it**,
and AGENTS.md warns against adding results that are trivial rearrangements. The case for it is
that it is the *actual* theorem (the parity is a sufficient condition for a hypothesis about
one submodule being `⊥`), it costs one line, and it would apply to a decomposition that
redundantly declares `0` in its support — a situation §3.4 shows the library's own constructors
can produce. The case against is that it is speculative API. **[M] I do not presuppose that
this new API is necessary**; I record it as a small optional improvement for the human to
accept or decline, and the required scope in §5 works either way.

### 4.3 Other risks

**[M] R1 — the `ℂ`/`K` seam.** `mem_of_invariant_of_mem_sup_of_odd_supp` is at `ℂ` for an
accidental reason (§2.3) while everything around it is at `K`. If it moves into
`WeightGrading.lean` unchanged, that file will have one `ℂ`-only declaration among
`K`-generic ones. Generalising requires a `K`-form of `quotient_apply_mkQ` (or an inline
`rfl`), which is cheap; but it is a *change*, and every consumer is at `ℂ`, so the human may
prefer to leave it. Flagged, not decided.

**[M] R2 — `WeightGrading.lean` would grow.** 246 lines today; the required scope in §5 adds
roughly 100–120, the full 18-declaration consolidation roughly 200–220. Still far below any
file-size limit, but it changes the file from "the definition and its independence" into "the
definition and its whole API". **[S]** `docs/ReviewGuidelines.md` bands a 100–200 line PR as
"large, okay but try to break up", so the full consolidation should be split.

**[M] R3 — the `@[simp]` accessors.** `mulOfMul_supp` (`@[simp]`, line 113) and `sup_supp`
(`@[simp]`, line 150) are `rfl` lemmas that would enter a much more widely imported file. A
`simp` lemma that unfolds `supp` to a `Finset` sum or union will now fire in contexts that never
saw it before. **[M]** Low risk (both sides are already-normal forms) but a real behavioural
change, and the kind of thing that shows up as an unexpected `simp` failure three files away.

**[M] R4 — nothing in this extraction is verifiable end to end right now.** §1.1: every
consumer is behind the blocker. Even a perfect extraction can only be validated against
*restated* applications until the blocker is resolved. §6 separates these two kinds of evidence
explicitly.

---

## 5. Bounded extraction proposal

### 5.1 Destination

**[M] Recommended home: `Physlib/Relativity/LorentzGroup/Boosts/WeightGrading.lean`.**
It is the file that defines `WeightDecomposition`, `copy` and `sup`; it is the only one of the
candidates that builds today (§1.1); its existing variable block is exactly the generality the
candidates want; and **[S]** it already imports `Boosts/Axis.lean` and
`Mathlib.Algebra.Group.Pointwise.Finset.Basic`, covering two of the four import needs (§2.2).
AGENTS.md's "place results in the appropriate existing file" points here and no other
mathematical or import consideration points elsewhere.

**[M] One declaration should not go there: `mul_le_iSup_convolution`** (§3.2). It has no
Lorentz content at all — no `rep`, no axis, no weight. Two options: (a) put it in
`WeightGrading.lean` anyway, in a small section marked as a submodule-only preliminary, with a
comment that it is upstreamable; (b) put it in `Physlib/Mathematics/` — there is no obviously
right file there, so this would mean a new one. **[M] I recommend (a)**: a new file for one
four-line lemma is worse than a clearly-marked section, and AGENTS.md defaults against new
files.

**[M] Import direction.** `WeightGrading.lean` must not import any Standard Model file, and
nothing in the proposal makes it do so. The one thing that would is the `quotient_apply_mkQ`
dependency, which points at `Invariants/LorentzCovariance.lean` (not SM, but a large and
irrelevant subtree) — inline it (§2.3).

### 5.2 Required work

Ordered, each step independently reviewable. **[M]** Steps 1–2 are a single coherent concept
("the product of two boost-weight decompositions"); step 3 is a second
("odd boost weight admits no invariant"); AGENTS.md's one-concept-per-PR rule suggests two PRs.

**PR A — the convolution.**

1. Add to `WeightGrading.lean` section C, after `sup_piece`: `sup_supp` (moved verbatim from
   `MassDimLTEight.lean:151`, shedding the inert `[Ring A] [Algebra K A]`), then a new section
   with `variable {A : Type*} [Ring A] [Algebra K A]` holding `mul_le_iSup_convolution`
   (strengthened to an equality per §3.2, inert typeclasses dropped), `mulOfMul`,
   `mulOfMul_supp`, `exists_add_eq_of_mem_mulOfMul_supp`, `two_dvd_of_mem_mulOfMul_supp`,
   `not_two_dvd_of_mem_mulOfMul_supp`.
2. Delete those six-plus-one from `MassDimLTEight.lean:53–152`; the file keeps its
   `namespace Lorentz.BoostWeight.WeightDecomposition` block only if step 3 is deferred,
   otherwise the whole block goes and the file starts at `namespace StandardModel`.
3. Add the needed Mathlib import(s) for `Submodule` multiplication (§2.2, probe P0a); update
   `WeightGrading.lean`'s module docstring, which **[S]** currently says at lines 27–29 that the
   product *"is built where it is used, in `CovAlgebraRealization/YukawaSector/MassDimLTEight.lean`"*
   — that sentence becomes false and must be replaced.
4. Fix overclaims O1, O3, O4, O5 (§4.1).

**PR B — the parity exclusion.**

5. Move `map_boostWeightSubmodule_le` and `mem_of_invariant_of_mem_sup_of_odd_supp` into
   `WeightGrading.lean` section B (they belong with
   `mem_of_mem_iSup_of_boostWeight_zero`, which the latter calls).
6. Inline `quotient_apply_mkQ` (§2.3) so that `WeightGrading.lean` gains no import.
7. Delete the corresponding block from `MassDimLTEight.lean`; the file then begins at
   `namespace StandardModel` and holds only Standard Model content (sections C, D, E), which is
   what its name promises.

**[M] Consumer impact: none.** All nine declarations keep their full names
(`Lorentz.BoostWeight.WeightDecomposition.*`) because the namespace is already the general one
— **[S]** `MassDimLTEight.lean:53` opens exactly `namespace Lorentz.BoostWeight.WeightDecomposition`.
Moving the declarations between files does not change a single call site, provided the consumer
files still reach `WeightGrading.lean`, which **[S]** they do
(`HiggsAlgebraCovRealization/Basic.lean:14` imports it and everything downstream inherits it).
**[M]** The only things that change are the two `@[simp]` lemmas' visibility (risk R3) and the
`hmul` argument, which stays in the same position.

### 5.3 Optional improvements, explicitly outside the required scope

| # | improvement | recommendation |
| --- | --- | --- |
| I1 | Strengthen `mul_le_iSup_convolution` to an equality and use `le_antisymm` in `mulOfMul.iSup_piece` (§3.2) | **Do** — it removes a duplicated argument. Folded into PR A above. |
| I2 | Split out `mem_of_invariant_of_mem_sup_of_piece_zero` with the odd-support corollary (§4.2) | **Offer** — one line, recovers the old contract exactly, but no consumer needs it. Human's call. |
| I3 | Generalise the parity theorem from `ℂ` to `K` (§2.3, R1) | **Offer** — makes it match its neighbours. Needs a `K`-form of the `rfl` helper. |
| I4 | Move the other nine general declarations (`ofTrivialAction`×3, `ofWeightBasis`, `iSupFintype`×2, `ofAxisTwo`, `iSupOfSupp`×2) into `WeightGrading.lean` (§2.0, §2.2) | **Follow-on PR C.** Independently worthwhile — it unblocks `trivialWeightDecomposition` as a one-liner (§3.3) and would let `iSupFintype` become a corollary of `iSupOfSupp`. Out of this task's scope. |
| I5 | Relocate `IsDerivativeCollection` and `boostDecomp` (`HiggsAlgebraCovRealization/Basic.lean:1137–1209`) | **Not now.** They are general in content — **[S]** they use only `B`, `repLorentz`, `RotatesIndices` and `lightConeDeriv`, and the surrounding `[Ring B] [Algebra ℂ B]`, `rep`, `massWeightPoly` are inherited and unused — but their prerequisites live in `Relativity/LightConeDeriv.lean`, which `WeightGrading.lean` does **not** import. A different destination and a bigger decision. |
| I6 | Generalise `mul_le_iSup_convolution`'s index from `ℤ` to `AddMonoid ι` | **Do not.** Nothing needs it (§3.2). |
| I7 | Introduce a graded-algebra structure | **Do not** (§3.1). It would require equality where the library has containment. |
| I8 | Add a minimality field to `WeightDecomposition.supp` | **Do not** (§3.4). It would break three existing constructors. |

**[M] Estimated required diff:** PR A roughly +95/−85, PR B roughly +40/−35, plus docstrings —
each within `docs/ReviewGuidelines.md`'s "average" band, each a single concept.

---

## 6. Post-bump Lean experiment checklist

Each probe is a stop/go gate. Probes are labelled **[generic]** if they can run without any
Standard Model file, and **[blocked]** if they require the blocker to be resolved first.

| # | probe | kind | pass criterion | stop/go |
| --- | --- | --- | --- | --- |
| **P0a** | **Destination-only imports.** In a scratch copy of `WeightGrading.lean` on 4.34.0, add the import(s) needed for `Submodule` multiplication (`Mathlib.Algebra.Algebra.Operations` or its 4.34.0 successor) and, if I4 is in scope, for `Module.Basis`. Build that file alone. | generic | Elaborates; `lake exe importGraph`-style inspection shows no new `Physlib/Particles/` edge. | **Stop** if `WeightGrading.lean` acquires any Standard Model dependency. That is the invariant the whole extraction exists to protect. |
| **P0b** | **The pointwise import.** Confirm that `Mathlib.Algebra.Group.Pointwise.Finset.Basic` (line 11) is what supplies `+ : Finset ℤ → Finset ℤ → Finset ℤ`, and that it is currently unused (§2.2). | generic | `mulOfMul.supp` elaborates with no further import. | Go either way; this only affects whether the PR adds or removes an import line. |
| **P1** | **Convolution, standalone.** State `mul_le_iSup_convolution` as an **equality** (§3.2) and `mulOfMul` in the destination, with the §5.2 variable block. Build. | generic | Both elaborate with no hypothesis beyond `hmul` and the two decompositions. | **Stop** if `hmul` proves insufficient — that would contradict the handoff's central claim and must be reported, not worked around by adding a representation hypothesis. |
| **P2** | **Noncommutative factor order.** With `A` a noncommutative ring (e.g. `Matrix (Fin 2) (Fin 2) ℂ` as a `ℂ`-algebra), check that `mulOfMul d₁ d₂ : WeightDecomposition rep i (V * W)` and that `mulOfMul d₂ d₁` has type `… (W * V)`, and that these do not unify. Also check the **left-nested** triple `mulOfMul hmul (mulOfMul hmul d₁ d₂) d₃ : … (V * W * U)` elaborates (§3.1). | generic | Types are as stated; the triple elaborates against `V * W * U` without an explicit `mul_assoc` rewrite. | **Stop** if the triple needs a rewrite: `higgsSqFermionBoostWeight` (`MassDimLTEight.lean:252`) and any analogue depend on it. |
| **P3** | **Redundant and empty support.** `d` with `supp := {0, 1}` but `piece 1 = ⊥`; `d` with `supp := ∅` (so `V = ⊥`); and `mulOfMul` of an empty-support factor with a nonempty one. Check `supp` values and that `piece_eq_bot` is still provable. | generic | `∅ + s = ∅`; the redundant entry is accepted; no lemma in the moved set concludes `piece k ≠ ⊥` from `k ∈ supp`. | Go. Confirms §3.4 in Lean rather than on paper. |
| **P4** | **Parity, standalone.** State `map_boostWeightSubmodule_le` and `mem_of_invariant_of_mem_sup_of_odd_supp` in the destination with `quotient_apply_mkQ` **inlined** (§2.3). Build. | generic | Elaborates; the destination still has no `Invariants/` import. | **Stop** if inlining fails — then `quotient_apply_mkQ` must move to a lower file instead, which is a separate decision. |
| **P5** | **Zero-piece / odd-support conclusion** (only if I2 is accepted). State `mem_of_invariant_of_mem_sup_of_piece_zero` and derive `mem_of_invariant_of_mem_sup_of_odd_supp` from it with the §4.2 one-liner. | generic | The corollary's statement is **verbatim** the current one, including implicit/explicit argument order. | Go. If the corollary's signature drifts at all, drop I2 rather than change consumers. |
| **P6** | **`K`-genericity** (only if I3 is accepted). Restate the parity theorem at `{K} [Field K] [Algebra ℝ K]`. | generic | Elaborates; the `ℂ` instance still typechecks at every old call shape. | Go / drop I3. |
| **P7** | **Restated application shapes.** Reproduce, without importing any Standard Model file, the four consumer shapes: `mulOfMul` of two abstract decompositions with even/odd support hypotheses; the nested `(even ⊞ even) ⊞ odd`; `((d₁.sup d₂).sup d₃)` with a `Finset.mem_union` case split (mirroring `MassDimLTEight.lean:307–313`); and the final `mem_of_invariant_of_mem_sup_of_odd_supp` application. | generic | All four elaborate against the moved declarations. | Go. **This is the furthest the extraction can be validated while the blocker stands.** Record explicitly that it is *restated shapes*, not production consumers. |
| **P8** | **Principal axiom audit.** `#print axioms` on `mulOfMul`, `mul_le_iSup_convolution`, `mulOfMul_supp`, `exists_add_eq_of_mem_mulOfMul_supp`, `two_dvd_of_mem_mulOfMul_supp`, `not_two_dvd_of_mem_mulOfMul_supp`, `sup_supp`, `map_boostWeightSubmodule_le`, `mem_of_invariant_of_mem_sup_of_odd_supp`. | generic | `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`. | **Stop** on anything else; AGENTS.md requires such declarations to be tagged. |
| **P9** | **Original production consumers.** Build, unchanged: `CovAlgebraRealization/YukawaSector/MassDimLTEight.lean` (sections C–E), `CovAlgebraRealization/FermionGaugeSector/MassWeight.lean`, `AlgebraRealization/HiggsAlgebraCovRealization/DerivSubmodule/BoostWeightDecomposition.lean`, `IsFermionSector/DerivSubmodule/BoostWeightDecomposition.lean`, `IsGaugeSector/DerivSubmodule/BoostWeightDecomposition.lean`. | **blocked** | All five elaborate with no call-site edits. | **This is the real acceptance gate and it cannot be reached until `StandardModel.JetAlgebra.SectorEquiv.Basic` builds.** Do not repair that blocker as part of this work; record the obligation as owed. |

### 6.1 Blocked production consumers, named

**[S]** The validation obligations that the blocker prevents, listed so they can be discharged
later rather than forgotten:

| consumer | declarations it exercises | file:line |
| --- | --- | --- |
| `higgsFermionBoostWeight`, `odd_higgsFermionBoostWeight_supp` | `mulOfMul`, `not_two_dvd_of_mem_mulOfMul_supp` | `MassDimLTEight.lean:236–248` |
| `higgsSqFermionBoostWeight`, `odd_higgsSqFermionBoostWeight_supp` | nested `mulOfMul`, `two_dvd_…`, `not_two_dvd_…` | `MassDimLTEight.lean:252–270` |
| `mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup` | `mem_of_invariant_of_mem_sup_of_odd_supp` | `MassDimLTEight.lean:287–293` |
| `…_seven_sup` | `sup`, `sup_supp`, `mem_of_invariant_of_mem_sup_of_odd_supp` | `MassDimLTEight.lean:299–313` |
| `gaugeFermionBoostWeight`, `odd_gaugeFermionBoostWeight_supp`, `mem_of_lorentz_invariant_sectorMassWeight_gauge_fermion_seven_sup` | `mulOfMul`, `not_two_dvd_…`, `mem_of_invariant_of_mem_sup_of_odd_supp` | `FermionGaugeSector/MassWeight.lean:78–113` |
| `higgsValueWeight`, `barHiggsValueWeight`, `higgsSubmoduleBoostWeight_piece`, `barHiggsSubmoduleBoostWeight_piece` | `ofTrivialAction`, `ofTrivialAction_piece` | `Higgs BWD:125–132, 238–267` |

**[M]** Until P9 runs, the strongest honest claim available is: *the moved declarations
elaborate in a Standard-Model-free setting and support restated versions of every application
shape the production consumers use.* That is not the same as the consumers building, and this
report does not conflate them.

---

## 7. Unresolved choices for human judgement

1. **Destination for `mul_le_iSup_convolution`** — a marked section in `WeightGrading.lean`
   (recommended) or a new `Physlib/Mathematics/` file (§5.1).
2. **I2, the zero-piece split** — genuinely optional, one line, no consumer (§4.2). I have not
   presupposed it is necessary.
3. **I3, `ℂ` → `K`** — consistency with the destination file versus leaving a working
   declaration alone (§2.3, R1).
4. **Scope of PR C (I4)** — whether the other nine general declarations move in the same
   campaign. **[M]** They should, eventually; the `trivialWeightDecomposition` duplication
   (§3.3) is the concrete payoff.
5. **Standing preference against cross-file moves.** Earlier sessions recorded a preference
   that work on a Lean file stay within that file and not relocate results. This proposal is
   inherently a cross-file move and needs an explicit go-ahead. **[M]** If that preference
   stands, the useful residue is the documentation fix (§4.1, O1/O3/O4/O5) and the
   `mul_le_iSup_convolution` strengthening (I1), both of which are in-file changes and both of
   which are worth doing on their own.
6. **Sequencing against the 4.34.0 bump.** Every probe in §6 is a 4.34.0 probe. **[M]** Since
   `WeightGrading.lean` is not behind the blocker, PR A and PR B could in principle be prepared
   against 4.33.0 and rebased — but the handoff forbids running anything here, so this is a
   scheduling question for the human, not a finding.

---

## 8. What this report does not establish

No Lean was elaborated. No build, cache fetch, lint, benchmark, timing or axiom audit was run,
and none is reported. Every Lean fragment above is an uncompiled sketch. The import-closure and
usage facts are from static text analysis, which sees `import` lines and identifier occurrences
but not elaboration: in particular, "no pointwise operation appears in `WeightGrading.lean`"
(§2.2) is a grep result, not a proof that the import is removable, and "`hodd` is used once"
(§4.2) is a textual count of a proof I could not elaborate. Mathlib claims hold only for rev
`db584cd6` (v4.33.0); absence there is not absence from 4.34.0, and presence there is not
presence in 4.34.0. No assumption is made about whether
`StandardModel.JetAlgebra.SectorEquiv.Basic` builds on any other revision, and I neither
repaired nor attempted to build it. I claim sufficiency of the hypotheses discussed, never
optimality or minimality. Human review, then the §6 probes on 4.34.0, are the acceptance gate
before implementation.
