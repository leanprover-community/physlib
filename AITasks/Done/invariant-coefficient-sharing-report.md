# Shared invariant-coefficient lifting: investigation report

Read-only investigation. No Lean was elaborated, built, linted or probed; no Lean file,
import, dependency, other report or roadmap file was edited. The only file added by this
task is this report.

Claims below are tagged:

- **[S]** source-verified — read directly from the files and line numbers cited.
- **[M]** mathematical deduction from **[S]** facts, done on paper, not machine-checked.
- **[K]** uncompiled Lean sketch — illustrative only, never elaborated.

---

## 1. Source provenance and scope inspected

**[S]** Working tree `/Users/josephsmith/LocalGithub/JTSphyslib`, branch `AddPotentialAlgebra`.

| item | value |
| --- | --- |
| HEAD | `7db2baf182932c35fcb5ed5d00b5f321049ae906` (`docs: add AI task folder and some AI analysis tasks`, 2026-09-21) |
| handoff reference commit | `5589e23dde62da95d6f7e4d9467cf63ecc111680` |
| relation | reference is an ancestor of HEAD (`git merge-base --is-ancestor` succeeds) |
| `git diff 5589e23d..HEAD --stat` | `AITasks/Done/.gitkeep`, `AITasks/ToDo/boost-weight-extraction.md`, `AITasks/ToDo/invariant-coefficient-sharing.md` — **no `.lean` file differs** |
| dirty files at start | `Draft.md` only (3 insertions, 1 deletion; not inspected for content, not a Lean source) |
| `lean-toolchain` | `leanprover/lean4:v4.33.0` |
| `lake-manifest.json` | manifest version `1.2.0`; `mathlib` rev `db584cd6d46c92f209a44c0f1c829460d327499d`, inputRev `v4.33.0` |
| git worktrees | one — this checkout is not a bump workspace and contains no 4.34.0 material |

So **[S]** every declaration named in the handoff is at the reference revision, byte for byte.
No declaration had to be relocated, and no material difference from the handoff description
was found. All Mathlib references below were read from `.lake/packages/mathlib` at rev
`db584cd6` (v4.33.0) and are asserted **only** for that snapshot.

Files read in full: `Physlib/Relativity/LorentzGroup/Invariants/Basic.lean` (341 lines),
`Physlib/Particles/StandardModel/GaugeGroup/Invariants/Basic.lean` (233),
`Physlib/Mathematics/LinearCombination.lean` (40). Read in relevant part:
`Physlib/Relativity/LorentzGroup/Invariants/LorentzCovariance.lean`,
`Physlib/Relativity/LorentzGroup/Invariants/IsLeftRightWeyl.lean`,
`Physlib/Particles/StandardModel/GaugeGroup/Invariants/IsSU2BiFundamental.lean`,
`.../IsSU3FunAntiFun.lean`, `Physlib/Particles/StandardModel/Peeling.lean`.
Consumer inventory obtained by repository-wide grep, not by the handoff's starting list.
Import closures computed by a static parse of `import` lines (a script in the scratchpad,
not added to the repository).

**Not inspected:** the interiors of `IsSU2Adjoint`, `IsSU2BiAdjoint`, `IsSU3Adjoint`,
`IsSU3BiAdjoint`, `IsSU2QuadFundamental`, `IsSU3BiFundamental`, `IsU1BiAdjoint`,
`IsBiLeftWeyl`, `IsVectorLeftRightWeyl` beyond their call sites; the `Rank*` Lorentz files.

---

## 2. Exact contract comparison

### 2.1 The two statements, transcribed with their effective context

**[S]** Lorentz — `Physlib/Relativity/LorentzGroup/Invariants/Basic.lean`, file-level
variable at line 52, section variable at line 62, theorem at lines 79–85:

```
variable {B : Type*} [AddCommGroup B] [Module ℂ B]          -- line 52
section Complement
variable {ι : Type} [Fintype ι] {G : Type*}                 -- line 62

theorem Lorentz.Invariants.exists_invariantCoeff
    (T : ι → B) (φ : G → B →ₗ[ℂ] B)
    (A : G → (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hφ : ∀ (g : G) (c : ι → ℂ), φ g (∑ i, c i • T i) = ∑ i, A g c i • T i)
    (hA : ∀ g : G, ∃ g' : G, ∀ u v : EuclideanSpace ℂ ι,
      ⟪u, WithLp.toLp 2 (A g v.ofLp)⟫_ℂ = ⟪WithLp.toLp 2 (A g' u.ofLp), v⟫_ℂ)
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c
```

**[S]** Gauge — `Physlib/Particles/StandardModel/GaugeGroup/Invariants/Basic.lean`,
file-level variable at line 48, section variable at lines 93–94, theorem at 141–145:

```
variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ι : Type*} [Fintype ι]   -- line 48
section Complement
variable {G : Type*} [Group G] (T : ι → B) (φ : G → B →ₗ[ℂ] B)
  (A : G → (ι → ℂ) →ₗ[ℂ] (ι → ℂ))                                            -- lines 93–94

theorem StandardModel.Family.exists_invariant_coeff
    (hφ : ∀ g (c : ι → ℂ), φ g (∑ i, c i • T i) = ∑ i, A g c i • T i)
    (hA : ∀ g (c d : ι → ℂ), ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i)
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c
```

### 2.2 Difference table

| # | aspect | Lorentz `exists_invariantCoeff` | gauge `exists_invariant_coeff` | verdict |
| --- | --- | --- | --- | --- |
| 1 | `B` | `Type*`, `[AddCommGroup B] [Module ℂ B]` | identical | same |
| 2 | `ι` universe | `Type` (universe 0) | `Type*` | **gauge is more general** |
| 3 | `ι` finiteness | `[Fintype ι]` | `[Fintype ι]` | same |
| 4 | `G` | bare `{G : Type*}`, no class | `{G : Type*} [Group G]` | **Lorentz is more general** |
| 5 | `A` | `G → (ι → ℂ) →ₗ[ℂ] (ι → ℂ)` | identical | same |
| 6 | `hφ` (the law) | `∀ g c, φ g (∑ i, c i • T i) = ∑ i, A g c i • T i` | character-for-character identical | same |
| 7 | `hA` (the adjoint) | `∀ g, ∃ g', ∀ u v : EuclideanSpace ℂ ι, ⟪u, A g v⟫ = ⟪A g' u, v⟫` | `∀ g c d : ι → ℂ, ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i` | **the only real difference** |
| 8 | `hx` | `x ∈ ⨆ i, ℂ ∙ T i` | identical | same |
| 9 | `hinv` | `∀ g, φ g x = x` | identical | same |
| 10 | conclusion | `∃ c, x = ∑ i, c i • T i ∧ ∀ g, A g c = c` | character-for-character identical | **same, including ordering** |
| 11 | argument order | `T φ A hφ hA hx hinv` | `T φ A hφ hA hx hinv` (T, φ, A via section variables) | same |
| 12 | naming | camel `exists_invariantCoeff` | snake `exists_invariant_coeff` | cosmetic |

**Conclusion-ordering caveat.** The handoff asks about conclusion ordering. The two
*principal* statements agree exactly. The flip is one level up, in the Lorentz matrix
wrapper: **[S]** `exists_invariantCoeff_matrix` (Basic.lean:166–176) concludes
`∃ c, (∀ g, actMat (M g) c = c) ∧ x = ∑ i, c i • T i` — invariance first — and its proof
ends with `exact ⟨c, hinvc, hc⟩`, i.e. it exists only to swap the conjuncts.
**[S]** `exists_isInvariantCoeff_of_mem_span` (267–278) and
**[S]** `IsLorentzCovariant.exists_isInvariantCoeff_of_mem_componentSpan`
(`LorentzCovariance.lean:155–159`) keep that order. The gauge callers all destructure as
`obtain ⟨c, rfl, hc⟩` (7 sites, §5.1), the Lorentz Weyl callers as `obtain ⟨c, hc, hx'⟩`.
Any shared statement must therefore fix one order; the *existing* shared order (both
principal theorems) is `x = … ∧ invariance`, and the flip lives only in the matrix wrapper,
which is Lorentz-only and can keep flipping.

### 2.3 What `hA` actually assumes

This is the crux, and the comments are misleading in both files.

**[S]** The gauge file's section-B prose (lines 84–87) says: *"One property of `A` is needed:
`A g⁻¹` is the adjoint of `A g` for the standard inner product on coefficients, which is to
say that `A` is unitary."*

**[M]** Two corrections. (a) "`A g⁻¹` is the adjoint of `A g`" does **not** say `A` is
unitary; it says `A g` has an adjoint inside the family. It coincides with unitarity only
if one additionally knows `A` is a homomorphism and `A 1 = 1`, and **[S]** neither is
assumed anywhere in the statement or used anywhere in the proof. (b) `[Group G]` is used
*solely to be able to write `g⁻¹` in `hA`*: **[S]** reading the proof (lines 146–169), the
group structure never appears — `hA` is applied once, at `g`, inside `inner_actₗ`
(line 165), and the element `g⁻¹` it produces is fed straight to `hKstab _ u hu` (line 166),
which accepts *any* element of `G`. No multiplication, no `inv_inv`, no `one_mul`.

**[M]** Therefore the gauge hypothesis is strictly the special case of the Lorentz
hypothesis in which the witness `g'` is chosen to be `g⁻¹`, and the `[Group G]` instance is
not a mathematical prerequisite of the theorem but a prerequisite of *writing* that
particular choice.

**[S] Decisive counterevidence against standardising on `g⁻¹`.** The Lorentz families are
genuinely not unitary, and the library says so: Basic.lean:154–155 documents `inner_actMat`
with *"The action is not unitary, and is not used to be."* Concretely, the witnesses
supplied by the three Lorentz call sites are conjugate transposes, not inverses:

- `exists_isInvariantCoeff_of_mem_span` (Basic.lean:275–277) supplies
  `dagger g = ⟨g.1ᴴ, …⟩` (`dagger`, line 217);
- `IsLeftRightWeyl.exists_isInvariantCoeff_of_mem_componentSpan` (lines 134–137) supplies
  `Invariants.dagger g`;
- `IsBiLeftWeyl` (line 139 ff.) likewise.

For `g ∈ SL(2,ℂ)`, `g†  ≠ g⁻¹` in general. So a shared statement phrased with `g⁻¹` would
be **unusable** by the Lorentz side. The existential-witness form is not gratuitous
generality; it is the form the existing Lorentz applications need.

### 2.4 Which laws are assumed, which follow, which are unused

**[M]**, from reading both proofs:

| property of `A` | status |
| --- | --- |
| `A g` linear | assumed (it is a `→ₗ[ℂ]`); used for `hKstab` and for the `Kᗮ` decomposition |
| `A` multiplicative / a representation | **never assumed, never used** — `A` is a bare function `G → End` |
| `A 1 = 1` | **never assumed, never used** |
| `A g` invertible | **never assumed, never used** |
| `A g` unitary / isometric | **never assumed, never used** (the gauge docstring's claim is not a hypothesis) |
| adjoint of `A g` lies in the family | assumed; the *only* nontrivial hypothesis on `A` |
| `φ` multiplicative or a representation | **never assumed** — `φ : G → B →ₗ[ℂ] B` is a bare function; the callers pass `fun g => repLorentz g`, discarding the monoid-hom structure |
| `T` linearly independent | **never assumed**; explicitly disclaimed in the Lorentz docstring (lines 77–78: *"Nothing is claimed about uniqueness, the components being possibly dependent."*) |

**[M]** So both theorems are about an arbitrary *set* of linear maps closed under adjoints
in a weak (witness-wise) sense, not about a group representation.

### 2.5 Where complex scalars, finiteness and `WithLp` are actually needed

**[M]**, tracing the proofs:

- **Inner product / orthogonality**: needed only on the *coefficient* space
  `EuclideanSpace ℂ ι = WithLp 2 (ι → ℂ)`. The two Mathlib facts consumed are
  **[S]** `Submodule.exists_add_mem_mem_orthogonal`
  (`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:427`, needs
  `[K.HasOrthogonalProjection]`) and **[S]** `Submodule.inf_orthogonal_eq_bot`
  (`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean:98`).
- **`[Fintype ι]`** does three jobs: it makes `∑ i` meaningful; it makes
  `EuclideanSpace ℂ ι` finite-dimensional hence complete, which supplies
  `HasOrthogonalProjection` through **[S]**
  `HasOrthogonalProjection.ofCompleteSpace` (`Projection/Basic.lean:54`); and it makes
  `Fintype.range_linearCombination` available for the `hx` unpacking.
- **`ℂ`**: used only as an `RCLike` field carrying the standard inner product. **[M]** The
  argument is verbatim valid over `𝕜` with `[RCLike 𝕜]`, since every Mathlib lemma used is
  stated at `RCLike`. I do **not** recommend taking that generality (§3.4).
- **`WithLp.toLp 2` / `.ofLp`**: pure type-level plumbing, as the Lorentz docstring says
  (Basic.lean:65). No mathematical content.
- **`B`**: **[S]** carries *no* inner product, *no* norm and *no* finiteness in either
  statement, and must not acquire any. `[AddCommGroup B]` (rather than `AddCommMonoid`) is
  genuinely used: **[M]** step `h1` applies `map_sub` to `contractₗ`, which needs subtraction
  in the codomain.

### 2.6 Boundary cases, on paper

**[M] Dependent family.** The whole point. If the `T i` satisfy relations, `K = ker(contract)`
is a nonzero subspace of coefficient space and the *given* coefficient `c` need not be
invariant; the theorem replaces it by its `Kᗮ`-component. Uniqueness is not claimed and does
not hold: any `c + κ` with `κ ∈ K` represents the same vector. **[M]** A stronger true
statement the proof in fact establishes, but does not expose: the produced `c` is the unique
*minimum-norm* representation of `x`, being the orthogonal projection of an arbitrary one
onto `Kᗮ`. Nothing currently needs this.

**[M] Empty index.** For `ι` empty, `⨆ i : ι, ℂ ∙ T i = ⊥`, so `hx` forces `x = 0`; `ι → ℂ`
is a subsingleton, so the unique `c` satisfies both conjuncts trivially. No hypothesis is
vacuously violated and the statement is true but content-free. **[M]** The proof also goes
through unchanged, since `K = ⊥ = ⊤` in the zero space and `Kᗮ` is the same zero space.

**[M] Degenerate `T` (all `T i = 0`).** `K = ⊤`, `Kᗮ = ⊥`, the produced `c` is `0`, and the
theorem says `x = 0` with `A g 0 = 0` — true by linearity of `A g`.

---

## 3. Common proof mechanism, library machinery and the candidate statement

### 3.1 Step-by-step correspondence

The two proofs are the same proof. Line-by-line map, all **[S]**:

| step | Lorentz `Invariants/Basic.lean` | gauge `GaugeGroup/Invariants/Basic.lean` |
| --- | --- | --- |
| unpack `hx` into a coefficient `c` | 87–90 (inline `span_range_eq_iSup` + `Fintype.range_linearCombination`) | 146 (via the extracted `mem_iSup_span_singleton_iff`, 58–61 — the same three rewrites) |
| the contraction map `q` | `contractₗ` 66–72 | `contractₗ` 98–104 — **identical definition body** |
| intertwining `q ∘ A g = φ g ∘ q` | `hcontr`, 91–93 | `hΦ`, 147–148 |
| `K := ker q` | 94 | 149 |
| `K` is `A`-stable | `hKstab`, 95–99 | `hKstab`, 150–153 |
| split `c = k + k'`, `k ∈ K`, `k' ∈ Kᗮ` | 100 | 154 |
| `x = q k'` (the `K` part is invisible) | `hx'`, 101–103 | `hx'`, 155–158 |
| `A g k' − k' ∈ K` (uses `hinv`) | `h1`, 105–106 | `h1`, 160–161 |
| `A g k' ∈ Kᗮ` (uses the adjoint) | `h2`, 107–111 | `h2`, 162–166 |
| `K ⊓ Kᗮ = ⊥` kills the difference | 112–115 | 167–169 |

**Why the coefficient maps preserve `K`** **[M]**: if `q u = 0` then
`q (A g u) = φ g (q u) = φ g 0 = 0`. Only linearity of `φ g` and the intertwining law are
used; no property of `A` beyond linearity.

**Why the adjoint condition makes `Kᗮ` invariant** **[M]**: let `g'` witness the adjoint of
`g`. For `u ∈ K`, `⟪u, A g k'⟫ = ⟪A g' u, k'⟫ = 0`, because `A g' u ∈ K` (stability applied at
`g'`) and `k' ∈ Kᗮ`. Note this consumes stability of `K` **at the witness `g'`, not at `g`** —
which is exactly why `hA` must range over a family closed under adjoints, and why a single
`g` with an adjoint outside the family would not do.

**Why replacing a preimage by its `Kᗮ` component preserves the image** **[M]**: `q` is linear
and kills `K`, so `q (k + k') = q k'`.

**Why the change is zero** **[M]**: `A g k' − k'` lies in `K` (by `h1`, using invariance of
`x`) and in `Kᗮ` (by `h2` and `k' ∈ Kᗮ`, which is a subspace). `K ⊓ Kᗮ = ⊥` in an inner
product space over `RCLike`, so the difference vanishes: `A g k' = k'`.

### 3.2 Invariant expression vs. invariant coefficient description

**[M]** The distinction the theorem exists to bridge. "`x` is invariant" is a statement about
a vector of `B`. "`c` is invariant" is a statement about a point of `ι`-space. The map
`c ↦ ∑ i, c i • T i` is equivariant but in general neither injective nor surjective onto the
invariants of its image *pointwise*: an invariant vector can be written with wildly
non-invariant coefficients (add any `κ ∈ K`, then move it — `A g κ` is another element of `K`,
generally `≠ κ`). The theorem says the fibre of an invariant vector always *contains* an
invariant point, which is what lets the downstream classification argue entirely in the
finite space `ι → ℂ`. It does **not** say the fibre consists of invariant points, and no
downstream file may assume that.

### 3.3 Existing Mathlib machinery for the individual steps

All **[S]**, read at mathlib rev `db584cd6` (v4.33.0). These are *available at the inspected
snapshot*; nothing here is a claim about 4.34.0.

| step | Mathlib declaration | file:line | context needed |
| --- | --- | --- | --- |
| split into `K ⊕ Kᗮ` | `Submodule.exists_add_mem_mem_orthogonal` | `Analysis/InnerProductSpace/Projection/Basic.lean:427` | `[K.HasOrthogonalProjection]` |
| `HasOrthogonalProjection` | `HasOrthogonalProjection.ofCompleteSpace` | `Projection/Basic.lean:54` | `[CompleteSpace K]` |
| `K ⊓ Kᗮ = ⊥` | `Submodule.inf_orthogonal_eq_bot` | `Analysis/InnerProductSpace/Orthogonal.lean:98` | — |
| pairing against `Kᗮ` | `Submodule.inner_right_of_mem_orthogonal` | `Orthogonal.lean:64` | — |
| **identify an adjoint from the pairing law** | `LinearMap.eq_adjoint_iff` | `Analysis/InnerProductSpace/Adjoint.lean:612` | `[FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]` |
| **`Kᗮ` invariant under `T` when `K` invariant under `T†`** | `Module.End.mem_invtSubmodule_adjoint_iff` | `Adjoint.lean:827` | `[FiniteDimensional 𝕜 E]` |
| same, continuous version | `ContinuousLinearMap.orthogonal_mem_invtSubmodule` | `Adjoint.lean:486` | `[CompleteSpace E]` |
| the invariance predicate | `Module.End.invtSubmodule`, `mem_invtSubmodule_iff_forall_mem_of_mem` | `Algebra/Module/Submodule/Invariant.lean:35, 58` | — |
| unpack `x ∈ ⨆ i, ℂ ∙ T i` | `Submodule.span_range_eq_iSup`, `Fintype.range_linearCombination` | (already used by both files) | `[Fintype ι]` |
| move a combination under a map given by a matrix | `LinearMap.map_sum_smul_of_forall_eq` | `Physlib/Mathematics/LinearCombination.lean:36` | Physlib, `CommSemiring R` |

**[M] There is no single Mathlib theorem that does the whole job.** The nearest relative is
`LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule`
(**[S]** `Analysis/InnerProductSpace/Semisimple.lean:30`), which handles one symmetric
operator, not a family with witnessed adjoints. Mathlib's semisimplicity results live on the
other side of the argument (they *use* this kind of complement to get semisimplicity), and
`Representation.invariants` carries no lifting theorem of this shape. So the common theorem
has to be stated in Physlib.

**[M] But the `h2` step can be delegated.** `Module.End.mem_invtSubmodule_adjoint_iff` is
exactly "`Kᗮ` is `T`-invariant iff `K` is `T†`-invariant", and `LinearMap.eq_adjoint_iff`
turns the hypothesis `hA` into the identification `A g' = (A g)†`. Both need
`[FiniteDimensional ℂ (EuclideanSpace ℂ ι)]`, which `[Fintype ι]` supplies. This would
replace roughly the five hand-written lines of `h2` in each file. This is a genuine
simplification (it names the concept instead of re-deriving it), not a generalisation; it
is listed as *optional* in §6 because it is a proof-internal change with an elaboration risk
(`LinearMap.adjoint` is noncomputable and carries `FiniteDimensional` side conditions that
must be found by instance search).

### 3.4 The smallest natural common statement

**[M] Recommendation.** The common statement is the Lorentz theorem with `ι` generalised from
`Type` to `Type*`. Nothing else changes. Specifically:

**[K]** (uncompiled sketch)

```lean
/-- An invariant of the span of a finite family is the contraction of an invariant
  coefficient function, provided the coefficient maps have all their adjoints inside the
  family: for every `g` some `g'` acts as the adjoint of `g`. The components may be
  linearly dependent, so nothing is claimed about uniqueness. -/
theorem exists_invariantCoeff_of_adjoint_mem
    {B : Type*} [AddCommGroup B] [Module ℂ B] {ι : Type*} [Fintype ι] {G : Type*}
    (T : ι → B) (φ : G → B →ₗ[ℂ] B) (A : G → (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hφ : ∀ (g : G) (c : ι → ℂ), φ g (∑ i, c i • T i) = ∑ i, A g c i • T i)
    (hA : ∀ g : G, ∃ g' : G, ∀ u v : EuclideanSpace ℂ ι,
      ⟪u, WithLp.toLp 2 (A g v.ofLp)⟫_ℂ = ⟪WithLp.toLp 2 (A g' u.ofLp), v⟫_ℂ)
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c
```

**[M] Why this and not something more abstract.** The handoff asks whether to state the
theorem about an intertwining linear map `q : E →ₗ[ℂ] B` rather than about a component
family. An abstract version would read: *given `q : E →ₗ[ℂ] B` with `E` a finite-dimensional
complex inner product space, a family `Ψ : G → E →ₗ[ℂ] E` with `q ∘ Ψ g = φ g ∘ q` and
adjoints inside the family, every `x ∈ range q` with `∀ g, φ g x = x` has a preimage fixed by
every `Ψ g`.* That is the mathematically honest form, and the component version is its
instance at `E = EuclideanSpace ℂ ι`, `q = contractₗ T`.

Arguments for the abstract form: it separates the mathematics (an intertwiner and its kernel)
from the presentation (a family of vectors); it is what one would submit to Mathlib; and
`range q` is a cleaner hypothesis than `⨆ i, ℂ ∙ T i`.

Arguments against, and why I recommend the component form anyway **[M]**: (a) *every* consumer
— 10 call sites, §5.1 — arrives with a family `T` and an `hφ` stated in `∑ i, c i • T i` form,
and would immediately need the same `hx`-unpacking and the same `contractₗ` wrapper, so the
abstract form buys a level of indirection and no shared work; (b) the `hφ` form is *not* the
naive `q ∘ Ψ g = φ g ∘ q` — it is stated pointwise on raw functions `c : ι → ℂ` and bridged to
`EuclideanSpace` by the caller-invisible `WithLp` shuffle, so an abstract statement would push
that shuffle onto every caller; (c) the handoff's own instruction is to prefer the smallest
natural statement, and the only actual difference between the two existing theorems is one
hypothesis. I therefore recommend the abstract version be *recorded as the mathematical
content in the docstring* and not separately formalised unless a third, non-family consumer
appears.

**[M] On minimality.** I claim the hypotheses are *sufficient*, and I do **not** claim they are
necessary or minimal. Two concrete non-claims: (i) I have no argument that adjoint-closure is
necessary — a family whose adjoints escape may still admit invariant lifting for other reasons
(e.g. if `K = ⊥`, the statement is trivially true with no hypothesis on `A` at all, which
already shows the hypothesis is not necessary); (ii) `[Fintype ι]` could conceivably be
relaxed to a completeness/closedness condition on `K`, but `∑ i` would have to become a
`Finsupp` sum and every consumer would change; I do not recommend it.

**[M] On `RCLike 𝕜`.** Every Mathlib lemma in the chain is stated at `RCLike`, so the proof
would go through verbatim at `𝕜`. I recommend **against** taking it: all 10 consumers are at
`ℂ`, the `hA` hypothesis for a real family would need a different bridge (`star` is trivial
over `ℝ`, so the "conjugate transpose" lemmas would degenerate), and the handoff explicitly
says to preserve the complex setting absent a directly useful relaxation. Record it as a
known free generalisation, not as scope.

---

## 4. Derivation of both specialisations

Both derivations below are **[M]** on paper with **[K]** Lean sketches. Neither was elaborated.

### 4.1 The Lorentz specialisation

**[M]** Trivial: the proposed statement *is* `exists_invariantCoeff` with `ι : Type` widened to
`Type*`. Widening a universe on an implicit type variable cannot break a caller that
instantiates it at `Type 0`, and **[S]** all three Lorentz instantiations do
(`Fin n → Fin 1 ⊕ Fin 3` at Basic.lean:267, `Fin 2 × Fin 2` at IsLeftRightWeyl.lean:131, and
the analogous type in IsBiLeftWeyl). So:

**[K]**
```lean
theorem Lorentz.Invariants.exists_invariantCoeff (T : ι → B) (φ : G → B →ₗ[ℂ] B) … :=
  exists_invariantCoeff_of_adjoint_mem T φ A hφ hA hx hinv
```
or, preferably, the name simply moves and `Invariants/Basic.lean` re-exports it.

**Unresolved:** whether `Lorentz.Invariants.exists_invariantCoeff` should survive as a name at
all. **[S]** it has **zero** consumers outside its own file (repository-wide grep: the only
reference is `exists_invariantCoeff_matrix` at line 171). So it could simply be deleted and
`exists_invariantCoeff_matrix` call the shared theorem directly. That is the smaller diff and
I recommend it; the human should confirm, since it removes a `public` name.

### 4.2 The gauge specialisation

**[M]** Take `g' := g⁻¹` and convert the raw-sum hypothesis to the inner-product one. The
conversion already exists: **[S]** `Family.inner_actₗ` (GaugeGroup/Invariants/Basic.lean:129–137)
has exactly the signature

```
inner_actₗ (hA : ∀ g (c d : ι → ℂ), ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i)
    (g : G) (a b : EuclideanSpace ℂ ι) : ⟪a, actₗ A g b⟫_ℂ = ⟪actₗ A g⁻¹ a, b⟫_ℂ
```

and **[S]** `actₗ A g b` is defined (lines 108–112) as `WithLp.toLp 2 (A g b.ofLp)` via
`LinearMap.mk`, so the two sides should be definitionally equal.

**[K]**
```lean
theorem StandardModel.Family.exists_invariant_coeff
    (hφ : ∀ g (c : ι → ℂ), φ g (∑ i, c i • T i) = ∑ i, A g c i • T i)
    (hA : ∀ g (c d : ι → ℂ), ∑ i, star (c i) * A g d i = ∑ i, star (A g⁻¹ c i) * d i)
    {x : B} (hx : x ∈ ⨆ i, ℂ ∙ T i) (hinv : ∀ g, φ g x = x) :
    ∃ c : ι → ℂ, x = ∑ i, c i • T i ∧ ∀ g, A g c = c :=
  exists_invariantCoeff_of_adjoint_mem T φ A hφ
    (fun g => ⟨g⁻¹, fun u v => inner_actₗ A hA g u v⟩) hx hinv
```

**Explicitly labelled unresolved step.** Whether `fun u v => inner_actₗ A hA g u v` typechecks
against the general `hA` *without* a `show`/`simp only [actₗ]` bridge. The target wants
`⟪u, WithLp.toLp 2 (A g v.ofLp)⟫` where `inner_actₗ` produces `⟪u, actₗ A g v⟫`. **[M]** These
should be defeq by `LinearMap.coe_mk` unfolding, but structure-eta on `LinearMap` applications
is exactly the kind of thing that elaborates or does not depending on reducibility settings.
If it does not, the fix is a one-line `simp only [actₗ, LinearMap.coe_mk, AddHom.coe_mk]` in
the wrapper — no change to either contract. This is probe P3 in §6.

**Hypothesis matching, checked item by item** **[M]**: `B`, `ι`, `Fintype ι`, `T`, `φ`, `A`,
`hφ`, `hx`, `hinv` are syntactically identical between the gauge theorem and the shared one;
`[Group G]` remains a hypothesis of the *gauge* theorem (it is needed to state `hA`) and is
simply not passed to the shared one; `hA` is discharged as above. Nothing is strengthened,
and the gauge conclusion is unchanged, so **[M]** the 7 existing `obtain ⟨c, rfl, hc⟩` call
sites are untouched.

**[M] The specialisations do not depend on the proofs they replace.** Each is a direct
application of the new theorem with a hypothesis supplied from a lemma (`inner_actₗ`) that is
independent of `exists_invariant_coeff`. **[S]** `inner_actₗ` is proved from `hA` and
`PiLp.inner_apply` alone (lines 133–137); it does not call `exists_invariant_coeff`.

---

## 5. Placement, consumers and boundary

### 5.1 Consumer inventory (repository-wide grep, **[S]**)

`Lorentz.Invariants.exists_invariantCoeff` — **0 external consumers**; used once, internally,
at `Invariants/Basic.lean:171`.

`Lorentz.Invariants.exists_invariantCoeff_matrix` — 2 consumers:
`Invariants/IsLeftRightWeyl.lean:134`, `Invariants/IsBiLeftWeyl.lean:139`
(plus internal use at `Invariants/Basic.lean:273`).

`Lorentz.Invariants.exists_isInvariantCoeff_of_mem_span` — 1 consumer:
`Invariants/LorentzCovariance.lean:159`.

`StandardModel.Family.exists_invariant_coeff` — **7 call sites**, in
`GaugeGroup/Invariants/`: `IsSU2Adjoint.lean:171`, `IsSU2BiAdjoint.lean:474`,
`IsSU3Adjoint.lean:205`, `IsSU3FunAntiFun.lean:282`, `IsSU3BiAdjoint.lean:918`,
`IsSU2QuadFundamental.lean:445`, `IsSU2BiFundamental.lean:317`. All destructure
`obtain ⟨c, rfl, hc⟩`. Four of them supply `hA` through
`Family.sum_star_mul_of_transpose act sum_act_mul act_star` (IsSU2Adjoint:173,
IsSU2BiAdjoint:476, IsSU3Adjoint:207, IsSU3BiAdjoint:920); the other three supply a
hand-proved `sum_star_mul_act`.

Supporting gauge API, **[S]**: `Family.mem_iSup_span_singleton_iff` — 12 sites across 11 files
including `IsGaugeSector/MassWeight/MassDimEight.lean:114`; `Family.mem_iSup_span_singleton` —
5 sites; `Family.sum_pi_two` — 4 direct sites plus many uses of the per-file `sum_pi_two`
wrappers that delegate to it.

Neither `Invariants.contractₗ` nor `Family.contractₗ`, nor `actMatₗ`, `inner_actMat`, `actₗ`,
`inner_actₗ` has any consumer outside its own file.

### 5.2 Import-direction facts (**[S]**, static import-closure computation)

| file | Physlib closure size | imports SM? | behind `JetAlgebra.SectorEquiv.Basic`? |
| --- | --- | --- | --- |
| `Physlib/Mathematics/LinearCombination.lean` | 1 (Mathlib only) | no | no |
| `Relativity/LorentzGroup/Invariants/Basic.lean` | 61 | no | no |
| `Relativity/LorentzGroup/Invariants/LorentzCovariance.lean` | 62 | no | no |
| `Relativity/LorentzGroup/Invariants/IsLeftRightWeyl.lean` | 67 | no | no |
| `StandardModel/GaugeGroup/Invariants/Basic.lean` | **1 (Mathlib only)** | no | no |
| `StandardModel/GaugeGroup/Invariants/IsSU2BiFundamental.lean` | 100 | yes | **no** |
| `StandardModel/GaugeGroup/Invariants/IsSU3FunAntiFun.lean` | 100 | yes | **no** |
| `StandardModel/Peeling.lean` | 120 | yes | **no** |
| `StandardModel/IsGaugeSector/MassWeight/MassDimEight.lean` | 120 | yes | **no** |

**[S]** Notably `GaugeGroup/Invariants/Basic.lean` currently imports **no Physlib file at all**
— only `Mathlib.Analysis.InnerProductSpace.PiL2`,
`Mathlib.Analysis.InnerProductSpace.Projection.Basic` and
`Mathlib.LinearAlgebra.Finsupp.LinearCombination`. It is under `StandardModel/` for
organisational reasons, not dependency ones.

**[S] Good news for validation:** none of the ten consumers is behind the
`StandardModel.JetAlgebra.SectorEquiv.Basic` blocker. That blocker sits under
`AlgebraRealization`/`CovAlgebraRealization`/`JetAlgebra` and is reached only through
`HiggsAlgebraCovRealization.Basic`. So, subject to the 4.34.0 bump itself, every production
consumer of both lifting theorems is reachable for a real build. This contrasts sharply with
the boost-weight task, where every consumer is blocked.

### 5.3 Recommended home

The shared theorem has no Lorentz content and no Standard Model content, so neither current
home is right. Two candidates:

**Option A (recommended): extend `Physlib/Mathematics/LinearCombination.lean`.**
**[S]** That file is already "Finite linear combinations under a linear map", already holds
`Fintype.sum_sum_mul_smul` and `LinearMap.map_sum_smul_of_forall_eq`, and is already imported
by `Relativity/LorentzGroup/Invariants/Basic.lean` — which is, **[S]**, its *only* importer in
the repository. Cost: two new Mathlib imports
(`Mathlib.Analysis.InnerProductSpace.PiL2`, `…Projection.Basic`), both of which its sole
current importer already has, and both of which the gauge file already has. So the
import-graph cost is genuinely zero for existing consumers. Conforms to AGENTS.md's "place
results in the appropriate existing file; do not create new files without good reason".
Requires the file's module docstring to be rewritten (it currently promises exactly two
bookkeeping identities) and a scalar-generality seam (the existing content is at
`[CommSemiring R]`; the new content is at `ℂ`), which means a new `section` with its own
variables.

**Option B: a new `Physlib/Mathematics/InnerProductSpace/InvariantCoefficient.lean`.**
**[S]** `Physlib/Mathematics/InnerProductSpace/` exists and holds `Adjoint.lean`, `Basic.lean`,
`Calculus.lean`, `Gaussian.lean`, `Submodule.lean`. Cleaner thematically — the theorem *is* an
inner-product-space complement argument — and avoids mixing an analysis import into an
otherwise algebra-only file. Cost: a new file, against AGENTS.md's default.

**[M] Recommendation: Option A**, on the strength of the zero import cost and the AGENTS.md
default, with Option B as the fallback if the human objects to analysis entering
`LinearCombination.lean`. This is a judgement call and is flagged in §7.

Import direction either way: `Mathematics/…` ← `Relativity/LorentzGroup/Invariants/Basic.lean`
and `Mathematics/…` ← `StandardModel/GaugeGroup/Invariants/Basic.lean`. **[M]** The general
theorem must not import either; neither currently exports anything the other needs, and
nothing in the proposal creates a Lorentz→SM or SM→Lorentz edge.

### 5.4 What survives, what disappears, what changes

**[M]** Disappears (proof bodies only, no public names lost if wrappers are kept):

- the ~24-line body of `Family.exists_invariant_coeff` (GaugeGroup/Invariants/Basic.lean:146–169);
- the ~30-line body of `Invariants.exists_invariantCoeff` (Invariants/Basic.lean:86–115);
- one of the two `contractₗ` definitions — **[S]** `Invariants.contractₗ` (66–72) and
  `Family.contractₗ` (98–104) have *identical* bodies modulo the position of `T`, and neither
  has an external consumer, so both can be replaced by one definition in the new home.

**[M]** Survives unchanged and stays where it is:

- `Invariants.actMat`, `actMatₗ`, `inner_actMat`, `exists_invariantCoeff_matrix`,
  `sum_mul_actMat`, `sum_mul_eq_zero_of_actMat_eq`, `two_zpow_ne_one`, `dagger`,
  `toLorentzGroup_dagger`, and all of section C — these are the Lorentz *matrix adapter* and
  have real Lorentz content;
- `Family.actₗ`, `Family.inner_actₗ`, `Family.sum_star_mul_of_transpose` — the gauge-side
  bridge from the raw-sum hypothesis to the inner-product one; `inner_actₗ` becomes the engine
  of the wrapper and `sum_star_mul_of_transpose` keeps its 4 consumers;
- `Family.mem_iSup_span_singleton_iff`, `mem_iSup_span_singleton`, `sum_pi_two` — 21 consumers
  between them, no reason to touch. **[M]** `mem_iSup_span_singleton_iff` is arguably also
  general mathematics that could move alongside (the Lorentz file inlines the same three
  rewrites at Basic.lean:87–90), but it is not part of the lifting theorem and moving it would
  touch 11 files. **Recommend leaving it**, and noting the duplication in a comment.

**[M]** Public callers needing adjustment: **none**, provided both existing theorems are kept
as thin wrappers with unchanged signatures. That is the whole point of the proposed shape.

### 5.5 The two generic peeling lemmas — relationship only

The handoff asks me to inspect `exists_mem_add_of_mem_sup` and `exists_smul_add_of_mem_sup`
(GaugeGroup/Invariants/Basic.lean:190–229) only to explain their relationship to lifting and
whether they belong nearby. I have not redesigned anything.

**[S]** Both take `{G : Type*}` with *no* `[Group G]` — unlike `exists_invariant_coeff` in the
same file. Both are about a stable submodule `S`, the quotient representation `S.mapQ S (φ g)`,
and lifting a quotient classification back. Neither mentions coefficients, inner products,
`ι`, `Fintype` or `ℂ`-specific analysis; **[M]** their only genuine prerequisites are
`[AddCommGroup B] [Module ℂ B]` and Mathlib's `Submodule.mapQ`/`mkQ` API, and the `ℂ` could be
any commutative ring for which `Submodule` quotients exist.

**[M] Relationship to lifting: orthogonal.** Lifting turns *one family's* invariants into a
finite coefficient problem; peeling turns a *classification already obtained in a quotient*
back into a statement in `B`. In the consumer files they are used in sequence — e.g. **[S]**
`IsSU2BiFundamental.exists_smul_epsilonContraction_of_invariant'` (line 317) calls
`exists_invariant_coeff`, and `IsSU2BiFundamental` section F (line 358) then calls
`exists_smul_add_of_mem_sup` with that theorem applied in `B ⧸ S` — but neither uses the other.

**[S]** Their real downstream shape is `StandardModel.Peeling.Step` (`Peeling.lean:296–302`),
whose `classify` field is exactly `exists_smul_add_of_mem_sup`'s conclusion minus the
invariance of the remainder:
`∀ S, IsStableUnder σ S → ∀ x ∈ V ⊔ S, (∀ g, σ g x = x) → ∃ c, ∃ y ∈ S, x = c • contraction + y`.
**[S]** `Peeling.lean` is not behind the blocker.

**[M] Recommendation: do not move them in this change.** They are not part of the shared
lifting theorem, they have a natural downstream home (`Peeling.lean`) that already consumes
them, and moving them is a separate decision with 9 call sites. If the human later wants the
gauge `Invariants/Basic.lean` to be purely about families, section C is the natural thing to
relocate to `Peeling.lean` — but that is a different PR, and this report does not argue for it.

---

## 6. Bounded implementation scope and post-bump experiment plan

### 6.1 Proposed scope (required work only)

1. Add `exists_invariantCoeff_of_adjoint_mem` (§3.4) and one `contractₗ` to the chosen home,
   with a docstring recording the abstract intertwiner formulation from §3.4 and the
   non-uniqueness caveat from §2.6.
2. Re-prove `StandardModel.Family.exists_invariant_coeff` as the §4.2 wrapper; delete its
   proof body and `Family.contractₗ`; keep `actₗ`, `inner_actₗ`, `sum_star_mul_of_transpose`.
3. Delete `Lorentz.Invariants.exists_invariantCoeff` and `Invariants.contractₗ` (zero external
   consumers) and point `exists_invariantCoeff_matrix` at the shared theorem — **or**, if the
   human prefers to keep the name, re-prove it as a one-line wrapper. Either way
   `exists_invariantCoeff_matrix`'s signature and conjunct order are unchanged.
4. Fix the two misleading pieces of prose: the gauge file's "which is to say that `A` is
   unitary" (lines 84–87) and the Lorentz `inner_actMat` docstring's implicit contrast — see
   §2.3. The gauge prose should say "closed under adjoints, with `g⁻¹` supplying the adjoint
   of `g` in every gauge case", not "unitary".

**[M] Estimated diff:** roughly +45 / −60 Lean lines plus docstrings — within the
"easy to check" band of `docs/ReviewGuidelines.md`, and a single coherent concept
("invariants of the span of a finite family lift to invariant coefficients") as AGENTS.md
requires.

### 6.2 Optional improvements, explicitly out of the required scope

- Replace the hand-written `h2` step by `LinearMap.eq_adjoint_iff` +
  `Module.End.mem_invtSubmodule_adjoint_iff` (§3.3). Proof-internal; no contract change.
- Expose the minimum-norm characterisation of the produced coefficient (§2.6). No consumer.
- Generalise `ℂ` to `RCLike 𝕜`. **Recommended against** (§3.4).
- Relocate `mem_iSup_span_singleton_iff` (§5.4). **Recommended against** in this PR.
- Relocate gauge section C to `Peeling.lean` (§5.5). **Recommended against** in this PR.

### 6.3 Ordered Lean 4.34.0 probes

Each probe is a stop/go gate; a failure at P*n* means the remaining probes are not informative.

| # | probe | pass criterion | stop/go |
| --- | --- | --- | --- |
| **P0** | Build the *destination* file only, with the two new Mathlib imports added and no new content. | Elaborates. | If `Mathlib.Analysis.InnerProductSpace.{PiL2, Projection.Basic}` have moved or been split in 4.34.0, resolve the new module names before anything else. |
| **P1** | State and prove `exists_invariantCoeff_of_adjoint_mem` in the destination, by copying the body of `Invariants.exists_invariantCoeff` verbatim and widening `ι` to `Type*`. | Elaborates with no new hypotheses. | Failure here means a Mathlib API in the orthogonal-projection chain changed; §3.3 lists every dependency with its 4.33.0 line so the diff can be located. |
| **P2** | Restate `Lorentz.Invariants.exists_invariantCoeff`'s *original* contract (verbatim, `ι : Type`) as a wrapper around P1. | Elaborates; `#print axioms` shows only the three standard axioms. | Go. |
| **P3** | Restate `StandardModel.Family.exists_invariant_coeff`'s *original* contract verbatim as the §4.2 wrapper. | Elaborates. | **The known-risky step** (§4.2): if `inner_actₗ`'s `actₗ A g v` does not unify with `WithLp.toLp 2 (A g v.ofLp)`, add `simp only [actₗ, LinearMap.coe_mk, AddHom.coe_mk]`. Neither contract changes either way. |
| **P4** | Empty-index and dependent-family sanity, as *restated applications*: `ι := Fin 0` with any `T`; and `ι := Fin 2` with `T 0 = T 1 ≠ 0`, `G := Unit`, `A _ := id`. | Both elaborate; the dependent one demonstrably does not force `c 0 = c 1`. | Go. Confirms §2.6 in Lean rather than on paper. |
| **P5** | Compile the **original production consumers**, not restatements: `GaugeGroup/Invariants/IsSU2BiFundamental.lean` and `IsSU3FunAntiFun.lean` (hand-proved `hA`), then `IsSU2Adjoint.lean` and `IsSU3BiAdjoint.lean` (`sum_star_mul_of_transpose` route), then `Relativity/LorentzGroup/Invariants/IsLeftRightWeyl.lean` and `LorentzCovariance.lean`. | All six elaborate unchanged. | **This is the acceptance gate.** §5.2 establishes that none of these is behind the blocker, so a failure here is a real regression, not an inherited one. |
| **P6** | `#print axioms` on `exists_invariantCoeff_of_adjoint_mem`, `Family.exists_invariant_coeff`, `Invariants.exists_invariantCoeff_matrix`, `Invariants.exists_isInvariantCoeff_of_mem_span`. | `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`. | Go. |
| **P7** *(optional)* | Swap the `h2` step for the Mathlib `invtSubmodule` route (§6.2). | P1–P6 still pass. | Purely optional; abandon on any friction. |

**[S] Blocker-related validation obligations.** The
`StandardModel.JetAlgebra.SectorEquiv.Basic` failure blocks nothing on this task's critical
path (§5.2). The one thing it does prevent is confirming that the *downstream* gauge-sector
consumers of the classification theorems — e.g.
`CovAlgebraRealization/GaugeHiggsSector/`, which sit behind
`HiggsAlgebraCovRealization.Basic` — still build. Those are consumers of the classification
*results*, not of the lifting theorem, and their contracts are untouched by this proposal; but
that reasoning is **[M]**, not a build, and should be recorded as owed. Do not repair or build
the blocker as part of this work.

---

## 7. Risks, counterevidence and questions for human judgement

**[M] Risks.**

1. *The §4.2 defeq* (P3). Low severity, known fix, no contract impact.
2. *Docstring drift.* The gauge file's section-B prose is the argument's exposition; rewriting
   "unitary" out of it changes the file's narrative. This is a documentation correction, not a
   mathematical one, but AGENTS.md treats module documentation as load-bearing and the human
   should read the replacement text.
3. *Deleting `Invariants.exists_invariantCoeff` and the two `contractₗ`.* All three are
   `@[expose] public` with docstrings. Grep says zero external consumers, but grep cannot see
   consumers in a branch not yet merged.
4. *`Type` → `Type*` on `ι`.* **[M]** Cannot break a `Type 0` instantiation, but it can change
   universe-metavariable resolution in an unannotated call. All three Lorentz call sites pass
   `T` explicitly, which pins `ι`, so the risk is small.

**Counterevidence to the whole proposal, stated fairly.** The strongest argument *against*
merging is that the two theorems currently sit in files whose module docstrings tell two
different, self-contained stories — "which vectors does `SL(2,ℂ)` leave alone" and "which
linear combinations of gauge components are invariant" — and each story reads better with its
proof visible. Merging saves ~55 lines of duplicated proof and one duplicated definition, but
costs a hop to a third file for a reader of either. **[M]** I judge the merge worthwhile
because the duplication is *exact* (§3.1 is a line-by-line identity, not an analogy) and
because the gauge file's prose has already drifted into a false claim ("unitary") that a
single shared statement would have prevented. But this is a taste judgement about
navigability, which `docs/ReviewGuidelines.md` explicitly reserves to the reviewer.

**Questions requiring human judgement.**

- **Home:** Option A (`Mathematics/LinearCombination.lean`, zero import cost, changes the
  file's character) or Option B (new `Mathematics/InnerProductSpace/InvariantCoefficient.lean`,
  cleaner theme, a new file)? §5.3.
- **Name:** `exists_invariantCoeff_of_adjoint_mem` is descriptive but long. The two existing
  names differ only in casing convention; the shared one has to pick a namespace that is
  neither `Lorentz.Invariants` nor `StandardModel.Family`.
- **Deletion:** delete `Lorentz.Invariants.exists_invariantCoeff` (zero consumers) or keep it
  as a wrapper? §4.1.
- **Standing preference:** previous sessions recorded a preference that work on a Lean file be
  confined to that file, without moving results out. This proposal is inherently a cross-file
  move and therefore needs an explicit go-ahead; if that preference still holds, the alternative
  is to leave both theorems where they are and only fix the "unitary" prose (§6.1 item 4),
  which is a genuinely useful standalone change.

---

## 8. What this report does not establish

No Lean was elaborated. No build, benchmark, timing, axiom audit or lint run was performed, and
none is reported. Every Lean fragment above is an uncompiled sketch. Mathlib claims are asserted
only for rev `db584cd6` (v4.33.0) as read from `.lake/packages/mathlib`; absence from that
snapshot is not evidence of absence from 4.34.0, and presence in it is not evidence of presence
in 4.34.0. No assumption is made about whether `StandardModel.JetAlgebra.SectorEquiv.Basic`
builds on any other revision. Human review, then the §6.3 probes on 4.34.0, are the acceptance
gate before implementation.
