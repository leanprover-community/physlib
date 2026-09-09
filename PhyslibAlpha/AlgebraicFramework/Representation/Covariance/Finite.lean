/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Representation.Covariance.Basic
public import PhyslibAlpha.AlgebraicFramework.Measurement.Postprocessing
public import Mathlib.Algebra.Group.Action.Prod

/-!

# Covariance for finite-outcome measurements

`Covariance.lean` sets up covariance in full measure-theoretic generality: a measurable action of
`G` on an outcome space `Ω`, transported to a physical system via a homomorphism into `Symmetry E`.
For a *finite* outcome type `ι`, this specializes drastically: a group acting on a finite label set
needs no measurability machinery at all, since every subset of a finite type is automatically
"measurable" in the relevant sense — a permutation of a finite set permutes it, full stop. This
file builds the induced symmetry action `G →* Symmetry (ι → ℝ)` on the classical `ι`-outcome system
(`ClassicalSystem.lean`, `FiniteOutcome.lean`), and uses it to specialize two of `Covariance.lean`'s
general structural theorems — covariance preserved under composition, and under postprocessing —
to finite-outcome measurements presented as channels (`Measurement.channelEquiv`).

The induced action is the standard "functions on a `G`-set" representation: `(σ • f) i = f (σ⁻¹ •
i)`. This is a genuine *left* action — `σ • (τ • f) = (σ * τ) • f` — precisely because of the
inverse: composing `f ↦ f ∘ (σ⁻¹ • ·)` then `f ↦ f ∘ (τ⁻¹ • ·)` composes the permutations as
`(στ)⁻¹ = τ⁻¹σ⁻¹` in the matching order (`inducedAction`'s `map_mul'` spells this out) — using `σ`
without inversion would instead give an *anti*-homomorphism. This matches the standard convention
for the classical system, `(β_g f)(x) = f(g⁻¹x)`.

Since a finite-outcome measurement `M : (ι → ℝ) →ₚ₁[ℝ] E` is already a channel
(`FiniteOutcome.lean`), its covariance under this induced action, matched to a target symmetry
`ρ : G →* Symmetry E`, is *literally* `Covariance.lean`'s general channel notion,
`M.IsCovariant inducedAction ρ` — no new predicate is needed. The two theorems proved here,
`postprocess_isCovariant` and `marginal_isCovariant`, both fall out of
`UnitalPositiveLinearMap.IsCovariant.comp` plus the fact that postprocessing and marginalizing are
literal channel composition (`Postprocessing.lean`).

## Main definitions

- `inducedLinearMap`, `inducedChannel`, `inducedSymmetry`, `inducedAction` : the homomorphism
  `G →* Symmetry (ι → ℝ)` induced by a `MulAction G ι` on a finite outcome-label type.
- `Measurement.postprocess_isCovariant` : post-processing by an equivariant classical channel
  preserves covariance.
- `Measurement.classicalPullback_isCovariant`, `Measurement.marginal_isCovariant` : marginals of a
  covariant joint measurement, for a diagonal product action on the joint outcome type, are
  covariant.

-/

@[expose] public section

section InducedAction

variable {G ι : Type*} [Group G] [MulAction G ι]

/-- The linear map on the classical system `ι → ℝ` induced by `σ : G` permuting the outcome label
type `ι`: pulling a function of the outcome back along `σ⁻¹`'s action on `ι`,
`(inducedLinearMap σ f) i = f (σ⁻¹ • i)`. The standard "functions on a `G`-set" representation,
`(β_g f)(x) = f(g⁻¹x)`, built as `LinearMap.funLeft` along the point map `i ↦ σ⁻¹ • i` — the same
building block `Postprocessing.lean`'s `classicalPullback` uses. -/
def inducedLinearMap (σ : G) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun i => σ⁻¹ • i)

@[simp]
lemma inducedLinearMap_apply (σ : G) (f : ι → ℝ) (i : ι) :
    inducedLinearMap σ f i = f (σ⁻¹ • i) := rfl

/-- `inducedLinearMap σ` promoted to a channel: positivity is pointwise (permuting nonnegative
coordinates stays nonnegative) and unitality is immediate (the certain event is constant). -/
def inducedChannel (σ : G) : (ι → ℝ) →ₚ₁[ℝ] (ι → ℝ) :=
  UnitalPositiveLinearMap.ofLinearMap (inducedLinearMap σ) (fun _x hx i => hx (σ⁻¹ • i)) rfl

@[simp]
lemma inducedChannel_apply (σ : G) (f : ι → ℝ) (i : ι) :
    inducedChannel σ f i = f (σ⁻¹ • i) := rfl

/-- `inducedChannel σ` is an order-automorphism, with inverse `inducedChannel σ⁻¹`: undoing a
permutation of the outcome labels undoes the induced channel. -/
lemma isOrderAutomorphism_inducedChannel (σ : G) :
    IsOrderAutomorphism (inducedChannel σ : (ι → ℝ) →ₚ₁[ℝ] (ι → ℝ)) := by
  refine ⟨inducedChannel σ⁻¹, UnitalPositiveLinearMap.ext fun x => funext fun i => ?_,
    UnitalPositiveLinearMap.ext fun x => funext fun i => ?_⟩
  · simp [UnitalPositiveLinearMap.comp_apply, inv_inv, inv_smul_smul]
  · simp [UnitalPositiveLinearMap.comp_apply, inv_inv, smul_inv_smul]

/-- `inducedChannel σ` bundled as a `Symmetry (ι → ℝ)`. -/
def inducedSymmetry (σ : G) : Symmetry (ι → ℝ) :=
  ⟨inducedChannel σ, isOrderAutomorphism_inducedChannel σ⟩

@[simp]
lemma inducedSymmetry_val (σ : G) : (inducedSymmetry σ : Symmetry (ι → ℝ)).1 = inducedChannel σ :=
  rfl

/-- The homomorphism `G →* Symmetry (ι → ℝ)` induced by a `G`-action on an outcome-label type `ι`:
`σ` acts on the classical system by pulling functions back along `σ⁻¹`'s action on the labels.
Group-homomorphism-hood is exactly the check that this is the direction composing as a genuine
*left* action, not its inverse-twisted (anti-homomorphism) variant. -/
def inducedAction : G →* Symmetry (ι → ℝ) where
  toFun := inducedSymmetry
  map_one' := Symmetry.ext fun x => funext fun i => by
    simp [inducedSymmetry_val, inducedChannel_apply]
  map_mul' σ τ := Symmetry.ext fun x => funext fun i => by
    simp [inducedSymmetry_val, Symmetry.val_mul, UnitalPositiveLinearMap.comp_apply,
      inducedChannel_apply, mul_smul, mul_inv_rev]

@[simp]
lemma inducedAction_val (σ : G) :
    (inducedAction σ : Symmetry (ι → ℝ)).1 = inducedChannel σ := rfl

end InducedAction

namespace Measurement

/-! ## Post-processing by an equivariant classical channel preserves covariance

A finite-outcome measurement `M : (ι → ℝ) →ₚ₁[ℝ] E` is covariant under a `G`-action on its outcome
labels `ι`, matched to a target symmetry `ρ : G →* Symmetry E`, precisely when
`M.IsCovariant inducedAction ρ` — `Covariance.lean`'s general notion, instantiated with the
induced action from `inducedAction` above. No new predicate is needed: this *is* that notion. -/

/-- Post-processing by an equivariant classical channel preserves covariance: if `M` is covariant
and the relabeling channel `K` itself intertwines the induced actions on `κ → ℝ` and `ι → ℝ`, then
postprocessing `M` through `K` is covariant for the `κ`-side action. Postprocessing being literal
channel composition (`Postprocessing.lean`), this falls out of `Covariance.lean`'s
`IsCovariant.comp`. -/
theorem postprocess_isCovariant
    {G ι κ E : Type*} [Group G]
    [MulAction G ι] [MulAction G κ]
    [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E]
    {ρ : G →* Symmetry E} {M : (ι → ℝ) →ₚ₁[ℝ] E} {K : (κ → ℝ) →ₚ₁[ℝ] (ι → ℝ)}
    (hM : M.IsCovariant (inducedAction (G := G) (ι := ι)) ρ)
    (hK : K.IsCovariant (inducedAction (G := G) (ι := κ)) (inducedAction (G := G) (ι := ι))) :
    (postprocess M K).IsCovariant (inducedAction (G := G) (ι := κ)) ρ :=
  hM.comp hK

/-! ## Marginals of a covariant joint measurement are covariant -/

/-- A deterministic relabeling `f : κ → ι` that intertwines two `G`-actions induces a classical
channel (`classicalPullback f`) that is itself covariant for the induced actions on `ι → ℝ` and
`κ → ℝ`. The equivariance hypothesis on `f` is the discrete, function-level form of
`Covariance.lean`'s `measurableSet_smul` — here trivial, since every map between finite `G`-sets is
automatically "measurable". -/
lemma classicalPullback_isCovariant
    {G ι κ : Type*} [Group G]
    [MulAction G ι] [MulAction G κ]
    (f : κ → ι) (hf : ∀ (g : G) (k : κ), f (g • k) = g • f k) :
    (classicalPullback f).IsCovariant
      (inducedAction (G := G) (ι := ι)) (inducedAction (G := G) (ι := κ)) := by
  intro g
  apply UnitalPositiveLinearMap.ext
  intro x
  funext k
  simp only [UnitalPositiveLinearMap.comp_apply, inducedAction_val, inducedChannel_apply,
    classicalPullback_apply]
  rw [hf g⁻¹ k]

/-- Marginals of a covariant joint measurement are covariant: if `J : (ι × κ → ℝ) →ₚ₁[ℝ] E` is
covariant for the diagonal product action of `G` on `ι × κ` (acting on both factors
simultaneously), then its marginal onto `ι`,
`postprocess J (classicalPullback Prod.fst)` (`Compatibility.lean`'s marginalization), is
covariant for the induced action on `ι` alone. This specializes `postprocess_isCovariant` to the
classical channel `classicalPullback Prod.fst`, using that `Prod.fst` intertwines the diagonal
action on `ι × κ` with the action on `ι` (`Prod.smul_fst`). -/
theorem marginal_isCovariant
    {G ι κ E : Type*} [Group G]
    [MulAction G ι] [MulAction G κ]
    [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E]
    {ρ : G →* Symmetry E} {J : (ι × κ → ℝ) →ₚ₁[ℝ] E}
    (hJ : J.IsCovariant (inducedAction (G := G) (ι := ι × κ)) ρ) :
    (postprocess J (classicalPullback Prod.fst)).IsCovariant
      (inducedAction (G := G) (ι := ι)) ρ :=
  hJ.comp (classicalPullback_isCovariant Prod.fst (fun g p => by simp))

end Measurement
