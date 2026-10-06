/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
/-!

# Souriau's moment map on a symplectic vector space

Souriau's moment map, cocycle and Noether theorem for affine actions on a symplectic space.

## i. Overview

Souriau (Structure des systèmes dynamiques, Dunod 1970, chapter 11) attaches to a Lie group `G`
acting on a symplectic manifold `V` by symplectomorphisms (a *dynamical group*) a *moment*
`μ : V → 𝔤*`, defined by `σ(Z_V(x)) = -∇[μ.Z]` for every `Z` in the Lie algebra (11.7). Two moments
differ by a constant (11.8 a); the moment is constant along the motions (Noether's theorem, 11.12);
and the moment fails to be equivariant for the coadjoint action by a *symplectic cocycle* `θ` whose
derivative `f` is a 2-form on `𝔤` satisfying `σ(Z_V)(Z'_V) = μ[Z, Z'] + f(Z)(Z')` (11.17 d) and the
cyclic identity (11.33). The cohomology class of `θ` is an invariant of the dynamical group; it is
zero when a `G`-invariant potential of `σ` exists (11.21) and for semisimple groups (11.27).

This file states and proves these results in the setting of Souriau's example (11.2): a real
finite-dimensional symplectic vector space `E` on which a real Lie algebra `𝔤` acts by *affine*
infinitesimally symplectic vector fields `Z_E(x) = A Z x + b Z` (the infinitesimal version of the
affine symplectomorphisms `x ↦ B x + C` of (10.12)). No manifold is involved: the moment is given
explicitly by `μ.Z (x) = -½ σ(A Z x, x) - σ(b Z, x)`, the cocycle by `f(Z)(Z') = σ(b Z, b Z')`, and
Noether's theorem is stated for a Hamiltonian flow on `E`.

All signs follow Souriau's printed conventions: the bracket of the Lie algebra is the one for which
`Z ↦ Z_E` is a homomorphism for the bracket `[Z, Z']_E = Z'_E ∘ Z_E - Z_E ∘ Z'_E` of (11.22 a)
(opposite to the usual commutator), `Ad(Z)(Z') = [Z, Z']` (6.13 b), and the coadjoint vector
field is `Z_{𝔤*}(ν) = ν ∘ Ad(Z)` (11.16).

## ii. Key results

- `AffineSymplecticAction.hasFDerivAt_moment`: (11.7), `σ(Z_E(x)) = -∇[μ.Z]`.
- `AffineSymplecticAction.moment_unique`: (11.8 a), two moments differ by a constant torsor; this is
  proved without the alternation of `σ`, from the symmetry of the second derivative of the given
  moment.
- `AffineSymplecticAction.sigma_vectorField_vectorField`: (11.17 d),
  `σ(Z_E)(Z'_E) = μ[Z, Z'] + f(Z)(Z')`.
- `AffineSymplecticAction.cocycle_cyclic`: (11.33), the cyclic identity of the symplectic cocycle.
- `AffineSymplecticAction.equivariant_of_coboundary`: (11.27) in this setting, a coboundary cocycle
  can be absorbed in the moment.
- `AffineSymplecticAction.noether`: (11.12), `μ.Z` is a first integral of every `Z_E`-invariant
  Hamiltonian flow.
- `planeTranslations_not_coboundary`: the translations of the plane have a non-zero cohomology class
  (the simplest instance of Souriau's "mass" cocycle).

## iii. Table of contents

- A. Symplectic forms
- B. Affine symplectic actions of a Lie algebra
- C. The Souriau cocycle
- D. The moment map
- E. Noether's theorem
- F. The plane: translations and a non-trivial cohomology class

## iv. References

- J.-M. Souriau, Structure des systèmes dynamiques, Dunod, Paris, 1970, chapter 11,
  pp. 104-117; English translation: Structure of Dynamical Systems, Birkhäuser, 1997
  (same equation numbers).

* J.-M. Souriau, *Structure des systèmes dynamiques*, Maîtrises de mathématiques, Dunod,
  Paris, 1970, chapter 11, pp. 104-117. The equation numbers (11.7),
  (11.8), (11.12), (11.17), (11.22), (11.27), (11.33) refer to this edition. [ref: Souriau1970]

-/

@[expose] public section

noncomputable section

namespace ClassicalMechanics

open Module

/-!

## A. Symplectic forms

Souriau's "forme de Lagrange" `σ` is an alternating non-degenerate bilinear form.

-/

/-- A symplectic form on a real vector space: an alternating non-degenerate bilinear form. -/
structure IsSymplecticForm {E : Type} [AddCommGroup E] [Module ℝ E] (σ : LinearMap.BilinForm ℝ E) :
    Prop where
  /-- `σ` is alternating: `σ v v = 0`. -/
  alt : LinearMap.BilinForm.IsAlt σ
  /-- `σ` is non-degenerate. -/
  nondeg : LinearMap.BilinForm.Nondegenerate σ

/-!

## B. Affine symplectic actions of a Lie algebra

The infinitesimal version of Souriau's example (11.2) with the affine symplectomorphisms of (10.12):
each `Z` of the Lie algebra acts on `E` by the affine vector field `Z_E(x) = A Z x + b Z`, with
`A Z` infinitesimally symplectic ((10.28)-(10.32)), and the bracket is Souriau's (6.12 b),
(11.22 a): `[Z, Z']_E = Z'_E ∘ Z_E - Z_E ∘ Z'_E`, extended to affine vector fields by the formula
`[X, X'](x) = DX'(x)(X(x)) - DX(x)(X'(x))`.

-/

/-- An affine infinitesimally symplectic action of a Lie algebra `g` on `E`, in Souriau's
conventions: `Z_E(x) = A Z x + b Z`. -/
structure AffineSymplecticAction {E : Type} [AddCommGroup E] [Module ℝ E]
    (σ : LinearMap.BilinForm ℝ E) (g : Type) [LieRing g] [LieAlgebra ℝ g] where
  /-- The linear part `Z ↦ A Z` of the vector fields. -/
  A : g →ₗ[ℝ] (E →ₗ[ℝ] E)
  /-- The constant part `Z ↦ b Z` of the vector fields. -/
  b : g →ₗ[ℝ] E
  /-- Each `A Z` is infinitesimally symplectic: `σ (A Z v) w + σ v (A Z w) = 0`. -/
  infinitesimallySymplectic : ∀ Z v w, σ (A Z v) w + σ v (A Z w) = 0
  /-- Souriau's bracket (11.22 a) on the linear parts: `A [Z, Z'] = A Z' ∘ A Z - A Z ∘ A Z'`. -/
  map_bracket_A : ∀ Z Z', A ⁅Z, Z'⁆ = A Z' ∘ₗ A Z - A Z ∘ₗ A Z'
  /-- Souriau's bracket on the constant parts: `b [Z, Z'] = A Z' (b Z) - A Z (b Z')`. -/
  map_bracket_b : ∀ Z Z', b ⁅Z, Z'⁆ = A Z' (b Z) - A Z (b Z')

/-- (11.16) with (6.13 b): the coadjoint vector field `Z_{𝔤*}(ν) = ν ∘ Ad(Z)`,
`Ad(Z)(Z') = [Z, Z']`, for a torsor `ν` given as a function; this is also the coboundary
`δ(ν)(Z)` of (11.24). -/
def coadjoint {g : Type} [LieRing g] (Z : g) (ν : g → ℝ) (Z' : g) : ℝ := ν ⁅Z, Z'⁆

namespace AffineSymplecticAction

variable {E : Type} [AddCommGroup E] [Module ℝ E]
variable {g : Type} [LieRing g] [LieAlgebra ℝ g] {σ : LinearMap.BilinForm ℝ E}
variable (ρ : AffineSymplecticAction σ g)

/-- (6.11): the affine vector field `Z_E` associated with `Z`. -/
def vectorField (Z : g) (x : E) : E := ρ.A Z x + ρ.b Z

/-- The moment (11.7), (11.9) of the action, as a function of the point `x` and of `Z`:
`μ.Z (x) = -½ σ(A Z x, x) - σ(b Z, x)`. Its sign is fixed by (11.7). -/
def moment (x : E) (Z : g) : ℝ := -(1 / 2 : ℝ) * σ (ρ.A Z x) x - σ (ρ.b Z) x

/-- (11.17 c): Souriau's cocycle `f(Z)(Z') = σ(b Z, b Z')`, a 2-form on `g`. -/
def cocycle (Z Z' : g) : ℝ := σ (ρ.b Z) (ρ.b Z')

/-- `infinitesimallySymplectic` in the form `σ (A Z v) w = -σ v (A Z w)`. -/
lemma sigma_A_left (Z : g) (v w : E) : σ (ρ.A Z v) w = -σ v (ρ.A Z w) :=
  eq_neg_of_add_eq_zero_left (ρ.infinitesimallySymplectic Z v w)

/-- `infinitesimallySymplectic` in the form `σ v (A Z w) = -σ (A Z v) w`. -/
lemma sigma_A_right (Z : g) (v w : E) : σ v (ρ.A Z w) = -σ (ρ.A Z v) w := by
  rw [ρ.sigma_A_left Z v w, neg_neg]

/-- For an alternating `σ`, `σ (A Z v) w` is symmetric in `v`, `w`. -/
lemma sigma_A_symm (hσ : IsSymplecticForm σ) (Z : g) (v w : E) :
    σ (ρ.A Z v) w = σ (ρ.A Z w) v := by
  rw [ρ.sigma_A_left Z v w, hσ.alt.neg_eq]

/-- The moment is a torsor: `μ.(Z + Z') = μ.Z + μ.Z'`. -/
lemma moment_add (x : E) (Z Z' : g) : ρ.moment x (Z + Z') = ρ.moment x Z + ρ.moment x Z' := by
  simp only [moment, map_add, LinearMap.add_apply]
  ring

/-- The moment is a torsor: `μ.(c Z) = c μ.Z`. -/
lemma moment_smul (x : E) (c : ℝ) (Z : g) : ρ.moment x (c • Z) = c * ρ.moment x Z := by
  simp only [moment, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-!

## C. The Souriau cocycle

(11.17 d, ♯), (11.30), (11.33), the Lie algebra cocycle identity (11.22)/(11.24), the change of
moment (11.18), the coboundary case (11.27) and the linear case (11.21). Everything here is algebra:
only the bilinearity and the alternation of `σ` and the axioms of the action are used.

-/

/-- (11.17 d, ♯): `σ(Z_E(x))(Z'_E(x)) = μ[Z, Z'](x) + f(Z)(Z')`. -/
lemma sigma_vectorField_vectorField (hσ : IsSymplecticForm σ) (Z Z' : g) (x : E) :
    σ (ρ.vectorField Z x) (ρ.vectorField Z' x) = ρ.moment x ⁅Z, Z'⁆ + ρ.cocycle Z Z' := by
  unfold vectorField moment cocycle
  rw [ρ.map_bracket_A Z Z', ρ.map_bracket_b Z Z']
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_add, map_sub, LinearMap.add_apply]
  have h1 : σ (ρ.A Z' (ρ.A Z x)) x = -σ (ρ.A Z x) (ρ.A Z' x) := ρ.sigma_A_left Z' _ _
  have h2 : σ (ρ.A Z (ρ.A Z' x)) x = σ (ρ.A Z x) (ρ.A Z' x) := by
    rw [ρ.sigma_A_left Z, hσ.alt.neg_eq]
  have h3 : σ (ρ.A Z' (ρ.b Z)) x = -σ (ρ.b Z) (ρ.A Z' x) := ρ.sigma_A_left Z' _ _
  have h4 : σ (ρ.A Z (ρ.b Z')) x = σ (ρ.A Z x) (ρ.b Z') := by
    rw [ρ.sigma_A_left Z, hσ.alt.neg_eq]
  rw [h1, h2, h3, h4]
  ring

/-- (11.30): the cocycle is antisymmetric. -/
lemma cocycle_antisymm (hσ : IsSymplecticForm σ) (Z Z' : g) :
    ρ.cocycle Z' Z = -ρ.cocycle Z Z' := by
  unfold cocycle
  exact (hσ.alt.neg_eq _ _).symm

/-- (11.33): the cyclic identity `f(Z)([Z', Z'']) + f(Z')([Z'', Z]) + f(Z'')([Z, Z']) = 0`. -/
lemma cocycle_cyclic (hσ : IsSymplecticForm σ) (Z Z' Z'' : g) :
    ρ.cocycle Z ⁅Z', Z''⁆ + ρ.cocycle Z' ⁅Z'', Z⁆ + ρ.cocycle Z'' ⁅Z, Z'⁆ = 0 := by
  unfold cocycle
  rw [ρ.map_bracket_b Z' Z'', ρ.map_bracket_b Z'' Z, ρ.map_bracket_b Z Z']
  simp only [map_sub]
  rw [ρ.sigma_A_right Z'' (ρ.b Z) (ρ.b Z'), ρ.sigma_A_right Z' (ρ.b Z) (ρ.b Z''),
    ρ.sigma_A_right Z (ρ.b Z') (ρ.b Z''), ρ.sigma_A_right Z'' (ρ.b Z') (ρ.b Z),
    ρ.sigma_A_right Z' (ρ.b Z'') (ρ.b Z), ρ.sigma_A_right Z (ρ.b Z'') (ρ.b Z')]
  have e1 := ρ.sigma_A_symm hσ Z'' (ρ.b Z') (ρ.b Z)
  have e2 := ρ.sigma_A_symm hσ Z' (ρ.b Z'') (ρ.b Z)
  have e3 := ρ.sigma_A_symm hσ Z (ρ.b Z'') (ρ.b Z')
  linarith

/-- (11.22)/(11.24) for the coadjoint representation: `f` is a Lie algebra cocycle,
`f([Z, Z']) = Z'_{𝔤*}(f(Z)) - Z_{𝔤*}(f(Z'))`, evaluated on `Z''`. -/
lemma cocycle_lie (hσ : IsSymplecticForm σ) (Z Z' Z'' : g) :
    ρ.cocycle ⁅Z, Z'⁆ Z'' = ρ.cocycle Z ⁅Z', Z''⁆ - ρ.cocycle Z' ⁅Z, Z''⁆ := by
  unfold cocycle
  rw [ρ.map_bracket_b Z Z', ρ.map_bracket_b Z' Z'', ρ.map_bracket_b Z Z'']
  simp only [map_sub, LinearMap.sub_apply]
  rw [ρ.sigma_A_right Z'' (ρ.b Z) (ρ.b Z'), ρ.sigma_A_right Z' (ρ.b Z) (ρ.b Z''),
    ρ.sigma_A_right Z'' (ρ.b Z') (ρ.b Z), ρ.sigma_A_right Z (ρ.b Z') (ρ.b Z'')]
  have e1 := ρ.sigma_A_symm hσ Z'' (ρ.b Z') (ρ.b Z)
  linarith

/-- (11.18): changing the moment into `μ - μ₀` (`μ₀` a constant torsor) keeps (11.17 d) with the
cocycle `f + Z_{𝔤*}(μ₀)`, i.e. `f(Z)(Z') + μ₀ [Z, Z']`. -/
lemma sigma_vectorField_vectorField_shift (hσ : IsSymplecticForm σ) (μ₀ : Dual ℝ g) (Z Z' : g)
    (x : E) :
    σ (ρ.vectorField Z x) (ρ.vectorField Z' x) =
      (ρ.moment x ⁅Z, Z'⁆ - μ₀ ⁅Z, Z'⁆) + (ρ.cocycle Z Z' + coadjoint Z μ₀ Z') := by
  rw [ρ.sigma_vectorField_vectorField hσ Z Z' x]
  unfold coadjoint
  ring

/-- (11.27) in this setting: if the cocycle is a coboundary, `f(Z)(Z') = μ₀ [Z, Z']`, then the
moment `μ + μ₀` is exactly equivariant. -/
lemma equivariant_of_coboundary (hσ : IsSymplecticForm σ) (μ₀ : Dual ℝ g)
    (h : ∀ Z Z', ρ.cocycle Z Z' = coadjoint Z μ₀ Z') (Z Z' : g) (x : E) :
    σ (ρ.vectorField Z x) (ρ.vectorField Z' x) = ρ.moment x ⁅Z, Z'⁆ + μ₀ ⁅Z, Z'⁆ := by
  rw [ρ.sigma_vectorField_vectorField hσ Z Z' x, h Z Z']
  rfl

/-- (11.21) in this setting: a linear action (`b = 0`, the case (11.2) of `Sp(E)`) has a zero
cocycle. -/
lemma cocycle_eq_zero_of_linear (hb : ρ.b = 0) (Z Z' : g) : ρ.cocycle Z Z' = 0 := by
  simp [cocycle, hb]

end AffineSymplecticAction

/-- The symplectic gradient (9.16) in the convention of (11.7) and (10.32): `X` is the symplectic
gradient of `u` when `σ (X x) v = -Du(x)(v)` for all `x`, `v`. -/
def IsSymplecticGradient {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : LinearMap.BilinForm ℝ E) (u : E → ℝ) (X : E → E) : Prop :=
  ∀ x v, σ (X x) v = -(fderiv ℝ u x v)

/-!

## D. The moment map

(11.7), (11.9) and (11.8 a), then the infinitesimal equivariance (11.17 d, ♠) and the identity
(11.8 c). The derivative of `y ↦ σ (A y) y` is computed by viewing `y ↦ σ (A y)` as a continuous
linear map into `E →L[ℝ] ℝ`.

-/

namespace AffineSymplecticAction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {g : Type} [LieRing g] [LieAlgebra ℝ g] {σ : LinearMap.BilinForm ℝ E}
variable (ρ : AffineSymplecticAction σ g)

/-- `y ↦ σ (A Z y)` as a continuous linear map from `E` to `E →L[ℝ] ℝ`. -/
def sigmaA (Z : g) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ σ ∘ₗ ρ.A Z)

@[simp]
lemma sigmaA_apply (Z : g) (y v : E) : ρ.sigmaA Z y v = σ (ρ.A Z y) v := by
  simp [sigmaA]

/-- The constant linear form `σ (b Z)` as a continuous linear map. -/
def sigmaB (Z : g) : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (σ (ρ.b Z))

@[simp]
lemma sigmaB_apply (Z : g) (v : E) : ρ.sigmaB Z v = σ (ρ.b Z) v := by
  simp [sigmaB]

/-- The derivative of `y ↦ σ (A Z y) y` at `x` is `v ↦ σ (A Z v) x + σ (A Z x) v`. -/
lemma hasFDerivAt_quad (Z : g) (x : E) :
    HasFDerivAt (fun y => σ (ρ.A Z y) y)
      ((ρ.sigmaA Z x).comp (ContinuousLinearMap.id ℝ E) + (ρ.sigmaA Z).flip x) x := by
  have h := (ρ.sigmaA Z).hasFDerivAt (x := x)
  have h2 := hasFDerivAt_id (𝕜 := ℝ) x
  have h3 := h.clm_apply h2
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp

/-- (11.7) under the sole symmetry `σ (A Z v) w = σ (A Z w) v`. -/
lemma hasFDerivAt_moment_of_symm (Z : g) (hsym : ∀ v w, σ (ρ.A Z v) w = σ (ρ.A Z w) v) (x : E) :
    HasFDerivAt (fun y => ρ.moment y Z)
      (-(LinearMap.toContinuousLinearMap (σ (ρ.vectorField Z x)))) x := by
  have hq := ρ.hasFDerivAt_quad Z x
  have hl : HasFDerivAt (fun y => σ (ρ.b Z) y) (LinearMap.toContinuousLinearMap (σ (ρ.b Z))) x :=
    (LinearMap.toContinuousLinearMap (σ (ρ.b Z))).hasFDerivAt
  have h := (hq.const_mul (-(1 / 2 : ℝ))).sub hl
  refine h.congr_fderiv ?_
  ext v
  simp [vectorField]
  rw [hsym v x]
  ring

/-- (11.7): `σ(Z_E(x)) = -∇[μ.Z]`, the derivative of `x ↦ μ.Z` at `x` is `v ↦ -σ (Z_E x) v`. -/
lemma hasFDerivAt_moment (hσ : IsSymplecticForm σ) (Z : g) (x : E) :
    HasFDerivAt (fun y => ρ.moment y Z)
      (-(LinearMap.toContinuousLinearMap (σ (ρ.vectorField Z x)))) x :=
  ρ.hasFDerivAt_moment_of_symm Z (ρ.sigma_A_symm hσ Z) x

/-- (11.9): `Z_E` is the symplectic gradient of `μ.Z`. -/
lemma vectorField_isSymplecticGradient (hσ : IsSymplecticForm σ) (Z : g) :
    IsSymplecticGradient σ (fun y => ρ.moment y Z) (ρ.vectorField Z) := by
  intro x v
  rw [(ρ.hasFDerivAt_moment hσ Z x).fderiv]
  simp

/-- The derivative of the affine map `x ↦ -σ (Z_E x)` (with values in `E →L[ℝ] ℝ`) is `-sigmaA`. -/
lemma hasFDerivAt_negSigmaVectorField (Z : g) (x : E) :
    HasFDerivAt (fun y => -(LinearMap.toContinuousLinearMap (σ (ρ.vectorField Z y))))
      (-(ρ.sigmaA Z)) x := by
  have h : HasFDerivAt (fun y => ρ.sigmaA Z y + ρ.sigmaB Z) (ρ.sigmaA Z) x :=
    (ρ.sigmaA Z).hasFDerivAt.add_const _
  refine (h.neg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  ext v
  simp [vectorField]

/-- (11.8 a): two moments of the same action differ by a constant torsor (`E` is connected). Any `ψ`
satisfying (11.7) equals `μ + c`, `Z` by `Z`. No alternation of `σ` is needed: the symmetry of the
second derivative of `ψ` gives `σ (A Z v) w = σ (A Z w) v`. -/
lemma moment_unique (ψ : E → g → ℝ)
    (hψ : ∀ Z x, HasFDerivAt (fun y => ψ y Z)
      (-(LinearMap.toContinuousLinearMap (σ (ρ.vectorField Z x)))) x) (Z : g) :
    ∃ c : ℝ, ∀ x, ψ x Z = ρ.moment x Z + c := by
  have hsym : ∀ v w, σ (ρ.A Z v) w = σ (ρ.A Z w) v := by
    intro v w
    have h := second_derivative_symmetric (f := fun y => ψ y Z)
      (f' := fun y => -(LinearMap.toContinuousLinearMap (σ (ρ.vectorField Z y)))) (hψ Z)
      (ρ.hasFDerivAt_negSigmaVectorField Z 0) v w
    simpa using h
  have hd : ∀ x, HasFDerivAt (fun y => ψ y Z - ρ.moment y Z) 0 x := fun x => by
    have h := (hψ Z x).sub (ρ.hasFDerivAt_moment_of_symm Z hsym x)
    rw [sub_self] at h
    exact h
  refine ⟨ψ 0 Z - ρ.moment 0 Z, fun x => ?_⟩
  have hc : ψ x Z - ρ.moment x Z = ψ 0 Z - ρ.moment 0 Z :=
    is_const_of_fderiv_eq_zero (f := fun y => ψ y Z - ρ.moment y Z)
      (fun y => (hd y).differentiableAt) (fun y => (hd y).fderiv) x 0
  linarith

/-- (11.17 d, ♠): `D(ψ)(x)(Z_E(x)) = ψ(x).ad(Z) + f(Z)`, evaluated on `Z'`: the infinitesimal
equivariance of the moment, up to the cocycle. -/
lemma fderiv_moment_vectorField (hσ : IsSymplecticForm σ) (Z Z' : g) (x : E) :
    fderiv ℝ (fun y => ρ.moment y Z') x (ρ.vectorField Z x) =
      coadjoint Z (ρ.moment x) Z' + ρ.cocycle Z Z' := by
  rw [(ρ.hasFDerivAt_moment hσ Z' x).fderiv]
  have e : (-(LinearMap.toContinuousLinearMap (σ (ρ.vectorField Z' x)))) (ρ.vectorField Z x) =
      -(σ (ρ.vectorField Z' x) (ρ.vectorField Z x)) := by simp
  rw [e, hσ.alt.neg_eq, ρ.sigma_vectorField_vectorField hσ Z Z' x]
  rfl

/-- (11.8 c): `σ([Z, Z']_E(x)) = -∇[σ(Z_E(x))(Z'_E(x))]`, an identity valid for every dynamical
group. -/
lemma sigma_vectorField_bracket (hσ : IsSymplecticForm σ) (Z Z' : g) (x v : E) :
    σ (ρ.vectorField ⁅Z, Z'⁆ x) v =
      -(fderiv ℝ (fun y => σ (ρ.vectorField Z y) (ρ.vectorField Z' y)) x v) := by
  have hc : HasFDerivAt (fun y => ρ.sigmaA Z y + ρ.sigmaB Z) (ρ.sigmaA Z) x :=
    (ρ.sigmaA Z).hasFDerivAt.add_const _
  have hu : HasFDerivAt (fun y => LinearMap.toContinuousLinearMap (ρ.A Z') y + ρ.b Z')
      (LinearMap.toContinuousLinearMap (ρ.A Z')) x :=
    (LinearMap.toContinuousLinearMap (ρ.A Z')).hasFDerivAt.add_const _
  have h := hc.clm_apply hu
  have h' : HasFDerivAt (fun y => σ (ρ.vectorField Z y) (ρ.vectorField Z' y))
      ((ρ.sigmaA Z x + ρ.sigmaB Z).comp (LinearMap.toContinuousLinearMap (ρ.A Z')) +
        (ρ.sigmaA Z).flip (LinearMap.toContinuousLinearMap (ρ.A Z') x + ρ.b Z')) x := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [vectorField]
  rw [h'.fderiv]
  simp only [vectorField, ρ.map_bracket_A, ρ.map_bracket_b, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, sigmaA_apply, sigmaB_apply,
    LinearMap.coe_toContinuousLinearMap', LinearMap.sub_apply, LinearMap.comp_apply, map_add,
    map_sub, LinearMap.add_apply]
  have e1 : σ (ρ.A Z x + ρ.b Z) (ρ.A Z' v) = -σ (ρ.A Z' (ρ.A Z x + ρ.b Z)) v := by
    rw [ρ.sigma_A_left Z' (ρ.A Z x + ρ.b Z) v, neg_neg]
  have e2 : σ (ρ.A Z v) (ρ.A Z' x + ρ.b Z') = σ (ρ.A Z (ρ.A Z' x + ρ.b Z')) v := by
    rw [ρ.sigma_A_left Z, hσ.alt.neg_eq]
  simp only [map_add, LinearMap.add_apply] at e1 e2
  linarith

/-!

## E. Noether's theorem

(11.12) states that a moment is constant on each leaf of the presymplectic evolution space. On `E`,
for a Hamiltonian flow `γ' = X ∘ γ` with `X` the symplectic gradient of an `H` invariant under
`Z_E`, this says that `μ.Z ∘ γ` is constant.

-/

/-- (11.12), Noether's theorem: along a motion of a Hamiltonian `H` invariant under `Z_E`, the
component `μ.Z` of the moment has zero derivative. -/
lemma noether (hσ : IsSymplecticForm σ) (H : E → ℝ) (X : E → E) (hX : IsSymplecticGradient σ H X)
    (Z : g) (hinv : ∀ x, fderiv ℝ H x (ρ.vectorField Z x) = 0)
    (γ : ℝ → E) (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) (t : ℝ) :
    HasDerivAt (fun s => ρ.moment (γ s) Z) 0 t := by
  have h := (ρ.hasFDerivAt_moment hσ Z (γ t)).comp_hasDerivAt t (hγ t)
  have e : σ (X (γ t)) (ρ.vectorField Z (γ t)) = 0 := by
    rw [hX (γ t) (ρ.vectorField Z (γ t)), hinv (γ t), neg_zero]
  have e2 : (-(LinearMap.toContinuousLinearMap (σ (ρ.vectorField Z (γ t))))) (X (γ t)) = 0 := by
    have e3 : (-(LinearMap.toContinuousLinearMap (σ (ρ.vectorField Z (γ t))))) (X (γ t)) =
        -(σ (ρ.vectorField Z (γ t)) (X (γ t))) := by simp
    rw [e3, hσ.alt.neg_eq, e]
  rw [e2] at h
  exact h

/-- (11.12) as a conservation law: `μ.Z` takes the same value at any two instants of a motion. -/
lemma noether_const (hσ : IsSymplecticForm σ) (H : E → ℝ) (X : E → E)
    (hX : IsSymplecticGradient σ H X) (Z : g) (hinv : ∀ x, fderiv ℝ H x (ρ.vectorField Z x) = 0)
    (γ : ℝ → E) (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) (t s : ℝ) :
    ρ.moment (γ t) Z = ρ.moment (γ s) Z :=
  is_const_of_deriv_eq_zero (f := fun s => ρ.moment (γ s) Z)
    (fun u => (ρ.noether hσ H X hX Z hinv γ hγ u).differentiableAt)
    (fun u => (ρ.noether hσ H X hX Z hinv γ hγ u).deriv) t s

end AffineSymplecticAction

/-!

## F. The plane: translations and a non-trivial cohomology class

The standard symplectic form of `ℝ × ℝ` and the translations `x ↦ x + Z`, whose vector fields are
constant, `Z_E(x) = Z`: their cocycle is `σ(Z, Z')` itself, which is not a coboundary (the Lie
algebra is abelian, so every coboundary vanishes). This is the simplest instance of (11.20)-(11.21):
no invariant potential exists, and no moment of the translations is equivariant.

-/

/-- `ℝ × ℝ` as an abelian Lie ring (the commutator bracket of the product ring, which vanishes). -/
instance instLieRingPlane : LieRing (ℝ × ℝ) := LieRing.ofAssociativeRing

/-- `ℝ × ℝ` as an abelian real Lie algebra. -/
instance instLieAlgebraPlane : LieAlgebra ℝ (ℝ × ℝ) := LieAlgebra.ofAssociativeAlgebra

/-- The standard symplectic form of the plane, `σ((a, b), (c, d)) = a d - b c`. -/
def planeForm : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun v w => v.1 * w.2 - v.2 * w.1)
    (by intros; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (by intros; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

/-- The translations `x ↦ x + Z` of the plane: `A = 0`, `b = id`, so `Z_E(x) = Z`. -/
def planeTranslations : AffineSymplecticAction planeForm (ℝ × ℝ) where
  A := 0
  b := LinearMap.id
  infinitesimallySymplectic := by intros; simp [planeForm]
  map_bracket_A := by intros; simp
  map_bracket_b := by intros; simp [LieRing.of_associative_ring_bracket, mul_comm]

/-- `planeForm` is symplectic. -/
lemma isSymplecticForm_planeForm : IsSymplecticForm planeForm := by
  refine ⟨fun v => ?_, ?_⟩
  · simp [planeForm]
    ring
  · refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · have h1 := hv (0, 1)
      have h2 := hv (1, 0)
      simp [planeForm] at h1 h2
      exact Prod.ext (by simpa using h1) (by simpa using h2)
    · have h1 := hw (0, 1)
      have h2 := hw (1, 0)
      simp [planeForm] at h1 h2
      exact Prod.ext (by simpa using h1) (by simpa using h2)

/-- (11.17 c), (11.20): for the translations of the plane the cocycle is `σ(Z, Z')`, so
`f((1, 0))((0, 1)) = 1`. -/
lemma planeTranslations_cocycle : planeTranslations.cocycle (1, 0) (0, 1) = 1 := by
  simp [AffineSymplecticAction.cocycle, planeTranslations, planeForm]

/-- (11.21): the cocycle of the translations is not a coboundary: the cohomology class of the
translations of the plane is not zero. -/
lemma planeTranslations_not_coboundary :
    ¬ ∃ μ₀ : Dual ℝ (ℝ × ℝ), ∀ Z Z', planeTranslations.cocycle Z Z' = coadjoint Z μ₀ Z' := by
  rintro ⟨μ₀, h⟩
  have := h (1, 0) (0, 1)
  rw [planeTranslations_cocycle] at this
  simp [coadjoint, LieRing.of_associative_ring_bracket] at this

end ClassicalMechanics

end
