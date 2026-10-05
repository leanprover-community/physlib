/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import PhyslibAlpha.ClassicalMechanics.MomentMap.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
/-!

# The cohomology class of the affine symplectic group

The moment cocycle of the affine symplectic group has a non-zero cohomology class.

## i. Overview

Souriau (Structure des systemes dynamiques, Dunod 1970, chapter 11) attaches to a dynamical group
`G` acting on a connected symplectic (or presymplectic) manifold `V` with moment `μ` a map
`θ : G → 𝔤*`, `θ(a) = μ(a_V(x)) - a_{𝔤*}(μ(x))` (11.17 a), which by connectedness does not depend
on `x` and satisfies the cocycle identity `θ(a × b) = θ(a) + a_{𝔤*}(θ(b))` (11.17 b). Its
cohomology class does not depend on the choice of the moment (11.18), (11.20), and it vanishes
when a `G`-invariant potential exists (11.21).

This file proves the following for the group of Souriau's example (10.12), the affine symplectic
group `Sp(E) ⋉ E` of a real symplectic vector space `E`, acting by `x ↦ B x + C`, with the moment
`moment` of (11.7): the defect `θ(a)` does not depend on `x` and equals `μ(C)` (a computation here,
not a consequence of connectedness), `θ` is a 1-cocycle of the coadjoint action, its derivative
at the identity along a curve is the Lie algebra cocycle of
`PhyslibAlpha.ClassicalMechanics.MomentMap.Basic`, and its cohomology class is not zero. It does NOT
prove (11.18), (11.20) or (11.21): by (11.21) the non-zero class means that no potential of `σ` is
invariant under this group, but that implication is Souriau's and is not formalised here.

The Lie algebra is the space of pairs `(A, b)` with `A` infinitesimally symplectic, acting by the
affine vector fields `Z_E(x) = A x + b`; only its module structure is used, and no Lean term
relates it to `AffineSymplecticAction` (the link with its cocycle is by formula). The adjoint
action is given by the formula of `adjoint` and characterised by the identity `vectorField_adjoint`
of (6.25); the coadjoint action `a_{𝔤*}(μ) = μ ∘ Ad(a⁻¹)` of (11.15) is a `MulAction` on the
dual.

The cocycle notions are Mathlib's: `θ` is a `groupCohomology.IsCocycle₁` for the coadjoint action,
and "the class is non-zero" is `¬ groupCohomology.IsCoboundary₁`. Souriau's differentiability
requirement on `θ` is not formalised: the group here carries no manifold structure, and `θ` is
given by a closed formula.

## ii. Key results

- `vectorField_adjoint`: (6.25), `(Ad(a) Z)_E (a_E x) = B (Z_E x)`, which characterises `adjoint`
  together with `vectorField_injective`.
- `moment_smul_sub_smul_moment`: (11.17 a) in closed form, `μ(a_E(x)) - a_{𝔤*}(μ(x)) = μ(C)`: the
  defect `θ(a)` does not depend on `x`, and is the moment at the point `a_E(0) = C`.
- `isCocycle₁_moment_translation`: (11.17 b), `θ` is a 1-cocycle of the coadjoint action.
- `hasDerivAt_moment_translation`: part of (11.17 c), the derivative of `θ` at the identity along a
  curve whose translation part has velocity `b'` is `σ (b', b Z)`, the value of
  `AffineSymplecticAction.cocycle` (the 2-form property and ♣ of (11.17 c) are not proved here).
- `not_isCoboundary₁_moment_translation`: the cohomology class of the affine symplectic group is
  non-zero as soon as `E ≠ 0`.

## iii. Table of contents

- A. The affine symplectic group
- B. Its Lie algebra and the adjoint action
- C. The coadjoint action and the moment
- D. The cohomology class
- E. The plane

## iv. References

- J.-M. Souriau, Structure des systemes dynamiques, Dunod, Paris, 1970: chapter 11,
  pp. 104-117, for (11.7), (11.15)-(11.21) and (11.28); (6.24)-(6.25) and (10.12),
  (10.28)-(10.32) for the adjoint action and the affine symplectic group.

* J.-M. Souriau, *Structure des systèmes dynamiques*, Maîtrises de mathématiques, Dunod,
  Paris, 1970, chapter 11, pp. 104-117, and (6.24)-(6.25), (10.12). The
  equation numbers refer to this edition. [ref: Souriau1970]

-/

@[expose] public section

noncomputable section

namespace ClassicalMechanics

open Module

/-!

## A. The affine symplectic group

The affine symplectomorphisms `x ↦ B x + C` of (10.12), with `B` linear symplectic.

-/

/-- The affine symplectic group of a bilinear form `σ` on `E`: the affine maps `x ↦ B x + C` with
`B` a linear equivalence preserving `σ` (Souriau (10.12)). -/
structure AffineSymplecticGroup {E : Type} [AddCommGroup E] [Module ℝ E]
    (σ : LinearMap.BilinForm ℝ E) where
  /-- The linear part `B`. -/
  linear : E ≃ₗ[ℝ] E
  /-- The translation part `C`. -/
  translation : E
  /-- The linear part preserves `σ`. -/
  map_symplecticForm : ∀ v w, σ (linear v) (linear w) = σ v w

namespace AffineSymplecticGroup

variable {E : Type} [AddCommGroup E] [Module ℝ E] {σ : LinearMap.BilinForm ℝ E}

instance : Mul (AffineSymplecticGroup σ) :=
  ⟨fun a b => ⟨b.linear.trans a.linear, a.linear b.translation + a.translation, fun v w => by
    simp only [LinearEquiv.trans_apply, a.map_symplecticForm, b.map_symplecticForm]⟩⟩

instance : One (AffineSymplecticGroup σ) := ⟨⟨LinearEquiv.refl ℝ E, 0, fun _ _ => rfl⟩⟩

instance : Inv (AffineSymplecticGroup σ) :=
  ⟨fun a => ⟨a.linear.symm, -(a.linear.symm a.translation), fun v w => by
    have h := a.map_symplecticForm (a.linear.symm v) (a.linear.symm w)
    simpa using h.symm⟩⟩

@[simp]
lemma mul_linear (a b : AffineSymplecticGroup σ) : (a * b).linear = b.linear.trans a.linear := rfl

@[simp]
lemma mul_translation (a b : AffineSymplecticGroup σ) :
    (a * b).translation = a.linear b.translation + a.translation := rfl

@[simp]
lemma one_linear : (1 : AffineSymplecticGroup σ).linear = LinearEquiv.refl ℝ E := rfl

@[simp]
lemma one_translation : (1 : AffineSymplecticGroup σ).translation = 0 := rfl

@[simp]
lemma inv_linear (a : AffineSymplecticGroup σ) : a⁻¹.linear = a.linear.symm := rfl

@[simp]
lemma inv_translation (a : AffineSymplecticGroup σ) :
    a⁻¹.translation = -(a.linear.symm a.translation) := rfl

/-- Two elements with the same linear and translation parts are equal. -/
@[ext]
lemma ext {a b : AffineSymplecticGroup σ} (hl : a.linear = b.linear)
    (ht : a.translation = b.translation) : a = b := by
  cases a
  cases b
  simp_all

instance : Group (AffineSymplecticGroup σ) where
  mul_assoc a b c := by
    refine ext (by rfl) ?_
    simp only [mul_translation, mul_linear, LinearEquiv.trans_apply, map_add, add_assoc]
  one_mul a := by
    refine ext (by rfl) ?_
    simp
  mul_one a := by
    refine ext (by rfl) ?_
    simp
  inv_mul_cancel a := by
    refine ext ?_ ?_
    · ext v
      simp
    · simp

/-- The affine symplectic group acts on `E` by `a_E(x) = B x + C` (10.12). -/
instance : MulAction (AffineSymplecticGroup σ) E where
  smul a x := a.linear x + a.translation
  one_smul x := by
    change (1 : AffineSymplecticGroup σ).linear x + (1 : AffineSymplecticGroup σ).translation = x
    simp
  mul_smul a b x := by
    change (a * b).linear x + (a * b).translation
      = a.linear (b.linear x + b.translation) + a.translation
    simp only [mul_linear, mul_translation, LinearEquiv.trans_apply, map_add, add_assoc]

lemma smul_def (a : AffineSymplecticGroup σ) (x : E) : a • x = a.linear x + a.translation := rfl

end AffineSymplecticGroup

/-!

## B. Its Lie algebra and the adjoint action

The pairs `(A, b)` with `A` infinitesimally symplectic, acting by the affine vector fields
`Z_E(x) = A x + b` of `AffineSymplecticAction`; the adjoint action of (6.24) is characterised by
(6.25). Only the module structure is used here: the Lie bracket of Souriau's (11.22 a) lives on
the abstract Lie algebra of `AffineSymplecticAction`.

-/

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- The Lie algebra of the affine symplectic group: the pairs `(A, b)` with `A` infinitesimally
symplectic ((10.28)-(10.32)). -/
def affineSymplecticAlgebra (σ : LinearMap.BilinForm ℝ E) : Submodule ℝ ((E →ₗ[ℝ] E) × E) where
  carrier := {Z | ∀ v w, σ (Z.1 v) w + σ v (Z.1 w) = 0}
  add_mem' := by
    intro Z Z' hZ hZ' v w
    have h1 := hZ v w
    have h2 := hZ' v w
    simp only [Prod.fst_add, LinearMap.add_apply, map_add]
    linarith
  zero_mem' := by
    intro v w
    simp
  smul_mem' := by
    intro c Z hZ v w
    have h := hZ v w
    simp only [Prod.smul_fst, LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [← mul_add, h, mul_zero]

variable {σ : LinearMap.BilinForm ℝ E}

lemma mem_affineSymplecticAlgebra {Z : (E →ₗ[ℝ] E) × E} :
    Z ∈ affineSymplecticAlgebra σ ↔ ∀ v w, σ (Z.1 v) w + σ v (Z.1 w) = 0 := Iff.rfl

/-- The affine vector field `Z_E(x) = A x + b` of `Z = (A, b)`, as in `AffineSymplecticAction`. -/
def vectorField (Z : affineSymplecticAlgebra σ) (x : E) : E := Z.1.1 x + Z.1.2

/-- The adjoint action (6.24): `Ad(a)(A, b) = (B A B⁻¹, B b - B A B⁻¹ C)` for `a = (B, C)`. -/
def adjoint (a : AffineSymplecticGroup σ) :
    affineSymplecticAlgebra σ →ₗ[ℝ] affineSymplecticAlgebra σ where
  toFun Z := ⟨(a.linear.toLinearMap ∘ₗ Z.1.1 ∘ₗ a.linear.symm.toLinearMap,
      a.linear Z.1.2 - a.linear (Z.1.1 (a.linear.symm a.translation))), by
    rw [mem_affineSymplecticAlgebra]
    intro v w
    have h := Z.2 (a.linear.symm v) (a.linear.symm w)
    rw [← a.map_symplecticForm (Z.1.1 (a.linear.symm v)) (a.linear.symm w),
      ← a.map_symplecticForm (a.linear.symm v) (Z.1.1 (a.linear.symm w))] at h
    simpa using h⟩
  map_add' Z Z' := by
    refine Subtype.ext (Prod.ext (LinearMap.ext fun v => ?_) ?_)
    · simp
    · simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      abel
  map_smul' c Z := by
    refine Subtype.ext (Prod.ext (LinearMap.ext fun v => ?_) ?_)
    · simp
    · simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
        RingHom.id_apply, smul_sub]

@[simp]
lemma adjoint_one : adjoint (1 : AffineSymplecticGroup σ) = LinearMap.id := by
  refine LinearMap.ext fun Z => Subtype.ext (Prod.ext (LinearMap.ext fun v => rfl) ?_)
  change Z.1.2 - Z.1.1 0 = Z.1.2
  simp

lemma adjoint_mul (a b : AffineSymplecticGroup σ) :
    adjoint (a * b) = adjoint a ∘ₗ adjoint b := by
  refine LinearMap.ext fun Z => Subtype.ext (Prod.ext (LinearMap.ext fun v => rfl) ?_)
  change (b.linear.trans a.linear) Z.1.2
      - (b.linear.trans a.linear) (Z.1.1 ((b.linear.trans a.linear).symm
        (a.linear b.translation + a.translation)))
    = a.linear (b.linear Z.1.2 - b.linear (Z.1.1 (b.linear.symm b.translation)))
      - a.linear (b.linear (Z.1.1 (b.linear.symm (a.linear.symm a.translation))))
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, map_add,
    LinearEquiv.symm_apply_apply, map_sub]
  abel

/-- (6.25): the adjoint action is the one for which `(Ad(a) Z)_E (a_E x) = B (Z_E x)`. With
`vectorField_injective` this characterises `adjoint`. -/
lemma vectorField_adjoint (a : AffineSymplecticGroup σ) (Z : affineSymplecticAlgebra σ) (x : E) :
    vectorField (adjoint a Z) (a • x) = a.linear (vectorField Z x) := by
  dsimp only [vectorField]
  have hA : (adjoint a Z).1.1
      = a.linear.toLinearMap ∘ₗ Z.1.1 ∘ₗ a.linear.symm.toLinearMap := rfl
  have hb : (adjoint a Z).1.2
      = a.linear Z.1.2 - a.linear (Z.1.1 (a.linear.symm a.translation)) := rfl
  rw [hA, hb, AffineSymplecticGroup.smul_def, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap]
  have hsym : a.linear.symm (a.linear x + a.translation) = x + a.linear.symm a.translation := by
    rw [map_add, LinearEquiv.symm_apply_apply]
  rw [hsym, map_add, map_add, map_add]
  abel

/-- An element of the Lie algebra is determined by its vector field. -/
lemma vectorField_injective {Z Z' : affineSymplecticAlgebra σ}
    (h : ∀ x, vectorField Z x = vectorField Z' x) : Z = Z' := by
  have h0 : Z.1.2 = Z'.1.2 := by
    have := h 0
    simpa [vectorField] using this
  refine Subtype.ext (Prod.ext (LinearMap.ext fun x => ?_) h0)
  have hx := h x
  rw [vectorField, vectorField, h0] at hx
  exact add_right_cancel hx

/-!

## C. The coadjoint action and the moment

The coadjoint action of (11.15), `a_{𝔤*}(μ) = μ ∘ Ad(a⁻¹)`, and the moment of (11.7), which is the
moment of `AffineSymplecticAction` read on the pairs `(A, b)`.

-/

/-- (11.15): the coadjoint action `a_{𝔤*}(μ) = μ.a_𝔤⁻¹`, that is `μ ∘ Ad(a⁻¹)`. -/
instance : SMul (AffineSymplecticGroup σ) (Dual ℝ (affineSymplecticAlgebra σ)) :=
  ⟨fun a μ => μ ∘ₗ adjoint a⁻¹⟩

@[simp]
lemma coadjoint_smul_apply (a : AffineSymplecticGroup σ) (μ : Dual ℝ (affineSymplecticAlgebra σ))
    (Z : affineSymplecticAlgebra σ) : (a • μ) Z = μ (adjoint a⁻¹ Z) := rfl

instance : MulAction (AffineSymplecticGroup σ) (Dual ℝ (affineSymplecticAlgebra σ)) where
  one_smul μ := by
    refine LinearMap.ext fun Z => ?_
    simp
  mul_smul a b μ := by
    refine LinearMap.ext fun Z => ?_
    simp [mul_inv_rev, adjoint_mul]

instance : DistribMulAction (AffineSymplecticGroup σ) (Dual ℝ (affineSymplecticAlgebra σ)) where
  smul_zero a := by
    refine LinearMap.ext fun Z => ?_
    simp
  smul_add a μ ν := by
    refine LinearMap.ext fun Z => ?_
    simp

/-- (11.7): the moment of the affine symplectic action, `μ(x)(A, b) = -½ σ(A x, x) - σ(b, x)`, the
moment of `AffineSymplecticAction` read on the pairs `(A, b)`. -/
def moment (σ : LinearMap.BilinForm ℝ E) (x : E) : Dual ℝ (affineSymplecticAlgebra σ) where
  toFun Z := -(1 / 2 : ℝ) * σ (Z.1.1 x) x - σ Z.1.2 x
  map_add' Z Z' := by
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
    ring
  map_smul' c Z := by
    simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, LinearMap.smul_apply, map_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
lemma moment_apply (x : E) (Z : affineSymplecticAlgebra σ) :
    moment σ x Z = -(1 / 2 : ℝ) * σ (Z.1.1 x) x - σ Z.1.2 x := rfl

@[simp]
lemma moment_zero : moment σ (0 : E) = 0 := by
  refine LinearMap.ext fun Z => ?_
  simp

/-!

## D. The cohomology class

(11.17 a) in closed form, (11.17 b), (11.17 c) and the non-vanishing of the class.

-/

/-- (11.17 a) in closed form: for this moment, the defect `θ(a) = μ(a_E(x)) - a_{𝔤*}(μ(x))` does
not depend on the point `x`, and equals the moment at `a_E(0) = C`. The terms in `x` cancel by the
infinitesimal symplecticity of `A` and the alternation of `σ`. -/
lemma moment_smul_sub_smul_moment (hσ : IsSymplecticForm σ) (x : E)
    (a : AffineSymplecticGroup σ) :
    moment σ (a • x) - a • moment σ x = moment σ a.translation := by
  refine LinearMap.ext fun Z => ?_
  have alt (u v : E) : σ u v = -σ v u := (hσ.alt.neg_eq v u).symm
  have hB : ∀ u v, σ (a.linear.symm u) v = σ u (a.linear v) := by
    intro u v
    rw [← a.map_symplecticForm (a.linear.symm u) v, LinearEquiv.apply_symm_apply]
  have h1 : σ (Z.1.1 (a.linear x)) a.translation
      + σ (a.linear x) (Z.1.1 a.translation) = 0 := Z.2 (a.linear x) a.translation
  have h1' : σ (Z.1.1 (a.linear x)) a.translation = σ (Z.1.1 a.translation) (a.linear x) := by
    rw [alt (a.linear x) (Z.1.1 a.translation)] at h1
    exact sub_eq_zero.mp h1
  simp only [LinearMap.sub_apply, coadjoint_smul_apply, moment_apply,
    AffineSymplecticGroup.smul_def]
  simp [adjoint, map_add]
  rw [hB (Z.1.1 (a.linear x)) x, hB Z.1.2 x, hB (Z.1.1 a.translation) x, h1']
  ring

/-- (11.17 b): `θ(a) = μ(C)` is a 1-cocycle of the coadjoint action,
`θ(a × b) = θ(a) + a_{𝔤*}(θ(b))`. -/
lemma isCocycle₁_moment_translation (hσ : IsSymplecticForm σ) :
    groupCohomology.IsCocycle₁ (fun a : AffineSymplecticGroup σ => moment σ a.translation) := by
  intro a b
  show moment σ (a * b).translation
    = a • moment σ b.translation + moment σ a.translation
  have h := moment_smul_sub_smul_moment hσ b.translation a
  have hab : (a * b).translation = a • b.translation := by
    rw [AffineSymplecticGroup.smul_def]
    rfl
  rw [hab, ← h]
  abel

/-- `y ↦ σ (A y)` as a continuous linear map from `E` to `E →L[ℝ] ℝ`, used to differentiate the
quadratic part of the moment. -/
def sigmaLinear {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (σ : LinearMap.BilinForm ℝ E) (A : E →ₗ[ℝ] E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ σ ∘ₗ A)

@[simp]
lemma sigmaLinear_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (σ : LinearMap.BilinForm ℝ E) (A : E →ₗ[ℝ] E) (y v : E) :
    sigmaLinear σ A y v = σ (A y) v := by
  simp [sigmaLinear]

/-- The derivative of `y ↦ σ (A y) y` at `x` is `v ↦ σ (A v) x + σ (A x) v`. -/
lemma hasFDerivAt_quad {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (σ : LinearMap.BilinForm ℝ E) (A : E →ₗ[ℝ] E) (x : E) :
    HasFDerivAt (fun y => σ (A y) y)
      ((sigmaLinear σ A x).comp (ContinuousLinearMap.id ℝ E) + (sigmaLinear σ A).flip x) x := by
  have h := (sigmaLinear σ A).hasFDerivAt (x := x)
  have h2 := hasFDerivAt_id (𝕜 := ℝ) x
  refine (h.clm_apply h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp

/-- (11.7) for the affine symplectic group: `σ(Z_E(x)) = -∇[μ.Z]`. -/
lemma hasFDerivAt_moment {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {σ : LinearMap.BilinForm ℝ E} (hσ : IsSymplecticForm σ)
    (Z : affineSymplecticAlgebra σ) (x : E) :
    HasFDerivAt (fun y => moment σ y Z)
      (-(LinearMap.toContinuousLinearMap (σ (vectorField Z x)))) x := by
  have hsym : ∀ v w : E, σ (Z.1.1 v) w = σ (Z.1.1 w) v := by
    intro v w
    rw [eq_neg_of_add_eq_zero_left (Z.2 v w), hσ.alt.neg_eq]
  have hlin : HasFDerivAt (fun y => σ Z.1.2 y)
      (LinearMap.toContinuousLinearMap (σ Z.1.2)) x :=
    (LinearMap.toContinuousLinearMap (σ Z.1.2)).hasFDerivAt
  refine (((hasFDerivAt_quad σ Z.1.1 x).const_mul (-(1 / 2 : ℝ))).sub hlin).congr_fderiv ?_
  ext v
  simp [vectorField]
  rw [hsym v x]
  ring

/-- Part of (11.17 c): along any curve of the group issued from the identity whose translation part
has velocity `b'`, the derivative of `θ = μ(C)` at the identity is `σ (b', b Z)`, which is the value
of `AffineSymplecticAction.cocycle` on the corresponding pairs (a relation by formula: no Lean term
relates the two Lie algebras). -/
lemma hasDerivAt_moment_translation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {σ : LinearMap.BilinForm ℝ E} (hσ : IsSymplecticForm σ)
    (γ : ℝ → AffineSymplecticGroup σ) (hγ : γ 0 = 1) (b' : E)
    (hC : HasDerivAt (fun t => (γ t).translation) b' 0) (Z : affineSymplecticAlgebra σ) :
    HasDerivAt (fun t => moment σ (γ t).translation Z) (σ b' Z.1.2) 0 := by
  have h0 : (γ 0).translation = 0 := by rw [hγ]; rfl
  refine ((hasFDerivAt_moment hσ Z ((γ 0).translation)).comp_hasDerivAt 0 hC).congr_deriv ?_
  simp only [neg_apply, LinearMap.coe_toContinuousLinearMap']
  rw [h0]
  have hv : vectorField Z (0 : E) = Z.1.2 := by simp [vectorField]
  rw [hv, hσ.alt.neg_eq]

/-- The cohomology class of the affine symplectic group of a non-zero symplectic vector space is
NOT zero: `θ` is not a coboundary. On the translations `(id, C)` the coadjoint action fixes the
elements `(0, b)` of the Lie algebra, so every coboundary vanishes on them, whereas
`θ((id, C))(0, b) = -σ (b, C)`, which is non-zero for a suitable `b` by non-degeneracy. (By
Souriau's (11.21) this forbids a potential of `σ` invariant under the group; that implication is
not formalised here.) -/
lemma not_isCoboundary₁_moment_translation (hσ : IsSymplecticForm σ) (hE : ∃ v : E, v ≠ 0) :
    ¬ groupCohomology.IsCoboundary₁
      (fun a : AffineSymplecticGroup σ => moment σ a.translation) := by
  rintro ⟨μ, hμ⟩
  obtain ⟨v, hv⟩ := hE
  obtain ⟨w, hsw⟩ : ∃ w : E, σ v w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (hσ.nondeg.1 v h)
  let a : AffineSymplecticGroup σ := ⟨LinearEquiv.refl ℝ E, w, fun _ _ => rfl⟩
  let Z : affineSymplecticAlgebra σ := ⟨(0, v), by simp [mem_affineSymplecticAlgebra]⟩
  have hZ : adjoint a⁻¹ Z = Z := by
    refine Subtype.ext (Prod.ext (LinearMap.ext fun u => ?_) ?_)
    · show a.linear.symm (Z.1.1 (a.linear.symm.symm u)) = Z.1.1 u
      simp [a, Z]
    · show a.linear.symm Z.1.2
          - a.linear.symm (Z.1.1 (a.linear.symm.symm a⁻¹.translation)) = Z.1.2
      simp [a, Z]
  have hk := congrArg (fun φ : Dual ℝ (affineSymplecticAlgebra σ) => φ Z) (hμ a)
  simp only [LinearMap.sub_apply, coadjoint_smul_apply, hZ, sub_self] at hk
  rw [show moment σ a.translation Z = -σ v w by simp [a, Z]] at hk
  exact hsw (neg_eq_zero.mp hk.symm)

/-!

## E. The plane

The simplest instance: the standard symplectic plane, whose affine symplectic group has a non-zero
cohomology class. This is the group-level counterpart of `planeTranslations_not_coboundary`.

-/

/-- The affine symplectic group of the symplectic plane has a non-zero cohomology class. -/
lemma planeForm_not_isCoboundary₁ :
    ¬ groupCohomology.IsCoboundary₁
      (fun a : AffineSymplecticGroup planeForm => moment planeForm a.translation) :=
  not_isCoboundary₁_moment_translation isSymplecticForm_planeForm ⟨(1, 0), by simp⟩

end ClassicalMechanics
