/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.Commutant
public import PhyslibAlpha.ProbabilisticTheory.Representation.VectorMeasure

/-!

# Covariance of the spectral measure under a finite group of symmetries

A group acting on the translation group acts on its characters, and the spectral measure of a
covariant representation is covariant.

## i. Overview

Let a discrete abelian group `G` of translations be represented unitarily by `π`, and let a group
`P` act on `G` by automorphisms `φ p`. The group `P` acts on the characters of `G` by
`(p • χ)(g) = χ(φ(p⁻¹) g)`. A unitary representation `ρ` of `P` on the same space is *covariant*
when `ρ(p) π(g) ρ(p)⁻¹ = π(φ(p) g)`. Together `π` and `ρ` represent the semidirect product
`G ⋊ P`: for a crystal, `G` is the group of lattice translations and `P` its point group.

The spectral measure of a vector `ξ`, the distribution of `ξ` over the characters, is determined
by its Fourier transform `g ↦ ⟨ξ, π(g) ξ⟩`. Since the transform of `ρ(p) ξ` is that of `ξ`
composed with `φ(p⁻¹)`, the spectral measure of `ρ(p) ξ` is the pushforward of that of `ξ` under
the action of `p` on the characters. Consequently the spectral projection of the image of a set of
characters is carried to the image of the projection by `ρ(p)`:
`ρ(p) P(S) = P(p • S) ρ(p)`. The unitary `ρ(p)` carries the sector of total momenta in `S` onto the
sector of total momenta in `p • S`.

## ii. Key results

- `UnitaryRep.dualAct` : the action of a group of automorphisms on the characters.
- `UnitaryRep.vectorMeasure_rho` : the spectral measure of `ρ(p) ξ` is the pushforward of that of
  `ξ`.
- `UnitaryRep.rho_mul_projection` : `ρ(p) P(S) = P(p • S) ρ(p)`.

## iii. Table of contents

- A. The action on the characters
- B. Covariance of the spectral measure

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder InnerProductSpace

namespace QuantumMechanics

namespace UnitaryRep

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable {P : Type*} [Group P] (φ : P →* MulAut (Multiplicative G))

/-! ## A. The action on the characters -/

/-- The automorphism `φ p` of the translation group as a continuous homomorphism. -/
def autCont (p : P) : Multiplicative G →ₜ* Multiplicative G where
  toMonoidHom := (φ p).toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

/-- The action of `p` on a character `χ`: `(p • χ)(g) = χ(φ(p⁻¹) g)`. -/
def dualAct (p : P) : PontryaginDual (Multiplicative G) →ₜ* PontryaginDual (Multiplicative G) :=
  PontryaginDual.map (autCont φ p⁻¹)

lemma dualAct_apply (p : P) (χ : PontryaginDual (Multiplicative G)) (g : Multiplicative G) :
    dualAct φ p χ g = χ (φ p⁻¹ g) := rfl

lemma dualAct_mul (p q : P) (χ : PontryaginDual (Multiplicative G)) :
    dualAct φ (p * q) χ = dualAct φ p (dualAct φ q χ) := by
  refine ContinuousMonoidHom.ext fun g => ?_
  show χ (φ (p * q)⁻¹ g) = χ (φ q⁻¹ (φ p⁻¹ g))
  rw [mul_inv_rev, map_mul]
  rfl

lemma dualAct_one (χ : PontryaginDual (Multiplicative G)) : dualAct φ 1 χ = χ := by
  refine ContinuousMonoidHom.ext fun g => ?_
  show χ (φ 1⁻¹ g) = χ g
  rw [inv_one, map_one]
  rfl

/-- The action of `p` on the characters is a bijection. -/
def dualActEquiv (p : P) :
    PontryaginDual (Multiplicative G) ≃ PontryaginDual (Multiplicative G) where
  toFun := dualAct φ p
  invFun := dualAct φ p⁻¹
  left_inv χ := by rw [← dualAct_mul, inv_mul_cancel, dualAct_one]
  right_inv χ := by rw [← dualAct_mul, mul_inv_cancel, dualAct_one]

/-! ## B. Covariance of the spectral measure -/

section Covariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : Multiplicative G →* unitary (H →L[ℂ] H)) (ρ : P →* unitary (H →L[ℂ] H))
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- The representation `ρ` of `P` is covariant with respect to the translations `π` and the
action `φ`: `ρ(p) π(g) = π(φ(p) g) ρ(p)`. -/
def IsCovariantRep : Prop :=
  ∀ (p : P) (g : Multiplicative G), ρ p * π g = π (φ p g) * ρ p

lemma measurable_dualAct (p : P) : Measurable (dualAct φ p) :=
  (dualAct φ p).continuous_toFun.measurable

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [TopologicalSpace G] in
/-- A representation of a group `Q` acting on the translations, restricted to the translations,
is covariant when the group relation `s t(a) = t(φ(s) a) s` holds. -/
lemma isCovariantRep_comp {Q : Type*} [Group Q] (φ : Q →* MulAut (Multiplicative G))
    (U : Q →* unitary (H →L[ℂ] H)) (τ : Multiplicative G →* Q)
    (h : ∀ (s : Q) (a : Multiplicative G), s * τ a = τ (φ s a) * s) :
    IsCovariantRep φ (U.comp τ) U := fun s a => by
  simp only [MonoidHom.comp_apply, ← map_mul, h]

variable {π ρ φ}

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [TopologicalSpace G] in
/-- The matrix coefficient of the translated vector. -/
lemma inner_rho_translation (hcov : IsCovariantRep φ π ρ) (p : P) (g : Multiplicative G)
    (ξ : H) :
    ⟪((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H) ξ,
        ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) (((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H) ξ)⟫_ℂ
      = ⟪ξ, ((π (φ p⁻¹ g) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) ξ⟫_ℂ := by
  have h1 : ρ p⁻¹ * π g * ρ p = π (φ p⁻¹ g) := by
    rw [hcov p⁻¹ g, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have h2 : ((ρ p⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = star ((ρ p : unitary (H →L[ℂ] H)) :
      H →L[ℂ] H) := by
    rw [map_inv]; rfl
  have h3 := congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H) ξ) h1
  simp only [Submonoid.coe_mul, mul_apply_eq_comp, h2] at h3
  rw [← h3, ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_inner_right]

variable [Countable G]

/-- **The spectral measure of `ρ(p) ξ` is the pushforward of that of `ξ`** under the action of `p`
on the characters. -/
lemma vectorMeasure_rho (hcov : IsCovariantRep φ π ρ) (p : P) (ξ : H) :
    vectorMeasure π (((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H) ξ) =
      Measure.map (dualAct φ p) (vectorMeasure π ξ) := by
  symm
  refine eq_vectorMeasure_of_transform_eq π _ _ (fun g => ?_)
  rw [integral_map (measurable_dualAct φ p).aemeasurable
    (TauCeti.PontryaginDual.continuous_coe_eval_const (G := Multiplicative G) g
      ).aestronglyMeasurable]
  simp only [dualAct_apply]
  rw [inner_rho_translation hcov p g ξ, ← inner_eq_integral_vectorMeasure π ξ (φ p⁻¹ g)]

omit [Countable G] in
lemma norm_sq_projection (S : Set (PontryaginDual (Multiplicative G))) (hS : MeasurableSet S)
    (η : H) : ‖projection π S η‖ ^ 2 = (vectorMeasure π η S).toReal := by
  rw [vectorMeasure_apply π η hS, ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

omit [Countable G] in
lemma inner_projection_self (S : Set (PontryaginDual (Multiplicative G))) (η : H) :
    ⟪projection π S η, η⟫_ℂ = ((‖projection π S η‖ ^ 2 : ℝ) : ℂ) := by
  have h := projection_isStarProjection π S
  have : projection π S η = (projection π S) (projection π S η) := by
    conv_lhs => rw [← h.isIdempotentElem.eq]
    rfl
  calc ⟪projection π S η, η⟫_ℂ = ⟪(projection π S) (projection π S η), η⟫_ℂ := by rw [← this]
    _ = ⟪projection π S η, projection π S η⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        h.isSelfAdjoint.star_eq]
    _ = _ := by rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- **The spectral projections are covariant**: `ρ(p) P(S) = P(p • S) ρ(p)` for every measurable
set `S` of characters. The unitary `ρ(p)` carries the sector of momenta in `S` onto the sector of
momenta in `p • S`. -/
lemma rho_mul_projection (hcov : IsCovariantRep φ π ρ) (p : P)
    {S : Set (PontryaginDual (Multiplicative G))} (hS : MeasurableSet S) :
    ((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * projection π S =
      projection π (dualAct φ p '' S) * ((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
  set R : H →L[ℂ] H := ((ρ p : unitary (H →L[ℂ] H)) : H →L[ℂ] H) with hR
  have hRR : star R * R = 1 := Unitary.coe_star_mul_self (ρ p)
  have hRR' : R * star R = 1 := Unitary.coe_mul_star_self (ρ p)
  have hmeas : MeasurableSet (dualAct φ p '' S) := by
    have : dualAct φ p '' S = dualAct φ p⁻¹ ⁻¹' S := by
      ext χ
      constructor
      · rintro ⟨ψ, hψ, rfl⟩
        change dualAct φ p⁻¹ (dualAct φ p ψ) ∈ S
        rw [← dualAct_mul, inv_mul_cancel, dualAct_one]; exact hψ
      · intro h
        refine ⟨dualAct φ p⁻¹ χ, h, ?_⟩
        rw [← dualAct_mul, mul_inv_cancel, dualAct_one]
    rw [this]
    exact measurable_dualAct φ p⁻¹ hS
  have key : R * projection π S * star R = projection π (dualAct φ p '' S) := by
    refine sub_eq_zero.1 (ContinuousLinearMap.ext fun x =>
      LinearMap.congr_fun ((inner_map_self_eq_zero
        (R * projection π S * star R - projection π
          (dualAct φ p '' S)).toLinearMap).1 fun η => ?_) x)
    set ξ := star R η with hξ
    have hη : R ξ = η := by
      have := congrArg (fun T : H →L[ℂ] H => T η) hRR'
      simpa [hξ, mul_apply_eq_comp] using this
    have e1 : ⟪(R * projection π S * star R) η, η⟫_ℂ = ((‖projection π S ξ‖ ^ 2 : ℝ) : ℂ) := by
      calc ⟪(R * projection π S * star R) η, η⟫_ℂ = ⟪R (projection π S ξ), η⟫_ℂ := rfl
        _ = ⟪projection π S ξ, ξ⟫_ℂ := by
          rw [hξ, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
        _ = _ := inner_projection_self S ξ
    have e3 : ‖projection π (dualAct φ p '' S) η‖ ^ 2 = ‖projection π S ξ‖ ^ 2 := by
      rw [norm_sq_projection _ hmeas, norm_sq_projection S hS, ← hη,
        vectorMeasure_rho hcov p ξ, Measure.map_apply (measurable_dualAct φ p) hmeas,
        (show Function.Injective (dualAct φ p) from (dualActEquiv φ p).injective).preimage_image S]
    change ⟪(R * projection π S * star R - projection π (dualAct φ p '' S)) η, η⟫_ℂ = 0
    rw [sub_apply, inner_sub_left, e1, inner_projection_self, e3, sub_self]
  calc R * projection π S = R * projection π S * (star R * R) := by rw [hRR, mul_one]
    _ = (R * projection π S * star R) * R := by simp only [mul_assoc]
    _ = _ := by rw [key]

end Covariance

end UnitaryRep

end QuantumMechanics

end ProbabilisticTheory

end
