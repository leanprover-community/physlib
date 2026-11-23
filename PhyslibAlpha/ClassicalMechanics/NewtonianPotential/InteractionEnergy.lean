/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.InvNormKernel

/-!
# The gravitational interaction energy of two mass densities

## i. Overview

For two mass densities `ρ₁`, `ρ₂` on `Space 3` given by Schwartz maps, the Newtonian
gravitational interaction energy is
`W(ρ₁, ρ₂) = ∫ ρ₁(x) Φ₂(x) dx = -G ∫∫ ρ₁(x) ρ₂(y) / ‖x - y‖ dx dy`,
where `Φ₂` is the Newtonian potential of `ρ₂`. The gravitational self-energy of a single density
`ρ` is `W(ρ, ρ) / 2`.

This module defines `W` and shows that it is a symmetric bilinear form which is invariant under
a common translation of both densities. As a consequence the interaction energy of a difference
of two densities with itself expands as `W(ρ₁, ρ₁) + W(ρ₂, ρ₂) - 2 W(ρ₁, ρ₂)`. For `G ≥ 0` the
interaction energy of a density with itself is nonpositive.

## ii. Key results

- `interactionEnergy` : the gravitational interaction energy of two Schwartz mass densities.
- `interactionEnergy_comm` : the interaction energy is symmetric.
- `interactionEnergy_add_left`, `interactionEnergy_smul_left` and their right-hand versions :
  the interaction energy is bilinear.
- `interactionEnergy_sum_left` : the interaction energy of a finite sum of densities.
- `interactionEnergy_sub_sub` : the interaction energy of a difference with itself.
- `interactionEnergy_translateSchwartz` : invariance under a common translation.
- `interactionEnergy_self_nonpos` : the interaction energy of a density with itself is
  nonpositive.

## iii. Table of contents

- A. The interaction energy
- B. Symmetry
- C. Bilinearity
- D. The interaction energy of a difference
- E. Translation invariance
- F. Sign of the self-interaction energy

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution
open scoped SchwartzMap

/-!

## A. The interaction energy

-/

/-- The Newtonian gravitational interaction energy `W(ρ₁, ρ₂) = ∫ ρ₁(x) Φ₂(x) dx` of two mass
densities on `Space 3`, where `Φ₂` is the Newtonian potential of `ρ₂` and `G` is the
gravitational constant. -/
def interactionEnergy (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) : ℝ :=
  ∫ x, ρ₁ x * newtonPotential G ρ₂ x

/-- A Schwartz density times a Newtonian potential is integrable. -/
lemma integrable_mul_newtonPotential (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    Integrable (fun x : Space 3 => ρ₁ x * newtonPotential G ρ₂ x) :=
  (isDistBounded_newtonPotential G ρ₂).integrable_space_mul ρ₁

/-- The interaction energy as a double integral over the kernel `1 / ‖x - y‖`. -/
lemma interactionEnergy_eq_integral_integral (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ ρ₂ = -G * ∫ x, ∫ y, ρ₁ x * (ρ₂ y * ‖x - y‖⁻¹) := by
  rw [interactionEnergy, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [newtonPotential]
  rw [integral_const_mul]
  ring

/-!

## B. Symmetry

-/

/-- The gravitational interaction energy is symmetric in the two densities. -/
lemma interactionEnergy_comm (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ ρ₂ = interactionEnergy G ρ₂ ρ₁ := by
  rw [interactionEnergy_eq_integral_integral, interactionEnergy_eq_integral_integral,
    integral_integral_swap (integrable_prod_mul_mul_inv_norm_sub ρ₁ ρ₂)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [norm_sub_rev]
  ring

/-!

## C. Bilinearity

-/

/-- The interaction energy is additive in the first density. -/
lemma interactionEnergy_add_left (G : ℝ) (ρ₁ ρ₂ ρ₃ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G (ρ₁ + ρ₂) ρ₃ = interactionEnergy G ρ₁ ρ₃ + interactionEnergy G ρ₂ ρ₃ := by
  simp only [interactionEnergy, _root_.add_apply, add_mul]
  exact integral_add (integrable_mul_newtonPotential G ρ₁ ρ₃)
    (integrable_mul_newtonPotential G ρ₂ ρ₃)

/-- The interaction energy is homogeneous in the first density. -/
lemma interactionEnergy_smul_left (G c : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G (c • ρ₁) ρ₂ = c * interactionEnergy G ρ₁ ρ₂ := by
  simp only [interactionEnergy, _root_.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

/-- The interaction energy of a difference in the first density. -/
lemma interactionEnergy_sub_left (G : ℝ) (ρ₁ ρ₂ ρ₃ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G (ρ₁ - ρ₂) ρ₃ = interactionEnergy G ρ₁ ρ₃ - interactionEnergy G ρ₂ ρ₃ := by
  simp only [interactionEnergy, _root_.sub_apply, sub_mul]
  exact integral_sub (integrable_mul_newtonPotential G ρ₁ ρ₃)
    (integrable_mul_newtonPotential G ρ₂ ρ₃)

/-- The interaction energy vanishes if the first density is zero. -/
lemma interactionEnergy_zero_left (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G 0 ρ = 0 := by
  simp [interactionEnergy]

/-- The interaction energy of a finite sum of densities. -/
lemma interactionEnergy_sum_left {ι : Type*} (G : ℝ) (s : Finset ι) (f : ι → 𝓢(Space 3, ℝ))
    (ρ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G (∑ i ∈ s, f i) ρ = ∑ i ∈ s, interactionEnergy G (f i) ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [interactionEnergy_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, interactionEnergy_add_left, ih]

/-- The interaction energy is additive in the second density. -/
lemma interactionEnergy_add_right (G : ℝ) (ρ₁ ρ₂ ρ₃ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ (ρ₂ + ρ₃) = interactionEnergy G ρ₁ ρ₂ + interactionEnergy G ρ₁ ρ₃ := by
  rw [interactionEnergy_comm, interactionEnergy_add_left, interactionEnergy_comm G ρ₂,
    interactionEnergy_comm G ρ₃]

/-- The interaction energy is homogeneous in the second density. -/
lemma interactionEnergy_smul_right (G c : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ (c • ρ₂) = c * interactionEnergy G ρ₁ ρ₂ := by
  rw [interactionEnergy_comm, interactionEnergy_smul_left, interactionEnergy_comm]

/-- The interaction energy of a difference in the second density. -/
lemma interactionEnergy_sub_right (G : ℝ) (ρ₁ ρ₂ ρ₃ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ (ρ₂ - ρ₃) = interactionEnergy G ρ₁ ρ₂ - interactionEnergy G ρ₁ ρ₃ := by
  rw [interactionEnergy_comm, interactionEnergy_sub_left, interactionEnergy_comm G ρ₂,
    interactionEnergy_comm G ρ₃]

/-!

## D. The interaction energy of a difference

-/

/-- The interaction energy of the difference of two densities with itself:
`W(ρ₁ - ρ₂, ρ₁ - ρ₂) = W(ρ₁, ρ₁) + W(ρ₂, ρ₂) - 2 W(ρ₁, ρ₂)`. -/
lemma interactionEnergy_sub_sub (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G (ρ₁ - ρ₂) (ρ₁ - ρ₂) =
      interactionEnergy G ρ₁ ρ₁ + interactionEnergy G ρ₂ ρ₂ - 2 * interactionEnergy G ρ₁ ρ₂ := by
  rw [interactionEnergy_sub_left, interactionEnergy_sub_right, interactionEnergy_sub_right,
    interactionEnergy_comm G ρ₂ ρ₁]
  ring

/-!

## E. Translation invariance

-/

/-- The interaction energy is invariant under a common translation of both densities. -/
lemma interactionEnergy_translateSchwartz (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ))
    (a : EuclideanSpace ℝ (Fin 3)) :
    interactionEnergy G (translateSchwartz a ρ₁) (translateSchwartz a ρ₂) =
      interactionEnergy G ρ₁ ρ₂ := by
  simp only [interactionEnergy, newtonPotential_translateSchwartz, translateSchwartz_apply]
  exact integral_sub_right_eq_self (fun x : Space 3 => ρ₁ x * newtonPotential G ρ₂ x)
    (basis.repr.symm a)

/-!

## F. Sign of the self-interaction energy

-/

/-- The interaction energy of a mass density with itself is nonpositive for `G ≥ 0`. Hence the
gravitational self-energy `W(ρ, ρ) / 2` is nonpositive. -/
lemma interactionEnergy_self_nonpos {G : ℝ} (hG : 0 ≤ G) (ρ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ ρ ≤ 0 := by
  rw [interactionEnergy_eq_integral_integral]
  have hint := integrable_prod_mul_mul_inv_norm_sub ρ ρ
  have h := integral_prod (fun p : Space 3 × Space 3 => ρ p.1 * (ρ p.2 * ‖p.1 - p.2‖⁻¹)) hint
  have hnn := integral_mul_mul_inv_norm_sub_nonneg ρ
  have e : ∫ x, ∫ y, ρ x * (ρ y * ‖x - y‖⁻¹) =
      ∫ p : Space 3 × Space 3, ρ p.1 * ρ p.2 * ‖p.1 - p.2‖⁻¹ := by
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only
    ring
  rw [e]
  nlinarith

/-- The interaction energy of a difference of two densities with itself is nonpositive:
`0 ≤ 2 W(ρ₁, ρ₂) - W(ρ₁, ρ₁) - W(ρ₂, ρ₂)` for `G ≥ 0`. -/
lemma interactionEnergy_add_self_le_two_mul {G : ℝ} (hG : 0 ≤ G) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ ρ₁ + interactionEnergy G ρ₂ ρ₂ ≤ 2 * interactionEnergy G ρ₁ ρ₂ := by
  have h := interactionEnergy_self_nonpos hG (ρ₁ - ρ₂)
  rw [interactionEnergy_sub_sub] at h
  linarith

end PhyslibAlpha.NewtonianPotential
