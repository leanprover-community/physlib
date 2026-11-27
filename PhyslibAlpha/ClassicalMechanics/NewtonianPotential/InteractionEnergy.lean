/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.NewtonPotential

/-!
# The gravitational interaction energy of two mass densities

## i. Overview

For two mass densities `ρ₁`, `ρ₂` on `Space 3` given by Schwartz maps, the Newtonian
gravitational interaction energy is
`W(ρ₁, ρ₂) = ∫ ρ₁(x) Φ₂(x) dx = -G ∫∫ ρ₁(x) ρ₂(y) / ‖x - y‖ dx dy`,
where `Φ₂` is the Newtonian potential of `ρ₂`. The gravitational self-energy of a single density
`ρ` is `W(ρ, ρ) / 2`.

This module defines `W` as a bilinear form on Schwartz maps and shows that it is symmetric and
invariant under a common translation of both densities. As a consequence the interaction energy
of a difference of two densities with itself expands as `W(ρ₁, ρ₁) + W(ρ₂, ρ₂) - 2 W(ρ₁, ρ₂)`.

## ii. Key results

- `interactionEnergy` : the gravitational interaction energy of two Schwartz mass densities, as a
  bilinear form.
- `interactionEnergy_eq_integral_prod` : the interaction energy as an integral over the kernel
  `1 / ‖x - y‖` on `Space 3 × Space 3`.
- `interactionEnergy_comm` : the interaction energy is symmetric.
- `interactionEnergy_sub_sub` : the interaction energy of a difference with itself.
- `interactionEnergy_translateSchwartz` : invariance under a common translation.

## iii. Table of contents

- A. The interaction energy
- B. Symmetry
- C. The interaction energy of a difference
- D. Translation invariance

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

/-- A Schwartz density times a Newtonian potential is integrable. -/
lemma integrable_mul_newtonPotential (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    Integrable (fun x : Space 3 => ρ₁ x * newtonPotential G ρ₂ x) :=
  (isDistBounded_newtonPotential G ρ₂).integrable_space_mul ρ₁

/-- The Newtonian gravitational interaction energy `W(ρ₁, ρ₂) = ∫ ρ₁(x) Φ₂(x) dx` of two mass
densities on `Space 3`, where `Φ₂` is the Newtonian potential of `ρ₂` and `G` is the
gravitational constant. It is a bilinear form in the two densities. -/
def interactionEnergy (G : ℝ) : LinearMap.BilinForm ℝ 𝓢(Space 3, ℝ) :=
  LinearMap.mk₂ ℝ (fun ρ₁ ρ₂ => ∫ x, ρ₁ x * newtonPotential G ρ₂ x)
    (fun ρ₁ ρ₂ ρ₃ => by
      simp only [_root_.add_apply, add_mul]
      exact integral_add (integrable_mul_newtonPotential G ρ₁ ρ₃)
        (integrable_mul_newtonPotential G ρ₂ ρ₃))
    (fun c ρ₁ ρ₂ => by
      simp only [_root_.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun ρ₁ ρ₂ ρ₃ => by
      simp only [map_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_mul_newtonPotential G ρ₁ ρ₂)
        (integrable_mul_newtonPotential G ρ₁ ρ₃))
    (fun c ρ₁ ρ₂ => by
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul c _)

/-- The interaction energy as an integral of a density against the potential of the other. -/
lemma interactionEnergy_apply (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ ρ₂ = ∫ x, ρ₁ x * newtonPotential G ρ₂ x := rfl

/-- The interaction energy as a double integral over the kernel `1 / ‖x - y‖`. -/
lemma interactionEnergy_eq_integral_integral (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ ρ₂ = -G * ∫ x, ∫ y, ρ₁ x * (ρ₂ y * ‖x - y‖⁻¹) := by
  rw [interactionEnergy_apply, ← integral_const_mul]
  congr 1 with x
  simp only [newtonPotential_apply]
  rw [integral_const_mul]
  ring

/-- The interaction energy as an integral over `Space 3 × Space 3` of the kernel
`1 / ‖x - y‖`. -/
lemma interactionEnergy_eq_integral_prod (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ₁ ρ₂ =
      -G * ∫ p : Space 3 × Space 3, ρ₁ p.1 * ρ₂ p.2 * ‖p.1 - p.2‖⁻¹ := by
  rw [interactionEnergy_eq_integral_integral,
    ← integral_prod _ (integrable_prod_mul_mul_inv_norm_sub ρ₁ ρ₂)]
  congr 1
  congr 1 with p
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
  congr 1 with y
  congr 1 with x
  rw [norm_sub_rev]
  ring

/-- The gravitational interaction energy is a symmetric bilinear form. -/
lemma isSymm_interactionEnergy (G : ℝ) : (interactionEnergy G).IsSymm :=
  ⟨interactionEnergy_comm G⟩

/-!

## C. The interaction energy of a difference

-/

/-- The interaction energy of the difference of two densities with itself:
`W(ρ₁ - ρ₂, ρ₁ - ρ₂) = W(ρ₁, ρ₁) + W(ρ₂, ρ₂) - 2 W(ρ₁, ρ₂)`. -/
lemma interactionEnergy_sub_sub (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G (ρ₁ - ρ₂) (ρ₁ - ρ₂) =
      interactionEnergy G ρ₁ ρ₁ + interactionEnergy G ρ₂ ρ₂ - 2 * interactionEnergy G ρ₁ ρ₂ := by
  simp only [map_sub, LinearMap.sub_apply, interactionEnergy_comm G ρ₂ ρ₁]
  ring

/-!

## D. Translation invariance

-/

/-- The interaction energy is invariant under a common translation of both densities. -/
lemma interactionEnergy_translateSchwartz (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ))
    (a : EuclideanSpace ℝ (Fin 3)) :
    interactionEnergy G (translateSchwartz a ρ₁) (translateSchwartz a ρ₂) =
      interactionEnergy G ρ₁ ρ₂ := by
  simp only [interactionEnergy_apply, newtonPotential_translateSchwartz, translateSchwartz_apply]
  exact integral_sub_right_eq_self (fun x : Space 3 => ρ₁ x * newtonPotential G ρ₂ x)
    (basis.repr.symm a)


end PhyslibAlpha.NewtonianPotential
