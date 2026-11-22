/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.InteractionEnergy

/-!
# The gravitational self-interaction energy is negative definite

## i. Overview

For `G > 0` the Newtonian gravitational interaction energy `W(ρ, ρ)` of a Schwartz mass density
with itself vanishes only for `ρ = 0`, and is strictly negative otherwise.

The proof combines three facts. The form `W` is negative semi-definite, so `W(ρ, ρ) = 0` forces
`W(η, ρ) = 0` for every `η`. By Poisson's equation `W(Δψ, ρ) = 4πG ∫ ψ ρ`. Taking `ψ = ρ` gives
`∫ ρ² = 0`, hence `ρ = 0`.

## ii. Key results

- `interactionEnergy_laplacian_left` : `W(Δψ, ρ) = 4πG ∫ ψ ρ`.
- `interactionEnergy_self_eq_zero_iff` : `W(ρ, ρ) = 0` if and only if `ρ = 0`.
- `interactionEnergy_self_neg` : `W(ρ, ρ) < 0` for `ρ ≠ 0`.

## iii. Table of contents

- A. The interaction energy with a Laplacian
- B. The null space of the interaction energy
- C. Definiteness

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution
open scoped SchwartzMap

/-!

## A. The interaction energy with a Laplacian

-/

/-- Poisson's equation in terms of the interaction energy: `W(Δψ, ρ) = 4πG ∫ ψ ρ`. -/
lemma interactionEnergy_laplacian_left (G : ℝ) (ψ ρ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G (Laplacian.laplacian ψ) ρ = 4 * Real.pi * G * ∫ x, ψ x * ρ x := by
  rw [← distLaplacian_newtonPotential_apply G ρ ψ, distLaplacian_apply, distOfFunction_apply]
  rfl

/-!

## B. The null space of the interaction energy

-/

/-- If the interaction energy of `ρ` with itself vanishes, then the interaction energy of `ρ`
with every density vanishes. This is the Cauchy-Schwarz inequality for a semi-definite form. -/
lemma interactionEnergy_eq_zero_of_self_eq_zero {G : ℝ} (hG : 0 ≤ G) {ρ : 𝓢(Space 3, ℝ)}
    (h : interactionEnergy G ρ ρ = 0) (η : 𝓢(Space 3, ℝ)) : interactionEnergy G η ρ = 0 := by
  by_contra hne
  have e : ∀ t : ℝ, interactionEnergy G (η + t • ρ) (η + t • ρ) =
      interactionEnergy G η η + 2 * t * interactionEnergy G η ρ := by
    intro t
    rw [interactionEnergy_add_left, interactionEnergy_add_right, interactionEnergy_add_right,
      interactionEnergy_smul_left, interactionEnergy_smul_left, interactionEnergy_smul_right,
      interactionEnergy_smul_right, interactionEnergy_comm G ρ η, h]
    ring
  have hq := interactionEnergy_self_nonpos hG
    (η + (-(interactionEnergy G η η - 1) / (2 * interactionEnergy G η ρ)) • ρ)
  rw [e] at hq
  have h1 : interactionEnergy G η η +
      2 * (-(interactionEnergy G η η - 1) / (2 * interactionEnergy G η ρ)) *
        interactionEnergy G η ρ = 1 := by
    field_simp
    ring
  linarith

/-!

## C. Definiteness

-/

/-- For `G > 0` the interaction energy of a density with itself vanishes only for the zero
density. -/
lemma interactionEnergy_self_eq_zero_iff {G : ℝ} (hG : 0 < G) (ρ : 𝓢(Space 3, ℝ)) :
    interactionEnergy G ρ ρ = 0 ↔ ρ = 0 := by
  constructor
  · intro h
    have h1 := interactionEnergy_eq_zero_of_self_eq_zero hG.le h (Laplacian.laplacian ρ)
    rw [interactionEnergy_laplacian_left] at h1
    have hpi := Real.pi_pos
    have h2 : ∫ x, ρ x * ρ x = 0 :=
      (mul_eq_zero.mp h1).resolve_left (by positivity)
    have hint : Integrable (fun x : Space 3 => ρ x ^ 2) := (ρ.memLp 2 volume).integrable_sq
    have h3 : (fun x : Space 3 => ρ x ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).mp (by simpa [sq] using h2)
    have hc : Continuous (fun x : Space 3 => ρ x ^ 2) := ρ.continuous.pow 2
    have h4 := (hc.ae_eq_iff_eq volume continuous_const).mp h3
    ext x
    have h5 : ρ x ^ 2 = 0 := congrFun h4 x
    simpa using (pow_eq_zero_iff two_ne_zero).mp h5
  · rintro rfl
    simp [interactionEnergy]

/-- For `G > 0` the interaction energy of a nonzero density with itself is strictly negative. -/
lemma interactionEnergy_self_neg {G : ℝ} (hG : 0 < G) {ρ : 𝓢(Space 3, ℝ)} (hρ : ρ ≠ 0) :
    interactionEnergy G ρ ρ < 0 :=
  lt_of_le_of_ne (interactionEnergy_self_nonpos hG.le ρ)
    fun h => hρ ((interactionEnergy_self_eq_zero_iff hG ρ).mp h)

end PhyslibAlpha.NewtonianPotential
