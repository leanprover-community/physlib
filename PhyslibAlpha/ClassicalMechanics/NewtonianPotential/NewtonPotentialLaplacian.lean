/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.NewtonPotentialDeriv

/-!
# The Laplacian of the Newtonian potential

## i. Overview

For a Schwartz mass density `ρ` on `Space 3` the Newtonian potential `Φ` satisfies Poisson's
equation `ΔΦ = 4πGρ` pointwise.

The derivative of `Φ` in a direction `v` is the potential of the derivative of `ρ` in the
direction `v`. Applying this twice gives `ΔΦ_ρ = Φ_{Δρ}`, and `Φ_{Δρ} = 4πGρ` follows from the
Laplacian of the point-source potential.

## ii. Key results

- `newtonPotential_laplacian` : the potential of `Δρ` is `4πGρ`.
- `laplacian_newtonPotential` : Poisson's equation, pointwise.

## iii. Table of contents

- A. The Newtonian potential of a Laplacian
- B. Poisson's equation

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution
open scoped SchwartzMap LineDeriv

/-!

## A. The Newtonian potential of a Laplacian

-/

/-- The Newtonian potential of the Laplacian of a density is `4πG` times the density. -/
lemma newtonPotential_laplacian (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    newtonPotential G (Laplacian.laplacian ρ) x = 4 * Real.pi * G * ρ x := by
  have h := congrArg (fun T => T ρ) (distLaplacian_inv_norm_sub x)
  simp only [distLaplacian_apply, distOfFunction_apply, smul_eq_mul] at h
  rw [newtonPotential_apply]
  simp_rw [norm_sub_rev x]
  have hδ : ((-(4 * Real.pi)) • diracDelta ℝ x) ρ = -(4 * Real.pi) * ρ x := by simp
  rw [h, hδ]
  ring

/-!

## B. Poisson's equation

-/

/-- **Poisson's equation** for the Newtonian potential, pointwise: `ΔΦ = 4πGρ`. -/
theorem laplacian_newtonPotential (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) :
    Space.laplacian (newtonPotential G ρ) = fun x => 4 * Real.pi * G * ρ x := by
  have hd : ∀ (i : Fin 3) (σ : 𝓢(Space 3, ℝ)),
      Space.deriv i (newtonPotential G σ) = newtonPotential G (∂_{basis i} σ) := by
    intro i σ
    funext x
    rw [Space.deriv_eq_fderiv_basis, fderiv_newtonPotential_apply]
  rw [Space.laplacian_eq_sum_snd_deriv]
  funext x
  simp_rw [hd]
  rw [← Finset.sum_apply, ← map_sum, ← SchwartzMap.laplacian_eq_sum basis ρ,
    newtonPotential_laplacian]

end PhyslibAlpha.NewtonianPotential
