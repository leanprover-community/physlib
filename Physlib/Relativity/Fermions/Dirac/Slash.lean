/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Fermions.Dirac.GammaMatrices
/-!
# The Dirac slash operator

This file defines the Dirac slash `k̸ = k_μ γ^μ` of a Lorentz vector, in the Dirac
representation obtained from the gamma endomorphisms `Fermion.Dirac.gamma` via the change of
coordinates `Fermion.Dirac.endEquivMatrix`. The slash is the Dirac representation of Clifford
multiplication `Fermion.Dirac.gammaMatrix`, and so contracts the lowered coordinates of a
Lorentz vector with the gamma matrices.

## Main Definitions

- `Slash.slash`: The Dirac slash `k̸ = k_μ γ^μ` of a Lorentz vector
- `Slash.slashProd`: The product of the Dirac slashes of a list of Lorentz vectors

-/

@[expose] public section

namespace Fermion.Dirac

noncomputable section

namespace Slash

/-- The Dirac slash `k̸ = k_μ γ^μ` of a Lorentz vector, in the Dirac representation.
It is the Dirac representation of Clifford multiplication `Fermion.Dirac.gammaMatrix`,
and so contracts the lowered coordinates of `k` with the gamma matrices. -/
def slash (k : Lorentz.Vector) : Matrix (Fin 4) (Fin 4) ℂ :=
  endEquivMatrix (gammaMatrix k)

/-- The notation for the Dirac slash operator, `k̸`. -/
notation k "̸" => slash k

/-- The Dirac slash as an `ℝ`-linear map, which it inherits from Clifford multiplication. -/
def slashLinear : Lorentz.Vector →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ :=
  (endEquivMatrix.toLinearEquiv.restrictScalars ℝ).toLinearMap ∘ₗ gammaMatrix

@[simp]
lemma slashLinear_apply (k : Lorentz.Vector) : slashLinear k = slash k := rfl

/-- The Dirac slash contracts the lowered vector coordinates with the gamma matrices. -/
lemma slash_eq_sum (k : Lorentz.Vector) :
    slash k = ∑ μ, ((minkowskiMatrix μ μ * k μ : ℝ) : ℂ) • endEquivMatrix (gamma μ) := by
  rw [slash, gammaMatrix_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun μ _ => by rw [← Complex.coe_smul, map_smul]

@[simp]
lemma slash_zero : slash (0 : Lorentz.Vector) = 0 := by
  rw [← slashLinear_apply, map_zero]

@[simp]
lemma slash_add (k l : Lorentz.Vector) : slash (k + l) = slash k + slash l := by
  rw [← slashLinear_apply, map_add, slashLinear_apply, slashLinear_apply]

@[simp]
lemma slash_smul (c : ℝ) (k : Lorentz.Vector) : slash (c • k) = c • slash k := by
  rw [← slashLinear_apply, map_smul, slashLinear_apply]

/-- Left multiplication by a slash matrix as a linear endomorphism. -/
def slashMulLeft (k : Lorentz.Vector) :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  LinearMap.mulLeft ℂ (slash k)

/-- Product of a list of slash factors, in left-to-right order. -/
def slashProd (ks : List Lorentz.Vector) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((ks.map slashMulLeft).prod) 1

@[simp]
lemma slashProd_nil : slashProd [] = 1 := by
  simp [slashProd]

@[simp]
lemma slashProd_cons (k : Lorentz.Vector) (ks : List Lorentz.Vector) :
    slashProd (k :: ks) = slash k * slashProd ks := by
  simp [slashProd, slashMulLeft]

end Slash

end

end Fermion.Dirac
