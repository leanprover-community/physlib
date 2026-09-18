/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.SpaceDQuantumSystem
public import Physlib.QuantumMechanics.Operators.Position
/-!

# Hydrogen atom

This module introduces the `d`-dimensional hydrogen atom with `1/r` potential.

In addition to the dimension `d`, the quantum mechanical system is characterized by
a mass `m > 0` and constant `k` appearing in the potential `V = -k/r`.
The standard hydrogen atom has `d=3`, `m = mₑmₚ/(mₑ + mₚ) ≈ mₑ` and `k = e²/4πε₀`.

The potential `V = -k/r` is singular at the origin. To address this we define a regularized
Hamiltonian in which the potential is replaced by `-k·r(ε)⁻¹`, where `r(ε)² = ‖x‖² + ε²`.
This goes by several names including "soft-core" and "truncated" Coulomb potential.

## References

* https://doi.org/10.1103/PhysRevA.80.032507. [ref: doi_physreva_80_032507]
* https://doi.org/10.1063/1.3290740. [ref: doi_1063_1_3290740]

-/

TODO "Prove that the Hydrogen Hamiltonian is _not_ essentially self-adjoint for `d < 3`."

TODO "Prove that the Hydrogen Hamiltonian is essentially self-adjoint for `d ≥ 3`."

TODO "Prove that (the closure of) the Hydrogen Hamiltonian has eigenvalues (point spectrum)
  {-½mk²ℏ⁻² / (n + ½(d - 1))² | n ∈ ℕ}. These correspond to the bound states."

TODO "Prove that (the closure of) the Hydrogen Hamiltonian has continuous spectrum [0,∞).
  These correspond to scattering states."

TODO "Analyze the Zeeman effect using first-order degenerate perturbation theory."

TODO "Analyze the Stark effect using first-order degenerate perturbation theory."

@[expose] public section

namespace QuantumMechanics
open MeasureTheory
open SchwartzMap

/-- A hydrogen atom is characterized by the number of spatial dimensions `d`,
  the mass `m` and the coefficient `k` for the `1/r` potential. -/
structure HydrogenAtom extends SpaceDQuantumSystem where
  /-- Coefficient in the Coulomb potential (positive for attractive) -/
  k : ℝ
  coulomb_potential : potential = fun x ↦ -k * ‖x‖⁻¹

namespace HydrogenAtom
noncomputable section

variable (H : HydrogenAtom)

/-!
## A. Basic
-/

@[simp]
lemma potential_eq : H.potential = fun x ↦ -H.k * ‖x‖⁻¹ := H.coulomb_potential

@[fun_prop]
lemma potential_AESM : AEStronglyMeasurable H.potential := by
  rw [potential_eq]
  exact AEMeasurable.aestronglyMeasurable (by fun_prop)

@[fun_prop]
lemma potential_AEM : AEMeasurable H.potential := H.potential_AESM.aemeasurable

/-!
## B. Regularization
-/

/-- The hydrogen atom Hamiltonian regularized by `ε ≠ 0` is defined to be
  `𝐇(ε) ≔ (2m)⁻¹𝐩² - k·𝐫(ε)⁻¹`. -/
def hamiltonianRegCLM (ε : ℝˣ) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  (2 * H.m)⁻¹ • (𝐩 ⬝ᵥ 𝐩) - H.k • 𝐫₀ ε (-1)

lemma hamiltonianRegCLM_eq (ε : ℝˣ) :
    H.hamiltonianRegCLM ε = (2 * H.m)⁻¹ • (𝐩 ⬝ᵥ 𝐩) - H.k • 𝐫₀ ε (-1) := rfl

end
end HydrogenAtom
end QuantumMechanics
