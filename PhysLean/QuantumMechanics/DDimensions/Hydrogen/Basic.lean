/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhysLean.QuantumMechanics.DDimensions.Operators.Momentum
public import PhysLean.QuantumMechanics.DDimensions.Operators.Position
/-!

# Hydrogen atom

This module introduces the `d`-dimensional hydrogen atom with `1/r` potential.

In addition to the dimension `d`, the quantum mechanical system is characterized by
a mass `m > 0` and constant `k` appearing in the potential `V = -k/r`.
The standard hydrogen atom has `d=3`, `m = mₑmₚ/(mₑ + mₚ) ≈ mₑ` and `k = e²/4πε₀`.

The potential `V = -k/r` is singular at the origin. To address this we define a regularized
Hamiltonian in which the potential is replaced by `-k(r(ε)⁻¹ + ½ε²r(ε)⁻³)`, where
`r(ε)² = ‖x‖² + ε²`. The `ε²/r³` term limits to the zero distribution for `ε → 0`
but is convenient to include for two reasons:
- It improves the convergence: `r(ε)⁻¹ + ½ε²r(ε)⁻³ = r⁻¹(1 + O(ε⁴/r⁴))` with no `O(ε²/r²)` term.
- It is what appears in the commutators of the (regularized) LRL vector components.

-/

@[expose] public section

namespace QuantumMechanics
open SchwartzMap

/-- A hydrogen atom is characterized by the number of spatial dimensions `d`,
  the mass `m` and the coefficient `k` for the `1/r` potential. -/
structure HydrogenAtom where
  /-- Number of spatial dimensions -/
  d : ℕ

  /-- Mass (positive) -/
  m : ℝ
  hm : 0 < m

  /-- Coefficient in potential (positive for attractive) -/
  k : ℝ

namespace HydrogenAtom
noncomputable section

variable (H : HydrogenAtom)

@[simp]
lemma m_ne_zero : H.m ≠ 0 := by linarith [H.hm]

/-- The hydrogen atom Hamiltonian regularized by `ε ≠ 0` is defined to be
  `𝐇(ε) ≔ (2m)⁻¹𝐩² - k(𝐫(ε)⁻¹ + ½ε²𝐫(ε)⁻³)`. -/
def hamiltonianReg (ε : ℝˣ) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  (2 * H.m)⁻¹ • 𝐩² - H.k • (𝐫[ε,-1] + (2⁻¹ * ε.1 ^ 2) • 𝐫[ε,-3])

end
end HydrogenAtom
end QuantumMechanics
