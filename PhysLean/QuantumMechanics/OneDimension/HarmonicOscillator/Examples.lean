/-
Copyright (c) 2025 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
/-!
# Examples: 1d Quantum Harmonic Oscillator

This module gives simple examples of how to use the
`QuantumMechanics.OneDimension.HarmonicOscillator` API.

It is intended for experimentation and pedagogical use, and should
not be imported into other modules.

To run it from the command line:
```
lake env lean PhysLean/QuantumMechanics/OneDimension/HarmonicOscillator/Examples.lean
```
-/

namespace QuantumMechanics
namespace OneDimension
namespace HarmonicOscillator
namespace Examples

open QuantumMechanics OneDimension HarmonicOscillator Constants

/-- A concrete harmonic oscillator with `m = 1`, `ω = 1`. -/
noncomputable def Q : HarmonicOscillator where
  m := 1
  ω := 1
  hω := by norm_num
  hm := by norm_num

-- Schrödinger operator acting on the ground state
-- Commenting out the checks to reduce noise in the output
-- #check Q.schrodingerOperator (Q.eigenfunction 0)

-- The time-independent Schrödinger equation for n = 0
-- Commenting out the checks to reduce noise in the output
-- #check Q.schrodingerOperator_eigenfunction 0

/-- The explicit pointwise form of the time-independent Schrödinger equation
for the ground state `n = 0`. -/
example :
    ∀ x, Q.schrodingerOperator (Q.eigenfunction 0) x =
      (Q.eigenValue 0) * Q.eigenfunction 0 x :=
  Q.schrodingerOperator_eigenfunction 0

/-- The explicit formula for the ground-state energy for `Q`. -/
example :
    Q.eigenValue 0 = ((0 : ℝ) + 1 / 2) * ℏ * Q.ω := by
  simp [QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue]

/-- Explicit formula for the ground-state wavefunction for `Q`. -/
example :
    Q.eigenfunction 0 =
        fun x : ℝ =>
          (1 / √(√Real.pi * Q.ξ)) * Complex.exp (- x^2 / (2 * Q.ξ^2)) := by
    -- This is exactly eigenfunction_zero specialized to our Q.
    simpa using
      (QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_zero (Q := Q))

end Examples
end HarmonicOscillator
end OneDimension
end QuantumMechanics
