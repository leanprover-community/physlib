/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
/-!

# Z-prime charges for the Standard Model

This file introduces the key data structure for Z′-models over the Standard Model:
the assignment of **integer** charges to the (chiral) SM fermions with `n` families.

We model the SM fermions (without RHN) as `5` species (Q, U, D, L, E) each carrying
`n` family copies. Thus a charge assignment is a function `Fin 5 → Fin n → ℤ`.

This file is intentionally lightweight: it provides the underlying data structure and
basic projections. Further API components (family permutations, potential-term charges,
anomaly cancellation conditions, quotients by scaling/hypercharge) are developed in
subsequent files/PRs.
-/

/-- Integer Z′-charges for the `n`-family Standard Model fermions (without RHN). -/
abbrev SMZPrimeCharges (n : ℕ) : Type := Fin 5 → Fin n → ℤ

namespace SMZPrimeCharges

variable {n : ℕ}

/-- The Q charges as a map `Fin n → ℤ`. -/
abbrev Q (χ : SMZPrimeCharges n) : Fin n → ℤ := χ 0

/-- The U charges as a map `Fin n → ℤ`. -/
abbrev U (χ : SMZPrimeCharges n) : Fin n → ℤ := χ 1

/-- The D charges as a map `Fin n → ℤ`. -/
abbrev D (χ : SMZPrimeCharges n) : Fin n → ℤ := χ 2

/-- The L charges as a map `Fin n → ℤ`. -/
abbrev L (χ : SMZPrimeCharges n) : Fin n → ℤ := χ 3

/-- The E charges as a map `Fin n → ℤ`. -/
abbrev E (χ : SMZPrimeCharges n) : Fin n → ℤ := χ 4

end SMZPrimeCharges
