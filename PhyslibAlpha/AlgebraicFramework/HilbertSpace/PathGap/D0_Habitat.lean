/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# D0 — Habitat: the finite-dimensional Hilbert space `H_d`

The entire argument lives in a single complex finite-dimensional
Hilbert space, `H_d = ℂ^d` with its standard inner product.
We never leave this space: in particular `d = ∞` is not a
realized dimension, only a limit of the family `{H_d}_{d∈ℕ}`
(see `D8_Szego.lean`).
-/

@[expose] public section

namespace TransportePosicion

/-- The finite-dimensional Hilbert space of dimension `d`:
`ℂ^d` with its standard Euclidean structure. -/
abbrev Hd (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Definitional identity: `H_d` is literally
`EuclideanSpace ℂ (Fin d)`. -/
theorem Hd_eq_euclidean (d : ℕ) :
    Hd d = EuclideanSpace ℂ (Fin d) := rfl

end TransportePosicion
