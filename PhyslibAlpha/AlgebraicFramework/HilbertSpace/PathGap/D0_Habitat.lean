/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# D0 — Hábitat: el espacio de Hilbert finito `H_d`

Todo el argumento vive en un único espacio de Hilbert complejo de dimensión
finita, `H_d = ℂ^d` con su producto interno estándar. No se sale nunca de
este espacio: en particular, `d = ∞` no es una dimensión realizada, sólo un
límite de la familia `{H_d}_{d∈ℕ}` (ver `D8_Szego.lean`).
-/

@[expose] public section

namespace TransportePosicion

/-- El espacio de Hilbert finito de dimensión `d`: `ℂ^d` con su estructura
euclidiana estándar. -/
abbrev Hd (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Identidad definicional: `H_d` es, literalmente, `EuclideanSpace ℂ (Fin d)`. -/
theorem Hd_eq_euclidean (d : ℕ) :
    Hd d = EuclideanSpace ℂ (Fin d) := rfl

end TransportePosicion
