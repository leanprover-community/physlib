/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Physlib.Thermodynamics.FundamentalRelation.ExtensiveState

/-!
# The fundamental relation of a simple thermodynamic system

## i. Overview

In the entropy representation, all thermodynamic information about a simple system is
contained in its **fundamental relation** `S = S(U, V, N)`, the entropy as a function of the
extensive parameters internal energy `U`, volume `V`, and particle number `N`. The
`FundamentalRelation` structure bundles that surface with three assumptions: smoothness on
the positive orthant (`smooth`), a positive energy derivative (`dS_dU_pos`, equivalently
`T > 0`), and degree-one homogeneity (`homogeneous`). The entropy `S` is kept total
(`ℝ → ℝ → ℝ → ℝ`), with positivity carried by the field hypotheses and by `ExtensiveState`,
and regularity is asserted only on the positive orthant (`posOrthant`).
Strict monotonicity in `U` is derived via `dS_dU_pos` which is the pointwise primitive
`∂S/∂U > 0` from which `strictMonoOn_U` follows.

## ii. Key results

- `FundamentalRelation` - the smooth entropy surface `S(U, V, N)` with its three fields.
- `FundamentalRelation.strictMonoOn_U` - entropy is strictly increasing in `U` (derived from
  `dS_dU_pos`).

## iii. Table of contents

- A. The fundamental relation
- B. Derived monotonicity in energy

## iv. References

- H.B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed., Wiley
  (1985). -/

@[expose] public section

namespace Thermodynamics

open scoped ContDiff

/-! ## A. The fundamental relation

The structure bundles the entropy surface `S` with the three properties of Postulate III:
continuity and differentiability (`smooth`), monotonicity in the energy (`dS_dU_pos`, i.e.
`∂S/∂U = 1/T > 0`), and degree-one homogeneity (`homogeneous`). The `smooth` field is taken
as C^∞, stronger than the continuity and differentiability the postulate states. -/

/-- A **fundamental relation** in the entropy representation: a total entropy function
`S(U, V, N)` that is C^∞ on the positive orthant, has positive energy derivative
(`dS_dU_pos`), and is homogeneous of degree one (`homogeneous`). -/
structure FundamentalRelation where
  /-- The entropy as a total function of `(U, V, N)`. -/
  S : ℝ → ℝ → ℝ → ℝ
  /-- Regularity: `S` is C^∞ on the positive orthant. -/
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × ℝ => S p.1 p.2.1 p.2.2) posOrthant
  /-- Postulate III, `T > 0`: for positive states, `∂S/∂U > 0`, i.e.
  `1 / T > 0` pointwise. This yields positive temperature without invoking concavity. -/
  dS_dU_pos : ∀ U V N, 0 < U → 0 < V → 0 < N → 0 < deriv (fun u => S u V N) U
  /-- Extensivity: `S` is homogeneous of degree one on the positive orthant,
  `S(lU, lV, lN) = l · S(U, V, N)` for `l > 0` (extensivity of the entropy). -/
  homogeneous : ∀ ⦃l : ℝ⦄, 0 < l → ∀ U V N, 0 < U → 0 < V → 0 < N →
    S (l * U) (l * V) (l * N) = l * S U V N

/-! ## B. Derived monotonicity in energy

Strict monotonicity of entropy in `U` is derived from the pointwise `dS_dU_pos` via
`strictMonoOn_of_deriv_pos`, and `T > 0` is a consequence. -/

/-- Derived: for fixed positive `V, N`, entropy is strictly increasing in the energy on
`Ioi 0`. Obtained from `dS_dU_pos` via `strictMonoOn_of_deriv_pos`. -/
lemma FundamentalRelation.strictMonoOn_U (Φ : FundamentalRelation) (V N : ℝ)
    (hV : 0 < V) (hN : 0 < N) :
    StrictMonoOn (fun U => Φ.S U V N) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · change ContinuousOn ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
      fun U : ℝ => (U, (V, N))) (Set.Ioi 0)
    exact Φ.smooth.continuousOn.comp
      (by
        show ContinuousOn (fun U : ℝ => (U, (V, N))) (Set.Ioi 0)
        fun_prop)
      (by
        intro U hU
        exact ⟨hU, hV, hN⟩)
  · rw [interior_Ioi]
    intro U hU
    exact Φ.dS_dU_pos U V N hU hV hN

end Thermodynamics
