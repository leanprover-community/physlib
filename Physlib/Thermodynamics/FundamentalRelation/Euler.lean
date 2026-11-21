/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Thermodynamics.FundamentalRelation.Intensive

/-!
# Euler relation for fundamental thermodynamic relations

## i. Overview

For a simple system in the entropy representation, extensivity says that the fundamental
relation is homogeneous of degree one:

`S(lU, lV, lN) = l * S(U, V, N)` for `l > 0`.

Differentiating this scaling identity at `l = 1` gives Euler's homogeneous-function identity

`U * ∂S/∂U + V * ∂S/∂V + N * ∂S/∂N = S`.

This file proves that identity for any `FundamentalRelation`. The proof differentiates the
same scaling curve in two ways: first by the chain rule and the total-derivative formula
from `Intensive.lean`, and second by the homogeneity field of `FundamentalRelation`.

The final theorem rewrites the homogeneous-function identity using the intensive parameters
defined from the entropy partials:

`U = T * S - P * V + μ * N`.

## ii. Key results

- `FundamentalRelation.euler` - Euler's homogeneous-function identity for entropy.
- `FundamentalRelation.euler_relation` - the thermodynamic Euler relation
  `U = T * S - P * V + μ * N`.

## iii. Table of contents

- A. Differentiating the scaling identity
- B. Euler identities

## iv. References

- H.B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed., Wiley
  (1985).
-/

@[expose] public section

namespace Thermodynamics

open scoped ContDiff

noncomputable section

/-! ## A. Differentiating the scaling identity

The proof of Euler's identity compares two derivatives of the same one-variable curve
`l ↦ S(lU, lV, lN)` at `l = 1`. The left calculation uses the chain rule together with the
total derivative formula from `Intensive.lean`; the right calculation uses the degree-one
homogeneity assumption directly. -/

/-- The derivative of the scaling curve computed by the chain rule.

For `l ↦ S(lU, lV, lN)`, differentiating through the coordinate map
`l ↦ (lU, lV, lN)` gives

`U * ∂S/∂U + V * ∂S/∂V + N * ∂S/∂N`

at `l = 1`. -/
private lemma hasDerivAt_scaling_left (Φ : FundamentalRelation) (e : ExtensiveState) :
    HasDerivAt (fun l => Φ.S (l * e.U) (l * e.V) (l * e.N))
      (e.U * Φ.dS_dU e + e.V * Φ.dS_dV e + e.N * Φ.dS_dN e) 1 := by
  set D := fderiv ℝ (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2)
    (e.U, e.V, e.N) with hD
  have hdiag : HasDerivAt (fun l : ℝ => (l * e.U, l * e.V, l * e.N))
      (e.U, e.V, e.N) 1 :=
    (hasDerivAt_mul_const e.U).prodMk
      ((hasDerivAt_mul_const e.V).prodMk (hasDerivAt_mul_const e.N))
  have hfderiv1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) D
      ((fun l : ℝ => (l * e.U, l * e.V, l * e.N)) 1) := by
    simpa [one_mul] using Φ.hasFDerivAt_joint e
  have hLHS : HasDerivAt (fun l => Φ.S (l * e.U) (l * e.V) (l * e.N))
      (D (e.U, e.V, e.N)) 1 := by
    change HasDerivAt ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
      fun l : ℝ => (l * e.U, (l * e.V, l * e.N))) (D (e.U, e.V, e.N)) 1
    exact hfderiv1.comp_hasDerivAt (1 : ℝ) hdiag
  rwa [Φ.fderiv_S_apply e e.U e.V e.N] at hLHS

/-- The derivative of the scaling curve computed from extensivity.

Near `l = 1`, positivity of `l` lets the homogeneity field rewrite
`S(lU, lV, lN)` as `l * S(U, V, N)`, whose derivative at `1` is `S(U,V,N)`. -/
private lemma hasDerivAt_scaling_right (Φ : FundamentalRelation) (e : ExtensiveState) :
    HasDerivAt (fun l => Φ.S (l * e.U) (l * e.V) (l * e.N)) (Φ.S e.U e.V e.N) 1 := by
  have heq : (fun l => Φ.S (l * e.U) (l * e.V) (l * e.N))
      =ᶠ[nhds (1 : ℝ)] (fun l => l * Φ.S e.U e.V e.N) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)] with l hl
    exact Φ.homogeneous hl e.U e.V e.N e.hU e.hV e.hN
  exact (hasDerivAt_mul_const (Φ.S e.U e.V e.N)).congr_of_eventuallyEq heq

/-! ## B. Euler identities

Equating the two derivatives of the scaling curve gives Euler's homogeneous-function identity
for entropy. Substituting the definitions of `temperature`, `pressure`, and
`chemicalPotential` then gives the usual thermodynamic Euler relation. -/

/-- Euler's homogeneous-function identity for entropy:

`U * ∂S/∂U + V * ∂S/∂V + N * ∂S/∂N = S`.

It follows by differentiating the degree-one scaling law for `S` at scale `l = 1`. -/
lemma FundamentalRelation.euler (Φ : FundamentalRelation) (e : ExtensiveState) :
    e.U * Φ.dS_dU e + e.V * Φ.dS_dV e + e.N * Φ.dS_dN e = Φ.S e.U e.V e.N :=
  (hasDerivAt_scaling_left Φ e).unique (hasDerivAt_scaling_right Φ e)

/-- The thermodynamic Euler relation in entropy-representation variables:

`U = T * S - P * V + μ * N`.

This is `FundamentalRelation.euler` rewritten using `T = (∂S/∂U)⁻¹`,
`P = T * ∂S/∂V`, and `μ = -T * ∂S/∂N`. -/
lemma FundamentalRelation.euler_relation (Φ : FundamentalRelation) (e : ExtensiveState) :
    e.U = Φ.temperature e * Φ.S e.U e.V e.N
          - Φ.pressure e * e.V + Φ.chemicalPotential e * e.N := by
  have hne : Φ.dS_dU e ≠ 0 :=
    ne_of_gt (by
      simpa [FundamentalRelation.dS_dU] using Φ.dS_dU_pos e.U e.V e.N e.hU e.hV e.hN)
  have he := Φ.euler e
  simp only [FundamentalRelation.temperature, FundamentalRelation.pressure,
    FundamentalRelation.chemicalPotential]
  field_simp
  linear_combination he

end

end Thermodynamics
