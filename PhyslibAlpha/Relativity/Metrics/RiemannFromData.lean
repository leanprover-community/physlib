/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.CoordDeriv
public import PhyslibAlpha.Relativity.Tensors.Tensor2

/-!

# Riemann curvature from Christoffel data

The coordinate Riemann curvature tensor evaluated directly from supplied Christoffel symbols `G`
and coordinate derivative table `dG`.

## i. Overview

Given closed-form Levi-Civita connection coefficients `G` and their partial derivatives
`dG μ x ρ ν σ = ∂_μ Γ^ρ_{νσ}`, `Pipeline.riemannFromData G dG x ρ σ μ ν` evaluates
`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`
directly without nested inverse-metric differentiation, and `riemannFromData_congr` records its
local dependence on the derivative components `(μ, ρ, ν, σ)` and `(ν, ρ, μ, σ)`.

## ii. Key results

- `Pipeline.riemannFromData` : data-parameterised Riemann curvature evaluator.
- `Pipeline.riemannFromData_congr` : local congruence with respect to derivative arguments.

## iii. Table of contents

- A. Curvature from Christoffel data

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1-3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 8 & Ch. 13.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 3.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=72). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Pipeline

/-!

## A. Curvature from Christoffel data

Evaluating the Riemann curvature tensor directly from closed-form connection coefficients `Γ` and
their coordinate derivatives `∂Γ` matches `Pipeline.riemann` while isolating algebraic curvature
contractions.

-/

/-- The Riemann tensor evaluated from supplied Christoffel symbols `G` and partial derivatives
`dG`: `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`.
Decoupled from `Pipeline.riemann` so explicit closed-form Christoffel and derivative tables
avoid re-differentiating inverse-metric sums. -/
noncomputable def riemannFromData {n : ℕ}
    (G : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (dG : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  dG μ x ρ ν σ - dG ν x ρ μ σ
    + ∑ l, (G x ρ μ l * G x l ν σ - G x ρ ν l * G x l μ σ)

/-- `riemannFromData` depends on its derivative argument only at `(μ, ρ, ν, σ)` and
`(ν, ρ, μ, σ)`. -/
lemma riemannFromData_congr {n : ℕ} (G : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    {dG dG' : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ}
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n)
    (h1 : dG μ x ρ ν σ = dG' μ x ρ ν σ) (h2 : dG ν x ρ μ σ = dG' ν x ρ μ σ) :
    riemannFromData G dG x ρ σ μ ν = riemannFromData G dG' x ρ σ μ ν := by
  simp only [riemannFromData, h1, h2]

end Pipeline

end GeneralRelativity
