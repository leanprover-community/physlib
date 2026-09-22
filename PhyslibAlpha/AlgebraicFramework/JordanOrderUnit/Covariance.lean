/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Observable

/-!

# Covariance, and positivity of the covariance matrix

## i. Overview

At the bare order-unit level, a state only sees first moments, `ω(a)`. The Jordan
product is exactly what supplies second moments, `ω(a ∘ b)`, and hence a genuine symmetric
covariance
$$ \operatorname{Cov}_\omega(a, b) = \omega(a \circ b) - \omega(a)\,\omega(b), $$
specializing to the variance already defined in `Observable.lean` on the diagonal,
`Var_ω(a) = Cov_ω(a, a)`. In the canonical C⋆-algebra realization (`CStarAlgebra/Jordan.lean`,
`a ∘ b = ½(ab+ba)`) this is exactly the usual symmetrized quantum covariance
`½⟨AB+BA⟩_ρ - ⟨A⟩_ρ⟨B⟩_ρ`.

The point of building this at the Jordan level rather than waiting for the full associative
product: positivity of Jordan squares (`sq_nonneg`) is *exactly* enough to prove that every
covariance matrix `Γᵢⱼ = Cov_ω(aᵢ, aⱼ)` of a finite family of observables is positive
semidefinite, `Γ ⪰ 0` — apply `moment_two_nonneg` to the single observable
`x = ∑ᵢ cᵢ (aᵢ - ω(aᵢ) 1)` and expand `ω(x ∘ x)` bilinearly. This is the Jordan-algebraic core of
uncertainty theory (variance nonnegativity, Cauchy–Schwarz-type consequences for covariance); the
genuinely non-Jordan remainder, the antisymmetric commutator piece `ω([a,b])/2i` of the *full*
(non-symmetrized) product, is deliberately left to the C⋆/Lie layer
(`StarAlgebra/Lie.lean`) — see the module docstring there for the split
`ω((a-ω(a))(b-ω(b))) = Cov_ω(a,b) + ½ω([a,b])`.

## ii. Key definitions and results

- `LinearMap.covarianceForm`
- `IsJordanOrderUnit.variance_eq_covarianceForm_self`
- `IsJordanOrderUnit.covarianceForm_isPosSemidef`
- `IsJordanOrderUnit.covariance_cauchy_schwarz`
- `IsJordanOrderUnit.covMatrix_posSemidef` : `0 ≤ ∑ i, ∑ j, c i * c j * Cov_ω(aᵢ, aⱼ)`

## iii. Table of contents

- A. Covariance
- B. Positivity of the covariance matrix

-/

@[expose] public section

namespace IsJordanOrderUnit

variable {E : Type*} [NonAssocCommRing E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] [IsCommJordan E]
  [IsOrderUnit E] [IsJordanOrderUnit E]

/-! ## A. Covariance -/

omit [IsOrderedAddMonoid E] [IsCommJordan E] [IsOrderUnit E] [IsJordanOrderUnit E] in
/-- The Jordan variance is the diagonal of the canonical generic covariance form. -/
theorem variance_eq_covarianceForm_self (ω : 𝓢[ℝ, E]) (a : E) :
    variance ω a = LinearMap.covarianceForm ω.toLinearMap a a := rfl

omit [IsOrderedAddMonoid E] [IsCommJordan E] [IsOrderUnit E] [IsJordanOrderUnit E] in
/-- The state's value on the Jordan product of two centered observables is exactly their
covariance: the algebraic identity underlying `covMatrix_posSemidef` below. -/
theorem moment_centered_mul (ω : 𝓢[ℝ, E]) (a b : E) :
    ω (LinearMap.centered ω.toLinearMap a * LinearMap.centered ω.toLinearMap b) =
      LinearMap.covarianceForm ω.toLinearMap a b := by
  exact LinearMap.apply_centered_mul_centered ω.toLinearMap (map_one ω)
    _root_.one_mul _root_.mul_one a b

/-- The covariance form of a state is positive semidefinite. This is the coordinate-free form of
covariance-matrix positivity and uses only positivity of Jordan squares. -/
theorem covarianceForm_isPosSemidef (ω : 𝓢[ℝ, E]) :
    (LinearMap.covarianceForm ω.toLinearMap).IsPosSemidef where
  isSymm := LinearMap.covarianceForm_isSymm ω.toLinearMap fun a b => mul_comm a b
  isNonneg := ⟨fun a => by
    rw [← moment_centered_mul]
    exact ω.map_nonneg (sq_nonneg (LinearMap.centered ω.toLinearMap a))⟩

/-- Cauchy--Schwarz for covariance, derived from the generic theorem for positive semidefinite
bilinear forms rather than from a Cstar GNS representation. -/
theorem covariance_cauchy_schwarz (ω : 𝓢[ℝ, E]) (a b : E) :
    (LinearMap.covarianceForm ω.toLinearMap a b) ^ 2 ≤ variance ω a * variance ω b := by
  have h := (LinearMap.covarianceForm ω.toLinearMap).apply_sq_le_of_symm
    (covarianceForm_isPosSemidef ω).isNonneg.nonneg
    (LinearMap.BilinForm.isSymm_iff.mp (covarianceForm_isPosSemidef ω).isSymm) a b
  simpa only [← variance_eq_covarianceForm_self] using h

/-! ## B. Positivity of the covariance matrix -/

/-- **Uncertainty theory, the Jordan-algebraic core**: the covariance matrix of a finite family of
observables is positive semidefinite. This is the coordinate form of
`covarianceForm_isPosSemidef`, obtained by evaluating the form on `∑ i, c i • a i`. -/
theorem covMatrix_posSemidef {ι : Type*} [Fintype ι] (ω : 𝓢[ℝ, E]) (a : ι → E) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * LinearMap.covarianceForm ω.toLinearMap (a i) (a j) := by
  have hnonneg := (covarianceForm_isPosSemidef ω).isNonneg.nonneg (∑ i, c i • a i)
  simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, LinearMap.covarianceForm_apply]
    at hnonneg
  refine hnonneg.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.covarianceForm_isSymm ω.toLinearMap (fun x y => mul_comm x y) |>.eq]
  rw [LinearMap.covarianceForm_apply]
  ring

end IsJordanOrderUnit
