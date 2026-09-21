/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!

# Statistics of a linear functional on a bilinear algebra

## i. Overview

Second moments and covariance use only a bilinear multiplication and a linear functional. They do
not intrinsically require an order, positivity, associativity, commutativity, or the Jordan
identity. This file defines them at that level so ordered Jordan algebras and self-adjoint parts of
star algebras can share one canonical construction.

For `omega : E ->_l[R] R`, the covariance is packaged as the bilinear form

`(a, b) |-> omega (a * b) - omega a * omega b`.

Commutativity of the product is used only to prove symmetry. A unit and the normalization
`omega 1 = 1` are used only for centering identities. Positivity is deliberately left to the
ordered specialization.

## ii. Key definitions and results

- `LinearMap.secondMomentForm`
- `LinearMap.covarianceForm`
- `LinearMap.variance`
- `LinearMap.centered`
- `LinearMap.apply_centered`
- `LinearMap.apply_centered_mul_centered`

## iii. Table of contents

- A. Second moments and covariance
- B. Centering a normalized functional

-/

@[expose] public section

namespace LinearMap

variable {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E]
  [SMulCommClass ℝ E E] [IsScalarTower ℝ E E]

/-! ## A. Second moments and covariance -/

/-- The second-moment bilinear form associated to a linear functional:
`secondMomentForm omega a b = omega (a * b)`. -/
def secondMomentForm (omega : E →ₗ[ℝ] ℝ) : LinearMap.BilinForm ℝ E where
  toFun a :=
    { toFun := fun b => omega (a * b)
      map_add' := fun b c => by simp only [mul_add, map_add]
      map_smul' := fun c b => by simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' a b := by
    ext c
    change omega ((a + b) * c) = omega (a * c) + omega (b * c)
    rw [add_mul, map_add]
  map_smul' c a := by
    ext b
    change omega ((c • a) * b) = c • omega (a * b)
    rw [smul_mul_assoc, map_smul]

@[simp]
lemma secondMomentForm_apply (omega : E →ₗ[ℝ] ℝ) (a b : E) :
    secondMomentForm omega a b = omega (a * b) := rfl

/-- The covariance bilinear form associated to a linear functional:
`covarianceForm omega a b = omega (a * b) - omega a * omega b`. -/
def covarianceForm (omega : E →ₗ[ℝ] ℝ) : LinearMap.BilinForm ℝ E where
  toFun a :=
    { toFun := fun b => omega (a * b) - omega a * omega b
      map_add' := fun b c => by
        simp only [mul_add, map_add]
        ring
      map_smul' := fun c b => by
        simp only [mul_smul_comm, map_smul, RingHom.id_apply, smul_eq_mul]
        ring }
  map_add' a b := by
    ext c
    change omega ((a + b) * c) - omega (a + b) * omega c =
      (omega (a * c) - omega a * omega c) + (omega (b * c) - omega b * omega c)
    rw [add_mul, map_add, map_add]
    ring
  map_smul' c a := by
    ext b
    change omega ((c • a) * b) - omega (c • a) * omega b =
      c • (omega (a * b) - omega a * omega b)
    rw [smul_mul_assoc, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring

@[simp]
lemma covarianceForm_apply (omega : E →ₗ[ℝ] ℝ) (a b : E) :
    covarianceForm omega a b = omega (a * b) - omega a * omega b := rfl

/-- The covariance form is symmetric when the multiplication is commutative. -/
lemma covarianceForm_isSymm (omega : E →ₗ[ℝ] ℝ) (hcomm : ∀ a b : E, a * b = b * a) :
    (covarianceForm omega).IsSymm := ⟨fun a b => by
  simp only [covarianceForm_apply]
  rw [hcomm a b, mul_comm (omega a) (omega b)]⟩

/-- The variance associated to a linear functional is the diagonal of its covariance form. -/
def variance (omega : E →ₗ[ℝ] ℝ) (a : E) : ℝ := covarianceForm omega a a

lemma covarianceForm_self (omega : E →ₗ[ℝ] ℝ) (a : E) :
    covarianceForm omega a a = variance omega a := rfl

/-! ## B. Centering a normalized functional -/

variable [One E]

/-- Center `a` at the value assigned by `omega`: `a - omega(a) • 1`. -/
def centered (omega : E →ₗ[ℝ] ℝ) (a : E) : E := a - omega a • (1 : E)

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
/-- A normalized linear functional sends every centered element to zero. -/
@[simp]
lemma apply_centered (omega : E →ₗ[ℝ] ℝ) (homega : omega 1 = 1) (a : E) :
    omega (centered omega a) = 0 := by
  simp [centered, homega]

/-- For a normalized functional, covariance is its value on the product of centered elements. -/
lemma apply_centered_mul_centered (omega : E →ₗ[ℝ] ℝ) (homega : omega 1 = 1)
    (honeLeft : ∀ x : E, 1 * x = x) (honeRight : ∀ x : E, x * 1 = x) (a b : E) :
    omega (centered omega a * centered omega b) = covarianceForm omega a b := by
  simp only [centered, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, map_sub, map_smul,
    smul_eq_mul, covarianceForm_apply, honeLeft, honeRight, homega]
  ring

end LinearMap
