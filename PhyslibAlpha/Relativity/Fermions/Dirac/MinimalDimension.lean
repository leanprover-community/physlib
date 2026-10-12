/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Physlib.Relativity.Fermions.Dirac.GammaMatrices
public import PhyslibAlpha.Relativity.PauliMatrices.Anticommuting
/-!

# The gamma matrices need four dimensions

## i. Overview

A Clifford family is a choice of `n × n` complex matrices `γ^μ`, one for each Lorentz index,
with `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} 1`. Dirac (1928) found one with `n = 4`, and no smaller
size works. Each `γ^μ` squares to `± 1`, so it is invertible, and `γ^0 γ^1 = -γ^1 γ^0` forces
`det (γ^0 γ^1) = (-1)ⁿ det (γ^0 γ^1)`: the size is even. Size two is excluded by the three
Pauli matrices: `γ^0, i γ^1, i γ^2, i γ^3` would be four anticommuting `2 × 2` involutions, and
`2 × 2` holds at most three. The Dirac endomorphisms `gamma` of Physlib, written as `4 × 4`
matrices, attain the bound.

## ii. Key results

- `IsCliffordFamily` : the relation `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} 1`.
- `IsCliffordFamily.even` : a Clifford family has even size.
- `IsCliffordFamily.ne_two` : there are no `2 × 2` Clifford families.
- `IsCliffordFamily.four_le` : a nonempty Clifford family has size at least four.
- `isCliffordFamily_gamma` : the Dirac gamma matrices are a Clifford family.
- `isLeast_size_isCliffordFamily` : the smallest size of a Clifford family is four.

## iii. Table of contents

- A. Clifford families
- B. The size is even
- C. Size two is excluded
- D. Dirac's matrices attain the bound

## iv. References

* P. A. M. Dirac, *The quantum theory of the electron*, Proc. R. Soc. London A 117 (1928)
  610–624.

-/

@[expose] public section

namespace Fermion.Dirac

open Matrix Complex

/-!

## A. Clifford families

-/

/-- A family of `n × n` matrices with `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} 1`. -/
def IsCliffordFamily {n : ℕ} (γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ μ ν, γ μ * γ ν + γ ν * γ μ = (2 * (minkowskiMatrix μ ν : ℂ)) • 1

namespace IsCliffordFamily

variable {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ} (hγ : IsCliffordFamily γ)
include hγ

lemma mul_self (μ : Fin 1 ⊕ Fin 3) : γ μ * γ μ = (minkowskiMatrix μ μ : ℂ) • 1 := by
  have h := hγ μ μ
  rw [← two_smul ℂ (γ μ * γ μ), mul_smul] at h
  exact smul_right_injective _ two_ne_zero h

lemma mul_comm_of_ne {μ ν : Fin 1 ⊕ Fin 3} (h : μ ≠ ν) : γ ν * γ μ = -(γ μ * γ ν) := by
  have := hγ μ ν
  rw [minkowskiMatrix.off_diag_zero h, Complex.ofReal_zero, mul_zero, zero_smul] at this
  exact eq_neg_of_add_eq_zero_right this

/-- Each member squares to `± 1`, so it is invertible. -/
lemma det_ne_zero (μ : Fin 1 ⊕ Fin 3) : (γ μ).det ≠ 0 := fun h => by
  have := congrArg det (hγ.mul_self μ)
  rw [det_mul, h, zero_mul, det_smul, det_one, mul_one, eq_comm] at this
  have hη : (minkowskiMatrix μ μ : ℂ) ≠ 0 := by
    rcases μ with μ | μ
    · rw [Subsingleton.elim μ 0, minkowskiMatrix.inl_0_inl_0]
      norm_num
    · rw [minkowskiMatrix.inr_i_inr_i]
      norm_num
  exact pow_ne_zero _ hη this

/-!

## B. The size is even

-/

/-- **A Clifford family has even size.** -/
lemma even : Even n := by
  have hne : (Sum.inl 0 : Fin 1 ⊕ Fin 3) ≠ Sum.inr 0 := Sum.inl_ne_inr
  have hd : (γ (Sum.inl 0) * γ (Sum.inr 0)).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero (hγ.det_ne_zero _) (hγ.det_ne_zero _)
  have h := congrArg det (hγ.mul_comm_of_ne hne)
  rw [det_neg, Fintype.card_fin, det_mul, mul_comm, ← det_mul] at h
  have h1 : ((-1 : ℂ) ^ n) = 1 := mul_right_cancel₀ hd (h.symm.trans (one_mul _).symm)
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h1

/-!

## C. Size two is excluded

-/

/-- `γ^0, i γ^1, i γ^2, i γ^3`: four involutions that anticommute. -/
noncomputable def involutions (γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ)
    (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin n) (Fin n) ℂ :=
  (Sum.elim (fun _ => (1 : ℂ)) (fun _ => I) μ) • γ μ

omit hγ in
lemma involutions_anticomm (μ ν : Fin 1 ⊕ Fin 3) :
    involutions γ μ * involutions γ ν + involutions γ ν * involutions γ μ =
      (Sum.elim (fun _ => (1 : ℂ)) (fun _ => I) μ * Sum.elim (fun _ => (1 : ℂ)) (fun _ => I) ν) •
        (γ μ * γ ν + γ ν * γ μ) := by
  simp only [involutions, smul_mul_smul_comm, smul_add, mul_comm (Sum.elim _ _ ν)]

/-- **There are no `2 × 2` Clifford families**: they would give four anticommuting `2 × 2`
involutions. -/
lemma ne_two : n ≠ 2 := by
  rintro rfl
  have h : PauliMatrix.IsAnticommuting (involutions γ) := fun μ ν => by
    rw [involutions_anticomm, hγ, smul_smul]
    congr 1
    rcases μ with μ | μ <;> rcases ν with ν | ν
    · rw [Subsingleton.elim μ 0, Subsingleton.elim ν 0]
      simp [minkowskiMatrix.inl_0_inl_0]
    · simp
    · simp
    · by_cases hμν : μ = ν
      · subst hμν
        simp [minkowskiMatrix.inr_i_inr_i]
      · simp [hμν]
  have := h.card_le_three
  simp at this

/-- **A nonempty Clifford family has size at least four.** -/
theorem four_le (hn : n ≠ 0) : 4 ≤ n := by
  obtain ⟨k, hk⟩ := hγ.even
  have := hγ.ne_two
  omega

end IsCliffordFamily

/-!

## D. Dirac's matrices attain the bound

-/

/-- The Dirac gamma matrices, written as `4 × 4` matrices, are a Clifford family. -/
lemma isCliffordFamily_gamma : IsCliffordFamily fun μ => endEquivMatrix (gamma μ) := fun μ ν => by
  rw [← map_mul, ← map_mul, ← map_add, gamma_anticomm, map_smul, map_one]

/-- **The gamma matrices need four dimensions (Dirac, 1928).** The smallest size of a nonempty
Clifford family is four. -/
theorem isLeast_size_isCliffordFamily :
    IsLeast {n : ℕ | n ≠ 0 ∧ ∃ γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ,
      IsCliffordFamily γ} 4 :=
  ⟨⟨by norm_num, _, isCliffordFamily_gamma⟩, fun _ ⟨hn, _, hγ⟩ => hγ.four_le hn⟩

end Fermion.Dirac
