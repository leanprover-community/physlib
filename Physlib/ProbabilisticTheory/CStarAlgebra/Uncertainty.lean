/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.Matrix.PosSemidef
public import Physlib.Meta.TODO.Basic
public import Physlib.ProbabilisticTheory.CStarAlgebra.Statistics

/-!
# Uncertainty relations

The covariance and commutator matrices of observables bound each other.

## i. Overview

The covariance matrix `Σ` and the commutator matrix `Ω` of a family of observables satisfy the
uncertainty relation: `Σ + i Ω` is positive semidefinite. For finitely many observables it gives
the Robertson relation `|det Ω| ≤ det Σ`. For two observables it is the Robertson–Schrödinger
relation. The Robertson relation `Var a · Var b ≥ |ω ⁅a, b⁆|² / 4` follows from it.

## ii. Key results

- `ProbabilisticTheory.State.commutator` : half of `-i ω ⁅a, b⁆`, a real number.
- `ProbabilisticTheory.State.commutatorMatrix` : the commutator matrix of a family of observables.
- `ProbabilisticTheory.State.posSemidef_covarianceMatrix_add_commutatorMatrix` : the uncertainty
  relation for a family of observables.
- `ProbabilisticTheory.State.robertson_det` : the Robertson relation for finitely many observables.
- `ProbabilisticTheory.State.robertson_schrodinger` : the Robertson–Schrödinger relation.
- `ProbabilisticTheory.State.robertson` : the Robertson relation.

## iii. Table of contents

- A. The commutator of centered observables
- B. The uncertainty relation for a family of observables
- C. Two observables

## iv. References

* None.

-/

@[expose] public section

open scoped ComplexOrder

namespace ProbabilisticTheory.State

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

TODO "Connect the covariance, the variance and the uncertainty relations of states with their
  vector-state versions for symmetric operators in `QuantumMechanics.Operators.Uncertainty`."

/-! ## A. The commutator of centered observables -/

/-- Centering does not change the commutator. -/
lemma lie_centered (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) :
    ⁅(ω.centered a : 𝒜), (ω.centered b : 𝒜)⁆ = ⁅(a : 𝒜), (b : 𝒜)⁆ := by
  simp only [coe_centered, Ring.lie_def, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one]
  module

/-- The value of `ω` on the commutator is twice `i` times the imaginary part of `ω` on the product
of the centered observables. -/
lemma extend_lie (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) :
    ω.extend ⁅(a : 𝒜), (b : 𝒜)⁆ =
      ((2 * (ω.extend ((ω.centered a : 𝒜) * ω.centered b)).im : ℝ) : ℂ) * Complex.I := by
  rw [← lie_centered, Ring.lie_def, map_sub, extend_centered_mul_swap ω a b, Complex.star_def,
    Complex.sub_conj]

/-- Half of `-i ω ⁅a, b⁆`. It is real since `ω ⁅a, b⁆` is imaginary. -/
noncomputable def commutator (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) : ℝ :=
  (ω.extend ⁅(a : 𝒜), (b : 𝒜)⁆).im / 2

/-- Swapping the observables changes the sign of the commutator. -/
lemma commutator_swap (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) :
    ω.commutator b a = -ω.commutator a b := by
  rw [commutator, commutator, Ring.lie_def, Ring.lie_def, ← neg_sub, map_neg, Complex.neg_im,
    neg_div]

/-- An observable commutes with itself. -/
@[simp]
lemma commutator_self (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) :
    ω.commutator a a = 0 := by
  simp [commutator, Ring.lie_def]

/-! ## B. The uncertainty relation for a family of observables -/

/-- The commutator matrix of a family of observables. -/
noncomputable def commutatorMatrix (ω : (ofCStarAlgebra 𝒜).State) {ι : Type*}
    (a : ι → selfAdjoint 𝒜) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ ω.commutator (a i) (a j)

/-- The entries of `Σ + i Ω` are the values of `ω` on the products of the centered observables. -/
lemma covarianceMatrix_add_commutatorMatrix_apply (ω : (ofCStarAlgebra 𝒜).State) {ι : Type*}
    (a : ι → selfAdjoint 𝒜) (i j : ι) :
    ((ω.covarianceMatrix a).map Complex.ofReal +
        Complex.I • (ω.commutatorMatrix a).map Complex.ofReal) i j =
      ω.extend ((ω.centered (a i) : 𝒜) * ω.centered (a j)) := by
  simp [covarianceMatrix, commutatorMatrix, covariance, commutator, extend_lie, Complex.ext_iff]

/-- The uncertainty relation for a family of observables: `Σ + i Ω` is positive semidefinite. -/
lemma posSemidef_covarianceMatrix_add_commutatorMatrix (ω : (ofCStarAlgebra 𝒜).State)
    {ι : Type*} (a : ι → selfAdjoint 𝒜) :
    ((ω.covarianceMatrix a).map Complex.ofReal +
      Complex.I • (ω.commutatorMatrix a).map Complex.ofReal).PosSemidef := by
  convert ω.posSemidef_extend_centered_mul a using 1
  ext i j
  exact ω.covarianceMatrix_add_commutatorMatrix_apply a i j

/-- `Σ - i Ω` is the entrywise conjugate of the hermitian `Σ + i Ω`, which is its transpose. So it
is positive semidefinite as well. -/
lemma posSemidef_covarianceMatrix_sub_commutatorMatrix (ω : (ofCStarAlgebra 𝒜).State)
    {ι : Type*} (a : ι → selfAdjoint 𝒜) :
    ((ω.covarianceMatrix a).map Complex.ofReal -
      Complex.I • (ω.commutatorMatrix a).map Complex.ofReal).PosSemidef := by
  have h := posSemidef_covarianceMatrix_add_commutatorMatrix ω a
  convert h.transpose using 1
  rw [← h.1.eq, Matrix.conjTranspose_transpose]
  ext i j
  simp [sub_eq_add_neg]

/-- The Robertson relation for finitely many observables, `|det Ω| ≤ det Σ`. -/
lemma robertson_det (ω : (ofCStarAlgebra 𝒜).State) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → selfAdjoint 𝒜) : |(ω.commutatorMatrix a).det| ≤ (ω.covarianceMatrix a).det :=
  Matrix.abs_det_le_det_of_posSemidef (posSemidef_covarianceMatrix_sub_commutatorMatrix ω a)
    (posSemidef_covarianceMatrix_add_commutatorMatrix ω a)

/-! ## C. Two observables -/

/-- The Robertson–Schrödinger relation, the case of two observables. -/
lemma robertson_schrodinger (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) :
    ω.covariance a b ^ 2 + ω.commutator a b ^ 2 ≤ ω.variance a * ω.variance b := by
  have h := ω.robertson_det ![a, b]
  rw [Matrix.det_fin_two, Matrix.det_fin_two] at h
  simp [covarianceMatrix, commutatorMatrix, covariance_comm ω b a] at h
  rw [commutator_swap ω b a, abs_neg, abs_mul_abs_self] at h
  rw [variance_eq_covariance, variance_eq_covariance, commutator_swap ω b a, neg_sq]
  nlinarith

/-- The Robertson relation `Var a · Var b ≥ |ω ⁅a, b⁆|² / 4`. -/
lemma robertson (ω : (ofCStarAlgebra 𝒜).State) (a b : selfAdjoint 𝒜) :
    ω.commutator a b ^ 2 ≤ ω.variance a * ω.variance b :=
  le_trans (le_add_of_nonneg_left (sq_nonneg _)) (robertson_schrodinger ω a b)

end ProbabilisticTheory.State
