/-
Copyright (c) 2026 Zhuoran Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoran Li
-/
module

public import Physlib.Relativity.Fermions.Dirac.Basic
/-!
# Gamma endomorphisms of Dirac fermions

The basis `chiralBasis` orders the coordinates as
`(left 0, left 1, dualRight 0, dualRight 1)`. The Weyl bases are the standard
coordinate bases: the first component has an undotted upper spinor index and the
second a dotted lower spinor index. Thus the upper-right block is `σ^μ` and the
lower-left block is `bar σ^μ = (1, -σ¹, -σ², -σ³)`.

`gamma` transports these chiral matrices to complex linear endomorphisms of
`Dirac`. Its Lorentz index is `Fin 1 ⊕ Fin 3`, with signature `(+,-,-,-)`.
These coordinates differ from the Dirac representation in
`Physlib.Relativity.CliffordAlgebra`.

The Clifford relations hold at the endomorphism level. The chirality operator
`gamma5` has matrix `diag(-1, -1, 1, 1)`, and defines the complementary projectors
`leftChiralProjector` and `rightChiralProjector`.
-/

@[expose] public section

namespace Fermion.Dirac

noncomputable section

open Complex Matrix

/-! ## A. Matrices in the chiral basis -/

/-- The gamma matrices in `chiralBasis`, with blocks `[0, σ^μ; bar σ^μ, 0]`. -/
def gammaMatrix : Fin 1 ⊕ Fin 3 → Matrix (Fin 4) (Fin 4) ℂ
  | Sum.inl 0 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | Sum.inr 0 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  | Sum.inr 1 => !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0]
  | Sum.inr 2 => !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

/-- The chiral matrices use Physlib's Pauli matrices with no spinor-coordinate permutation. -/
lemma gammaMatrix_eq_fromBlocks (μ : Fin 1 ⊕ Fin 3) :
    gammaMatrix μ =
      (fromBlocks 0 (PauliMatrix.pauliMatrix μ)
        ((minkowskiMatrix μ μ : ℂ) • PauliMatrix.pauliMatrix μ) 0).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  simp only [submatrix_apply, Equiv.symm_apply_apply]
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [gammaMatrix, PauliMatrix.pauliMatrix, finSumFinEquiv,
      Fin.castAdd, Fin.castLE, Fin.natAdd, Fin.addNat, Matrix.cons_val_two, Matrix.cons_val_three]

private lemma gammaMatrix_anticomm (μ ν : Fin 1 ⊕ Fin 3) :
    gammaMatrix μ * gammaMatrix ν + gammaMatrix ν * gammaMatrix μ =
      (2 * (minkowskiMatrix μ ν : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases μ <;> fin_cases ν <;>
    simp [gammaMatrix, minkowskiMatrix.off_diag_zero] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.one_apply]

/-! ## B. Gamma endomorphisms and the Clifford relations -/

/-- The gamma endomorphisms of `Dirac`, defined using its chiral basis. Multiplication
of these endomorphisms is composition, with the right factor acting first. -/
def gamma (μ : Fin 1 ⊕ Fin 3) : Module.End ℂ Dirac :=
  Matrix.toLinAlgEquiv chiralBasis (gammaMatrix μ)

/-- The matrix of a gamma endomorphism in the chiral basis. -/
@[simp]
lemma gamma_toMatrix (μ : Fin 1 ⊕ Fin 3) :
    LinearMap.toMatrix chiralBasis chiralBasis (gamma μ) = gammaMatrix μ :=
  (LinearMap.toMatrix chiralBasis chiralBasis).apply_symm_apply _

/-- A gamma endomorphism acts on a basis vector by the corresponding matrix column. -/
lemma gamma_apply_chiralBasis (μ : Fin 1 ⊕ Fin 3) (j : Fin 4) :
    gamma μ (chiralBasis j) = ∑ i, gammaMatrix μ i j • chiralBasis i :=
  Matrix.toLinAlgEquiv_self _ _ _

@[simp]
lemma gamma_apply_chiralBasis_repr (μ : Fin 1 ⊕ Fin 3) (i j : Fin 4) :
    chiralBasis.repr (gamma μ (chiralBasis j)) i = gammaMatrix μ i j := by
  rw [← LinearMap.toMatrix_apply, gamma_toMatrix]

/-- The Clifford anticommutator for gamma endomorphisms, with signature `(+,-,-,-)`. -/
theorem gamma_anticomm (μ ν : Fin 1 ⊕ Fin 3) :
    gamma μ * gamma ν + gamma ν * gamma μ =
      (2 * (minkowskiMatrix μ ν : ℂ)) • (1 : Module.End ℂ Dirac) := by
  apply (LinearMap.toMatrix chiralBasis chiralBasis).injective
  simpa only [map_add, map_smul, LinearMap.toMatrix_mul, gamma_toMatrix,
    LinearMap.toMatrix_one] using gammaMatrix_anticomm μ ν

/-- A gamma endomorphism squares to the corresponding diagonal metric sign. -/
lemma gamma_mul_self (μ : Fin 1 ⊕ Fin 3) :
    gamma μ * gamma μ = (minkowskiMatrix μ μ : ℂ) • (1 : Module.End ℂ Dirac) := by
  apply smul_right_injective _ (two_ne_zero (α := ℂ))
  simpa only [mul_smul, two_smul] using gamma_anticomm μ μ

/-- The time gamma endomorphism squares to the identity. -/
@[simp]
lemma gamma_inl_zero_mul_self : gamma (Sum.inl 0) * gamma (Sum.inl 0) = 1 := by
  simpa using gamma_mul_self (Sum.inl 0)

/-- Each spatial gamma endomorphism squares to minus the identity. -/
@[simp]
lemma gamma_inr_mul_self (i : Fin 3) : gamma (Sum.inr i) * gamma (Sum.inr i) = -1 := by
  simpa using gamma_mul_self (Sum.inr i)

/-- Gamma endomorphisms with distinct Lorentz indices anticommute. -/
lemma gamma_mul_gamma_of_ne {μ ν : Fin 1 ⊕ Fin 3} (h : μ ≠ ν) :
    gamma μ * gamma ν = -(gamma ν * gamma μ) := by
  apply eq_neg_of_add_eq_zero_left
  simpa only [minkowskiMatrix.off_diag_zero h, Complex.ofReal_zero, mul_zero, zero_smul]
    using gamma_anticomm μ ν

/-! ## C. Chirality -/

/-- The chirality endomorphism `γ⁵ = i γ⁰ γ¹ γ² γ³`. -/
def gamma5 : Module.End ℂ Dirac :=
  I • (gamma (Sum.inl 0) * gamma (Sum.inr 0) * gamma (Sum.inr 1) * gamma (Sum.inr 2))

/-- In the chiral basis, `γ⁵` is negative on the left-handed coordinates and positive
on the dual-right-handed coordinates. -/
@[simp]
lemma gamma5_toMatrix :
    LinearMap.toMatrix chiralBasis chiralBasis gamma5 = diagonal ![-1, -1, 1, 1] := by
  simp only [gamma5, map_smul, LinearMap.toMatrix_mul, gamma_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gammaMatrix, Matrix.diagonal, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The chirality endomorphism squares to the identity. -/
@[simp]
lemma gamma5_mul_self : gamma5 * gamma5 = 1 := by
  apply (LinearMap.toMatrix chiralBasis chiralBasis).injective
  simp only [LinearMap.toMatrix_mul, gamma5_toMatrix, LinearMap.toMatrix_one,
    Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.one_apply]

/-- The chirality endomorphism anticommutes with every gamma endomorphism. -/
lemma gamma5_mul_gamma (μ : Fin 1 ⊕ Fin 3) : gamma5 * gamma μ = -(gamma μ * gamma5) := by
  apply (LinearMap.toMatrix chiralBasis chiralBasis).injective
  simp only [LinearMap.toMatrix_mul, map_neg, gamma5_toMatrix, gamma_toMatrix]
  ext i j
  simp only [Matrix.neg_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [gammaMatrix, Matrix.cons_val_two, Matrix.cons_val_three]

/-! ## D. Chiral projectors -/

/-- The projector `(1 - γ⁵) / 2` onto the left-handed Weyl component. -/
def leftChiralProjector : Module.End ℂ Dirac := (2 : ℂ)⁻¹ • (1 - gamma5)

/-- The projector `(1 + γ⁵) / 2` onto the dual-right-handed Weyl component. -/
def rightChiralProjector : Module.End ℂ Dirac := (2 : ℂ)⁻¹ • (1 + gamma5)

/-- The left chiral projector retains the first two chiral coordinates. -/
@[simp]
lemma leftChiralProjector_toMatrix :
    LinearMap.toMatrix chiralBasis chiralBasis leftChiralProjector = diagonal ![1, 1, 0, 0] := by
  simp only [leftChiralProjector, map_smul, map_sub, LinearMap.toMatrix_one, gamma5_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal, Matrix.one_apply, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The right chiral projector retains the last two chiral coordinates. -/
@[simp]
lemma rightChiralProjector_toMatrix :
    LinearMap.toMatrix chiralBasis chiralBasis rightChiralProjector = diagonal ![0, 0, 1, 1] := by
  simp only [rightChiralProjector, map_smul, map_add, LinearMap.toMatrix_one, gamma5_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal, Matrix.one_apply, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The left chiral projector is idempotent. -/
@[simp]
lemma leftChiralProjector_mul_self : leftChiralProjector * leftChiralProjector =
    leftChiralProjector := by
  simp only [leftChiralProjector, smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul,
    one_mul, mul_one, gamma5_mul_self]
  module

/-- The right chiral projector is idempotent. -/
@[simp]
lemma rightChiralProjector_mul_self : rightChiralProjector * rightChiralProjector =
    rightChiralProjector := by
  simp only [rightChiralProjector, smul_mul_assoc, mul_smul_comm, mul_add, add_mul,
    one_mul, mul_one, gamma5_mul_self]
  module

/-- The chiral projectors are orthogonal. -/
@[simp]
lemma leftChiralProjector_mul_rightChiralProjector :
    leftChiralProjector * rightChiralProjector = 0 := by
  simp only [leftChiralProjector, rightChiralProjector, smul_mul_assoc, mul_smul_comm,
    mul_add, sub_mul, one_mul, mul_one, gamma5_mul_self]
  module

/-- The chiral projectors are orthogonal in the reverse order as well. -/
@[simp]
lemma rightChiralProjector_mul_leftChiralProjector :
    rightChiralProjector * leftChiralProjector = 0 := by
  simp only [leftChiralProjector, rightChiralProjector, smul_mul_assoc, mul_smul_comm,
    mul_sub, add_mul, one_mul, mul_one, gamma5_mul_self]
  module

/-- The two chiral projectors resolve the identity on `Dirac`. -/
@[simp]
lemma leftChiralProjector_add_rightChiralProjector :
    leftChiralProjector + rightChiralProjector = 1 := by
  simp only [leftChiralProjector, rightChiralProjector]
  module

end

end Fermion.Dirac
