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
second a dotted lower spinor index.

`gammaMatrix` is Clifford multiplication by a real Lorentz vector, valued in
complex linear endomorphisms of `Dirac`. Physlib's `Lorentz.Vector` has upper
Lorentz indices and uses the Pauli basis `(1, -σ¹, -σ², -σ³)` for its Hermitian
matrix representation. Thus `gammaMatrix v` has upper-right block
`v⁰ 1 - vⁱ σⁱ` and lower-left block `v⁰ 1 + vⁱ σⁱ` in the chiral basis.

The upper-index components `gamma μ` are derived by raising the index of
`gammaMatrix (Lorentz.Vector.basis μ)`. In particular,
`gammaMatrix v = v⁰ gamma 0 - vⁱ gamma i`, with signature `(+,-,-,-)`.
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
open scoped Lorentz.Vector

/-! ## A. Clifford multiplication by Lorentz vectors -/

/-- Clifford multiplication by a Lorentz vector on `Dirac`, defined using its chiral basis.
This map is real linear because `Lorentz.Vector` is a real vector space. Each value is
a complex linear endomorphism; multiplication is composition, with the right factor first. -/
def gammaMatrix : Lorentz.Vector →ₗ[ℝ] Module.End ℂ Dirac :=
  (Matrix.toLinAlgEquiv chiralBasis).toLinearEquiv.toLinearMap.restrictScalars ℝ ∘ₗ
    { toFun v :=
        (fromBlocks 0 (∑ μ, (minkowskiMatrix μ μ * v μ) • PauliMatrix.pauliMatrix μ)
          (∑ μ, v μ • PauliMatrix.pauliMatrix μ) 0).submatrix
          (finSumFinEquiv (m := 2) (n := 2)).symm
          (finSumFinEquiv (m := 2) (n := 2)).symm
      map_add' v w := by
        ext i j
        obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
        obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
        simp only [Matrix.add_apply, submatrix_apply, Equiv.symm_apply_apply]
        cases i <;> cases j <;>
          simp [fromBlocks, Lorentz.Vector.apply_add, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' r v := by
        simp only [Lorentz.Vector.apply_smul, RingHom.id_apply, mul_left_comm _ r,
          ← smul_smul, ← Finset.smul_sum]
        ext i j
        obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
        obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
        simp only [Matrix.smul_apply, submatrix_apply, Equiv.symm_apply_apply]
        cases i <;> cases j <;> simp [fromBlocks] }

/-- The chiral matrix of Clifford multiplication has blocks `[0, v_μ σ^μ; v^μ σ^μ, 0]`. -/
@[simp]
lemma gammaMatrix_toMatrix (v : Lorentz.Vector) :
    LinearMap.toMatrix chiralBasis chiralBasis (gammaMatrix v) =
      (fromBlocks 0 (∑ μ, (minkowskiMatrix μ μ * v μ) • PauliMatrix.pauliMatrix μ)
        (∑ μ, v μ • PauliMatrix.pauliMatrix μ) 0).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm :=
  (LinearMap.toMatrix chiralBasis chiralBasis).apply_symm_apply _

/-- The chiral matrices of Clifford multiplication on the Lorentz basis vectors. -/
lemma gammaMatrix_basis_toMatrix (μ : Fin 1 ⊕ Fin 3) :
    LinearMap.toMatrix chiralBasis chiralBasis (gammaMatrix (Lorentz.Vector.basis μ)) =
      match μ with
      | Sum.inl 0 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
      | Sum.inr 0 => !![0, 0, 0, -1; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
      | Sum.inr 1 => !![0, 0, 0, I; 0, 0, -I, 0; 0, -I, 0, 0; I, 0, 0, 0]
      | Sum.inr 2 => !![0, 0, -1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, -1, 0, 0] := by
  rw [gammaMatrix_toMatrix]
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  simp only [submatrix_apply, Equiv.symm_apply_apply]
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [Lorentz.Vector.basis_apply, PauliMatrix.pauliMatrix, finSumFinEquiv,
      Matrix.fromBlocks, Fin.castAdd, Fin.castLE, Fin.natAdd, Fin.addNat,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The Clifford anticommutator on pairs of Lorentz basis vectors. -/
lemma gammaMatrix_basis_anticomm (μ ν : Fin 1 ⊕ Fin 3) :
    gammaMatrix (Lorentz.Vector.basis μ) * gammaMatrix (Lorentz.Vector.basis ν) +
      gammaMatrix (Lorentz.Vector.basis ν) * gammaMatrix (Lorentz.Vector.basis μ) =
      (2 * ⟪Lorentz.Vector.basis μ, Lorentz.Vector.basis ν⟫ₘ) •
        (1 : Module.End ℂ Dirac) := by
  apply (LinearMap.toMatrix chiralBasis chiralBasis).injective
  rw [← Complex.coe_smul]
  simp only [map_add, LinearMap.toMatrix_mul, map_smul,
    LinearMap.toMatrix_one, gammaMatrix_basis_toMatrix]
  fin_cases μ <;> fin_cases ν <;> simp <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.one_apply]

/-- Clifford multiplication satisfies the anticommutator relation for the Minkowski product. -/
theorem gammaMatrix_anticomm (v w : Lorentz.Vector) :
    gammaMatrix v * gammaMatrix w + gammaMatrix w * gammaMatrix v =
      (2 * ⟪v, w⟫ₘ) • (1 : Module.End ℂ Dirac) := by
  let B := (LinearMap.mul ℝ (Module.End ℂ Dirac)).compl₁₂ gammaMatrix gammaMatrix
  let G : Lorentz.Vector →ₗ[ℝ] Lorentz.Vector →ₗ[ℝ] Module.End ℂ Dirac :=
    LinearMap.mk₂ ℝ (fun v w => (2 * ⟪v, w⟫ₘ) • (1 : Module.End ℂ Dirac))
      (by intros; simp [mul_add, add_smul])
      (by intros; simp [mul_smul, mul_left_comm])
      (by intros; simp [mul_add, add_smul])
      (by intros; simp [mul_smul, mul_left_comm])
  have h : B + B.flip = G := by
    apply Lorentz.Vector.basis.ext
    intro μ
    apply Lorentz.Vector.basis.ext
    intro ν
    exact gammaMatrix_basis_anticomm μ ν
  exact LinearMap.congr_fun₂ h v w

/-- Clifford multiplication squares to the Minkowski norm squared times the identity. -/
lemma gammaMatrix_mul_self (v : Lorentz.Vector) :
    gammaMatrix v * gammaMatrix v = ⟪v, v⟫ₘ • (1 : Module.End ℂ Dirac) := by
  apply smul_right_injective _ (two_ne_zero (α := ℝ))
  simpa only [mul_smul, two_smul] using gammaMatrix_anticomm v v

/-! ## B. Upper-index gamma components -/

/-- The upper-index gamma components `γ^μ`, obtained by raising the index of
Clifford multiplication on the Lorentz basis. Their chiral blocks are `[0, σ^μ; bar σ^μ, 0]`. -/
def gamma (μ : Fin 1 ⊕ Fin 3) : Module.End ℂ Dirac :=
  minkowskiMatrix μ μ • gammaMatrix (Lorentz.Vector.basis μ)

/-- Clifford multiplication on a Lorentz basis vector is the corresponding lower-index gamma. -/
lemma gammaMatrix_basis (μ : Fin 1 ⊕ Fin 3) :
    gammaMatrix (Lorentz.Vector.basis μ) = minkowskiMatrix μ μ • gamma μ := by
  simp [gamma, smul_smul]

/-- Clifford multiplication contracts the lower-index vector coordinates with `γ^μ`. -/
lemma gammaMatrix_eq_sum (v : Lorentz.Vector) :
    gammaMatrix v = ∑ μ, (minkowskiMatrix μ μ * v μ) • gamma μ := by
  calc
    gammaMatrix v = ∑ μ, v μ • gammaMatrix (Lorentz.Vector.basis μ) := by
      conv_lhs => rw [← Lorentz.Vector.basis.sum_repr v]
      simp [Lorentz.Vector.basis_repr_apply]
    _ = ∑ μ, (minkowskiMatrix μ μ * v μ) • gamma μ := by
      simp [gammaMatrix_basis, smul_smul, mul_comm]

/-- The matrix of a gamma endomorphism in the chiral basis. -/
@[simp]
lemma gamma_toMatrix (μ : Fin 1 ⊕ Fin 3) :
    LinearMap.toMatrix chiralBasis chiralBasis (gamma μ) =
      match μ with
      | Sum.inl 0 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
      | Sum.inr 0 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
      | Sum.inr 1 => !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0]
      | Sum.inr 2 => !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0] := by
  simp only [gamma, ← Complex.coe_smul, map_smul, gammaMatrix_basis_toMatrix]
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three]

/-- The Clifford anticommutator for gamma endomorphisms, with signature `(+,-,-,-)`. -/
theorem gamma_anticomm (μ ν : Fin 1 ⊕ Fin 3) :
    gamma μ * gamma ν + gamma ν * gamma μ =
      (2 * (minkowskiMatrix μ ν : ℂ)) • (1 : Module.End ℂ Dirac) := by
  simp only [gamma, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (minkowskiMatrix ν ν), ← smul_add, gammaMatrix_anticomm]
  rw [smul_smul, ← Complex.coe_smul]
  fin_cases μ <;> fin_cases ν <;>
    norm_num [minkowskiMatrix.off_diag_zero] <;> simp [minkowskiMatrix.off_diag_zero]

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
    norm_num [Matrix.diagonal, Matrix.cons_val_two, Matrix.cons_val_three]

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
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three]

/-- Chirality anticommutes with Clifford multiplication by every Lorentz vector. -/
lemma gamma5_mul_gammaMatrix (v : Lorentz.Vector) :
    gamma5 * gammaMatrix v = -(gammaMatrix v * gamma5) := by
  rw [gammaMatrix_eq_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    gamma5_mul_gamma, smul_neg, Finset.sum_neg_distrib]

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
