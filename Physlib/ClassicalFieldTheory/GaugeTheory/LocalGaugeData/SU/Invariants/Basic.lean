/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.TensorSpecies
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
/-!
# Elements of `SU(N)` in a coordinate plane, and what commutes with them

## i. Overview

For two distinct coordinates `p` and `q`, an element `U` of `SU(2)` acts on the plane they span
and fixes the other coordinates: this is `SU.planeEmbed p q`, a group homomorphism from `SU(2)`
to `SU(N)` (A, B). Writing `P` for the inclusion of the plane, the embedded element is
`1 + P (U - 1) Pᵀ`, and conjugating `P M Pᵀ` by it gives `P (U M U†) Pᵀ`, so the action on the
matrices supported on the plane is computed in `SU(2)`.

Three elements of `SU(2)` do all the work: a diagonal phase `diag (u, ū)`, the rotation by a
quarter turn, and the rotation by an eighth of a turn. Embedded in every plane, they force a
matrix commuting with all of `SU(N)` to be scalar (C), and a linear endomorphism of the
complexified Lie algebra `ℂ ⊗[ℝ] su(N)` commuting with the adjoint action to be scalar (D); the
latter is computed on the matrices `adjMat A`, which identify the complexified Lie algebra with the
traceless complex matrices. These are the two facts behind the
classification of the invariant tensors of `SU(N)` with a fundamental and an anti-fundamental
index, and with one or two adjoint indices.

## ii. Key results

- `SU.planeEmbed` : `SU(2)` acting on the plane of two coordinates, as a subgroup of `SU(N)`.
- `SU.eq_smul_one_of_commute` : a matrix commuting with `SU(N)` is scalar.
- `suTensor.eq_smul_id_of_commute_adjRep` : an endomorphism of the complexified Lie algebra
  commuting with the adjoint action is scalar.

## iii. Table of contents

- A. The plane matrices
- B. The plane embedding of `SU(2)`
- C. Matrices commuting with `SU(N)`
- D. Endomorphisms of the complexified Lie algebra commuting with `SU(N)`

-/

@[expose] public section

open Matrix MatrixGroups

namespace SU

variable {N : ℕ}

/-!

## A. The plane matrices

-/

/-- The inclusion of the plane of the coordinates `p` and `q`: the `N × 2` matrix whose columns
  are the basis vectors `e_p` and `e_q`. -/
def planeInclusion (p q : Fin N) : Matrix (Fin N) (Fin 2) ℂ :=
  Matrix.of fun x i => if x = ![p, q] i then 1 else 0

@[simp]
lemma planeInclusion_apply (p q : Fin N) (x : Fin N) (i : Fin 2) :
    planeInclusion p q x i = if x = ![p, q] i then 1 else 0 := rfl

/-- The inclusion of the plane of two distinct coordinates is an isometry. -/
lemma planeInclusion_transpose_mul {p q : Fin N} (hpq : p ≠ q) :
    (planeInclusion p q)ᵀ * planeInclusion p q = 1 := by
  ext i j
  simp only [mul_apply, transpose_apply, planeInclusion_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_apply]
  fin_cases i <;> fin_cases j <;> simp [hpq, Ne.symm hpq]

/-- The inclusion of the plane has real entries, so its conjugate transpose is its transpose. -/
lemma conjTranspose_planeInclusion (p q : Fin N) :
    (planeInclusion p q)ᴴ = (planeInclusion p q)ᵀ := by
  ext i x
  simp only [conjTranspose_apply, transpose_apply, planeInclusion_apply]
  split_ifs <;> simp

/-- The matrix acting as `U` on the plane of the coordinates `p` and `q` and as the identity on
  the other coordinates. -/
def planeMatrix (p q : Fin N) (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1 + planeInclusion p q * (U - 1) * (planeInclusion p q)ᵀ

variable {p q : Fin N}

/-- The plane matrix of the identity is the identity. -/
@[simp]
lemma planeMatrix_one : planeMatrix p q 1 = 1 := by
  simp [planeMatrix]

/-- The plane matrices multiply as the matrices on the plane. -/
lemma planeMatrix_mul (hpq : p ≠ q) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    planeMatrix p q U * planeMatrix p q V = planeMatrix p q (U * V) := by
  set P := planeInclusion p q
  have h : P * (U - 1) * Pᵀ * (P * (V - 1) * Pᵀ) = P * ((U - 1) * (V - 1)) * Pᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, ← Matrix.mul_assoc Pᵀ,
      planeInclusion_transpose_mul hpq, Matrix.one_mul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_assoc P]
  rw [planeMatrix, planeMatrix, planeMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, h,
    show U * V - 1 = (U - 1) + (V - 1) + (U - 1) * (V - 1) by noncomm_ring,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

/-- The conjugate transpose of a plane matrix is the plane matrix of the conjugate
  transpose. -/
lemma conjTranspose_planeMatrix (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (planeMatrix p q U)ᴴ = planeMatrix p q Uᴴ := by
  have hP : (planeInclusion p q)ᵀᴴ = planeInclusion p q := by
    ext x i
    simp only [conjTranspose_apply, transpose_apply, planeInclusion_apply]
    split_ifs <;> simp
  rw [planeMatrix, planeMatrix, conjTranspose_add, conjTranspose_one, conjTranspose_mul,
    conjTranspose_mul, hP, conjTranspose_planeInclusion, conjTranspose_sub, conjTranspose_one,
    Matrix.mul_assoc]

/-- A plane matrix has the determinant of the matrix on the plane. -/
lemma det_planeMatrix (hpq : p ≠ q) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (planeMatrix p q U).det = U.det := by
  rw [planeMatrix, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc,
    planeInclusion_transpose_mul hpq, Matrix.mul_one, add_sub_cancel]

/-- A plane matrix moves the plane as the matrix on the plane does. -/
lemma planeMatrix_mul_planeInclusion (hpq : p ≠ q) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    planeMatrix p q U * planeInclusion p q = planeInclusion p q * U := by
  rw [planeMatrix, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
    planeInclusion_transpose_mul hpq, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  abel

/-- The transpose of the inclusion of the plane intertwines a plane matrix with the matrix on
  the plane. -/
lemma transpose_planeInclusion_mul_planeMatrix (hpq : p ≠ q) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (planeInclusion p q)ᵀ * planeMatrix p q U = U * (planeInclusion p q)ᵀ := by
  rw [planeMatrix, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    planeInclusion_transpose_mul hpq, Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul]
  abel

/-- Conjugating a matrix supported on the plane by a plane matrix conjugates it on the plane. -/
lemma planeMatrix_conj (hpq : p ≠ q) (U M : Matrix (Fin 2) (Fin 2) ℂ) :
    planeMatrix p q U * (planeInclusion p q * M * (planeInclusion p q)ᵀ) * (planeMatrix p q U)ᴴ
      = planeInclusion p q * (U * M * Uᴴ) * (planeInclusion p q)ᵀ := by
  rw [conjTranspose_planeMatrix, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    planeMatrix_mul_planeInclusion hpq, Matrix.mul_assoc, Matrix.mul_assoc,
    transpose_planeInclusion_mul_planeMatrix hpq]
  simp only [Matrix.mul_assoc]

/-- The block on the plane of a matrix conjugated by a plane matrix is the conjugate of its
  block. -/
lemma planeBlock_conj (hpq : p ≠ q) (U : Matrix (Fin 2) (Fin 2) ℂ) (C : Matrix (Fin N) (Fin N) ℂ) :
    (planeInclusion p q)ᵀ * (planeMatrix p q U * C * (planeMatrix p q U)ᴴ) * planeInclusion p q
      = U * ((planeInclusion p q)ᵀ * C * planeInclusion p q) * Uᴴ := by
  rw [conjTranspose_planeMatrix]
  simp only [← Matrix.mul_assoc]
  rw [transpose_planeInclusion_mul_planeMatrix hpq, Matrix.mul_assoc _ (planeMatrix p q Uᴴ),
    planeMatrix_mul_planeInclusion hpq]
  simp only [Matrix.mul_assoc]

/-- The entries of the block on the plane are the entries of the matrix at the two
  coordinates. -/
@[simp]
lemma planeBlock_apply (C : Matrix (Fin N) (Fin N) ℂ) (i j : Fin 2) :
    ((planeInclusion p q)ᵀ * C * planeInclusion p q) i j = C (![p, q] i) (![p, q] j) := by
  simp [mul_apply, planeInclusion_apply]

/-- A plane matrix of a diagonal matrix is diagonal. -/
lemma planeMatrix_diagonal (hpq : p ≠ q) (a b : ℂ) :
    planeMatrix p q (diagonal ![a, b])
      = diagonal fun x => if x = p then a else if x = q then b else 1 := by
  ext x y
  simp only [planeMatrix, Matrix.add_apply, one_apply, Matrix.mul_apply, transpose_apply,
    planeInclusion_apply, Matrix.sub_apply, diagonal_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases hxp : x = p <;> by_cases hxq : x = q <;> by_cases hyp : y = p <;>
    by_cases hyq : y = q <;> simp_all [Ne.symm hpq, @eq_comm _ p y, @eq_comm _ q y]

/-!

## B. The plane embedding of `SU(2)`

-/

/-- `SU(2)` acting on the plane of the coordinates `p` and `q` and trivially on the others: a
  homomorphism from `SU(2)` to `SU(N)`. -/
noncomputable def planeEmbed (p q : Fin N) (hpq : p ≠ q) : SU 2 →* SU N where
  toFun U := ⟨planeMatrix p q U.1, by
    have hU := mem_specialUnitaryGroup_iff.mp U.2
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose] at hU
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
      conjTranspose_planeMatrix, planeMatrix_mul hpq, det_planeMatrix hpq, hU.1, planeMatrix_one]
    exact ⟨rfl, hU.2⟩⟩
  map_one' := Subtype.ext planeMatrix_one
  map_mul' U V := Subtype.ext (planeMatrix_mul hpq U.1 V.1).symm

@[simp]
lemma planeEmbed_val (hpq : p ≠ q) (U : SU 2) : (planeEmbed p q hpq U).1 = planeMatrix p q U.1 :=
  rfl

/-- The diagonal element `diag (u, ū)` of `SU(2)`, for a complex number `u` of modulus one. -/
noncomputable def diagPhase (u : ℂ) (hu : u * star u = 1) : SU 2 :=
  ⟨diagonal ![u, star u], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose,
      diagonal_conjTranspose, diagonal_mul_diagonal, det_diagonal, Fin.prod_univ_two]
    have hu' : (starRingEnd ℂ) u * u = 1 := by rw [mul_comm]; exact hu
    have hu'' : u * (starRingEnd ℂ) u = 1 := hu
    refine ⟨?_, by simpa using hu⟩
    rw [← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hu', hu'']⟩

@[simp]
lemma diagPhase_val (u : ℂ) (hu : u * star u = 1) :
    (diagPhase u hu).1 = diagonal ![u, star u] := rfl

/-- The rotation `!![c, -s; s, c]` of `SU(2)`, for real `c` and `s` with `c² + s² = 1`. -/
noncomputable def rotation (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : SU 2 :=
  ⟨!![(c : ℂ), -s; s, c], by
    have h' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose, det_fin_two_of]
    refine ⟨?_, by linear_combination h'⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← pow_two] <;>
      first | linear_combination h' | ring⟩

@[simp]
lemma rotation_val (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (rotation c s h).1 = !![(c : ℂ), -s; s, c] := rfl

/-!

## C. Matrices commuting with `SU(N)`

The diagonal phase `diag (i, -i)` in the plane of `p` and `q` negates the entries at `(p, q)`
and `(q, p)` of a matrix it commutes with, and the quarter turn exchanges the diagonal entries
at `p` and `q`.

-/

/-- A matrix fixed by conjugation by a plane matrix has its block on the plane fixed by
  conjugation by the matrix on the plane. -/
lemma planeBlock_eq_of_conj_eq (hpq : p ≠ q) {U : Matrix (Fin 2) (Fin 2) ℂ}
    {C : Matrix (Fin N) (Fin N) ℂ} (hC : planeMatrix p q U * C * (planeMatrix p q U)ᴴ = C) :
    U * ((planeInclusion p q)ᵀ * C * planeInclusion p q) * Uᴴ
      = (planeInclusion p q)ᵀ * C * planeInclusion p q := by
  rw [← planeBlock_conj hpq, hC]

/-- A matrix commuting with every element of `SU(N)` is fixed by conjugation. -/
lemma conj_eq_of_commute {C : Matrix (Fin N) (Fin N) ℂ} (hC : ∀ g : SU N, g.1 * C = C * g.1)
    (g : SU N) : g.1 * C * g.1ᴴ = C := by
  have hg : g.1 * g.1ᴴ = 1 := by
    rw [← star_eq_conjTranspose, ← mem_unitaryGroup_iff]
    exact (mem_specialUnitaryGroup_iff.mp g.2).1
  rw [hC, Matrix.mul_assoc, hg, Matrix.mul_one]

/-- A matrix commuting with every element of `SU(N)` is diagonal, with equal diagonal
  entries. -/
lemma apply_eq_of_commute {C : Matrix (Fin N) (Fin N) ℂ} (hC : ∀ g : SU N, g.1 * C = C * g.1)
    (hpq : p ≠ q) : C p q = 0 ∧ C p p = C q q := by
  have hI : Complex.I * star Complex.I = 1 := by simp
  have h1 := congrFun (congrFun (planeBlock_eq_of_conj_eq hpq
    (conj_eq_of_commute hC (planeEmbed p q hpq (diagPhase Complex.I hI)))) 0) 1
  have h2 := congrFun (congrFun (planeBlock_eq_of_conj_eq hpq
    (conj_eq_of_commute hC (planeEmbed p q hpq (rotation 0 1 (by norm_num))))) 1) 1
  have hB : ∀ i j, ((planeInclusion p q)ᵀ * C * planeInclusion p q) i j
      = C (![p, q] i) (![p, q] j) := planeBlock_apply C
  generalize (planeInclusion p q)ᵀ * C * planeInclusion p q = B at h1 h2 hB
  simp only [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, diagPhase_val,
    rotation_val, diagonal_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    cons_val_fin_one, empty_val', Fin.isValue] at h1 h2
  simp only [hB] at h1 h2
  simp at h1 h2
  exact ⟨by linear_combination (-1 / 2 : ℂ) * h1 + (C p q / 2) * Complex.I_mul_I, h2⟩

/-- A matrix commuting with every element of `SU(N)` is scalar. -/
lemma eq_smul_one_of_commute {C : Matrix (Fin N) (Fin N) ℂ}
    (hC : ∀ g : SU N, g.1 * C = C * g.1) : ∃ z : ℂ, C = z • 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, Subsingleton.elim _ _⟩
  refine ⟨C ⟨0, hN⟩ ⟨0, hN⟩, ext fun x y => ?_⟩
  rw [Matrix.smul_apply, one_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x = ⟨0, hN⟩
    · simp [hx]
    · simp [(apply_eq_of_commute hC hx).2]
  · simp [hxy, (apply_eq_of_commute hC hxy).1]

end SU

/-!

## D. Endomorphisms of the complexified Lie algebra commuting with `SU(N)`

-/

namespace suTensor

open SU TensorProduct

variable {N : ℕ}

/-- The matrix unit at `(x, y)` off the diagonal, as an element of the complexified Lie algebra,
  and zero on the diagonal. -/
noncomputable def offDiag (x y : Fin N) : SUAlgebraComplexified N :=
  ofTraceless (if x = y then 0 else single x y 1)

/-- The difference of the diagonal matrix units at `x` and at `y`, as an element of the
  complexified Lie algebra. -/
noncomputable def diagDiff (x y : Fin N) : SUAlgebraComplexified N :=
  ofTraceless (single x x 1 - single y y 1)

lemma adjMat_offDiag (x y : Fin N) :
    adjMat N (offDiag x y) = if x = y then 0 else single x y 1 := by
  refine adjMat_ofTraceless ?_
  split_ifs with h
  · exact trace_zero _ _
  · exact trace_single_eq_of_ne _ _ _ h

lemma adjMat_offDiag_of_ne {x y : Fin N} (h : x ≠ y) : adjMat N (offDiag x y) = single x y 1 := by
  simp [adjMat_offDiag, h]

@[simp]
lemma offDiag_self (x : Fin N) : offDiag x x = 0 :=
  adjMat_injective (by simp [adjMat_offDiag])

@[simp]
lemma adjMat_diagDiff (x y : Fin N) : adjMat N (diagDiff x y) = single x x 1 - single y y 1 :=
  adjMat_ofTraceless (by rw [trace_sub, trace_single_eq_same, trace_single_eq_same, sub_self])

@[simp]
lemma diagDiff_self (x : Fin N) : diagDiff x x = 0 :=
  adjMat_injective (by simp)

/-- The inclusion of the plane carries the matrix units of the plane to those of the
  coordinates. -/
lemma planeInclusion_single (p q : Fin N) (i j : Fin 2) :
    planeInclusion p q * single i j (1 : ℂ) * (planeInclusion p q)ᵀ
      = single (![p, q] i) (![p, q] j) 1 := by
  ext x y
  have h : ∀ a b : Fin N, (if x = a then (1 : ℂ) else 0) * (if y = b then 1 else 0)
      = single a b (1 : ℂ) x y := fun a b => by
    by_cases hx : x = a
    · by_cases hy : y = b
      · subst hx hy
        simp
      · simp [hx, hy, Ne.symm hy]
    · simp [hx, Ne.symm hx]
  rw [← h]
  simp only [Matrix.mul_apply, transpose_apply, planeInclusion_apply, single_apply, ite_and,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Fintype.sum_eq_single j fun k hk => by simp [Ne.symm hk]]
  simp

/-- The adjoint action of an element of `SU(2)` embedded in a plane on a matrix supported on the
  plane. -/
lemma adjMat_adjRep_planeEmbed {p q : Fin N} (hpq : p ≠ q) (U : SU 2)
    (A : SUAlgebraComplexified N) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : adjMat N A = planeInclusion p q * M * (planeInclusion p q)ᵀ) :
    adjMat N (adjRep N (planeEmbed p q hpq U) A)
      = planeInclusion p q * (U.1 * M * U.1ᴴ) * (planeInclusion p q)ᵀ := by
  rw [adjMat_adjRep, val_inv, hA, planeEmbed_val, star_eq_conjTranspose,
    planeMatrix_conj hpq]

/-- The phase `(1 + i) / √2`, a square root of `i` of modulus one. -/
noncomputable def sqrtI : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)

lemma sqrt_two_mul_sqrt_two : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'

lemma star_sqrtI : star sqrtI = (1 - Complex.I) / (Real.sqrt 2 : ℂ) := by
  simp [sqrtI, Complex.conj_ofReal, sub_eq_add_neg]

lemma sqrtI_mul_star : sqrtI * star sqrtI = 1 := by
  rw [star_sqrtI, sqrtI, div_mul_div_comm, sqrt_two_mul_sqrt_two, div_eq_one_iff_eq two_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma sqrtI_mul_self : sqrtI * sqrtI = Complex.I := by
  rw [sqrtI, div_mul_div_comm, sqrt_two_mul_sqrt_two, div_eq_iff two_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma star_sqrtI_mul_self : star sqrtI * star sqrtI = -Complex.I := by
  rw [← star_mul, sqrtI_mul_self, Complex.star_def, Complex.conj_I]

lemma sqrtI_ne_I : sqrtI ≠ Complex.I := fun h => by
  have h' := congrArg Complex.re h
  rw [sqrtI, Complex.div_ofReal_re] at h'
  simp only [Complex.add_re, Complex.one_re, Complex.I_re, add_zero] at h'
  exact (div_ne_zero one_ne_zero (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne') h'

lemma star_sqrtI_ne_I : star sqrtI ≠ Complex.I := fun h => by
  have h' := congrArg Complex.re h
  rw [star_sqrtI, Complex.div_ofReal_re] at h'
  simp only [Complex.sub_re, Complex.one_re, Complex.I_re, sub_zero] at h'
  exact (div_ne_zero one_ne_zero (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne') h'

/-- The adjoint action of a diagonal matrix of `SU(N)` scales the entry at `(x, y)` by
  `d x * star (d y)`. -/
lemma adjMat_adjRep_apply_of_diagonal {g : SU N} {d : Fin N → ℂ} (hg : g.1 = diagonal d)
    (A : SUAlgebraComplexified N) (x y : Fin N) :
    adjMat N (adjRep N g A) x y = d x * adjMat N A x y * star (d y) := by
  rw [adjMat_adjRep, val_inv, hg, star_eq_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

variable {L : SUAlgebraComplexified N →ₗ[ℂ] SUAlgebraComplexified N}

/-- For `p ≠ q`, an endomorphism commuting with the adjoint action sends the matrix unit at
  `(p, q)` to a multiple of itself. The phase `diag (ω, ω̄)` in the plane of `p` and `q`, with
  `ω² = i`, multiplies that matrix unit by `i` and no other entry by `i`. -/
lemma map_offDiag_eq_smul (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
      L (adjRep N g A) = adjRep N g (L A)) {p q : Fin N} (hpq : p ≠ q) :
    L (offDiag p q) = adjMat N (L (offDiag p q)) p q • offDiag p q := by
  set d : Fin N → ℂ := fun x => if x = p then sqrtI else if x = q then star sqrtI else 1
  set g := planeEmbed p q hpq (diagPhase sqrtI sqrtI_mul_star)
  have hg : g.1 = diagonal d := by
    rw [planeEmbed_val, diagPhase_val, planeMatrix_diagonal hpq]
  have h1 : sqrtI * (starRingEnd ℂ) sqrtI = 1 := sqrtI_mul_star
  have h2 : (starRingEnd ℂ) sqrtI * sqrtI = 1 := by rw [mul_comm]; exact sqrtI_mul_star
  have h3 : (starRingEnd ℂ) sqrtI * (starRingEnd ℂ) sqrtI = -Complex.I := star_sqrtI_mul_self
  have h4 : (starRingEnd ℂ) sqrtI ≠ Complex.I := star_sqrtI_ne_I
  have h5 : (1 : ℂ) ≠ Complex.I := fun h => by simp [Complex.ext_iff] at h
  have h6 : -Complex.I ≠ Complex.I := fun h => by
    have := congrArg Complex.im h
    norm_num at this
  have hmul : ∀ x y, d x * star (d y) = Complex.I ↔ x = p ∧ y = q := fun x y => by
    by_cases hxp : x = p <;> by_cases hxq : x = q <;> by_cases hyp : y = p <;>
      by_cases hyq : y = q <;>
      simp_all [d, Ne.symm hpq, sqrtI_mul_self, sqrtI_ne_I]
  have hY : adjRep N g (L (offDiag p q)) = Complex.I • L (offDiag p q) := by
    rw [← hL, ← map_smul]
    congr 1
    refine adjMat_injective (Matrix.ext fun x y => ?_)
    rw [adjMat_adjRep_apply_of_diagonal hg, map_smul, Matrix.smul_apply,
      adjMat_offDiag_of_ne hpq, single_apply, smul_eq_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [mul_one, mul_one]
      exact (hmul _ _).2 ⟨rfl, rfl⟩
    · simp
  refine adjMat_injective (Matrix.ext fun x y => ?_)
  rw [map_smul, Matrix.smul_apply, adjMat_offDiag_of_ne hpq, single_apply, smul_eq_mul]
  have hxy := congrArg (fun A => adjMat N A x y) hY
  simp only [adjMat_adjRep_apply_of_diagonal hg, map_smul, Matrix.smul_apply,
    smul_eq_mul] at hxy
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [mul_one]
  · have hne : d x * star (d y) ≠ Complex.I := fun he =>
      h ⟨((hmul x y).1 he).1.symm, ((hmul x y).1 he).2.symm⟩
    rw [mul_zero]
    have h' : (d x * star (d y) - Complex.I) * adjMat N (L (offDiag p q)) x y = 0 := by
      linear_combination hxy
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hne)

/-- The quarter turn in the plane of `p` and `q` sends the matrix unit at `(p, q)` to minus the
  one at `(q, p)`. -/
lemma adjRep_quarterTurn_offDiag {p q : Fin N} (hpq : p ≠ q) :
    adjRep N (planeEmbed p q hpq (rotation 0 1 (by norm_num))) (offDiag p q) = -offDiag q p := by
  refine adjMat_injective ?_
  rw [adjMat_adjRep_planeEmbed hpq _ _ (single 0 1 1)
    (by rw [adjMat_offDiag_of_ne hpq, planeInclusion_single]; rfl)]
  rw [show (rotation 0 1 (by norm_num)).1 * single 0 1 1 * (rotation 0 1 (by norm_num)).1ᴴ
      = -single 1 0 (1 : ℂ) by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, single_apply, Matrix.vecMul, dotProduct]]
  rw [Matrix.mul_neg, Matrix.neg_mul, planeInclusion_single, map_neg,
    adjMat_offDiag_of_ne (Ne.symm hpq)]
  rfl

/-- The coefficients of the matrix units at `(p, q)` and at `(q, p)` agree. -/
lemma coeff_offDiag_swap (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
      L (adjRep N g A) = adjRep N g (L A)) {p q : Fin N} (hpq : p ≠ q) :
    adjMat N (L (offDiag q p)) q p = adjMat N (L (offDiag p q)) p q := by
  have h := hL (planeEmbed p q hpq (rotation 0 1 (by norm_num))) (offDiag p q)
  rw [adjRep_quarterTurn_offDiag, map_neg, map_offDiag_eq_smul hL (Ne.symm hpq),
    map_offDiag_eq_smul hL hpq, map_smul, adjRep_quarterTurn_offDiag] at h
  have h' := congrArg (fun A => adjMat N A q p) h
  simpa [adjMat_offDiag_of_ne (Ne.symm hpq)] using h'

/-- The cosine of an eighth of a turn, `1 / √2`. -/
noncomputable def invSqrtTwo : ℝ := (Real.sqrt 2)⁻¹

lemma invSqrtTwo_sq_add : invSqrtTwo ^ 2 + invSqrtTwo ^ 2 = 1 := by
  rw [invSqrtTwo, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma invSqrtTwo_mul_self : (invSqrtTwo : ℂ) * invSqrtTwo = 1 / 2 := by
  have h := invSqrtTwo_sq_add
  have h' : (invSqrtTwo : ℂ) ^ 2 + (invSqrtTwo : ℂ) ^ 2 = 1 := by exact_mod_cast h
  linear_combination h' / 2

/-- The eighth turn in the plane of `p` and `q` sends the sum of the matrix units at `(p, q)`
  and at `(q, p)` to minus the difference of the diagonal matrix units at `p` and at `q`. -/
lemma adjRep_eighthTurn_offDiag {p q : Fin N} (hpq : p ≠ q) :
    adjRep N (planeEmbed p q hpq (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add))
      (offDiag p q + offDiag q p) = -diagDiff p q := by
  refine adjMat_injective ?_
  rw [adjMat_adjRep_planeEmbed hpq _ _ (single 0 1 1 + single 1 0 1)
    (by rw [map_add, adjMat_offDiag_of_ne hpq, adjMat_offDiag_of_ne (Ne.symm hpq),
      Matrix.mul_add, Matrix.add_mul, planeInclusion_single, planeInclusion_single]; rfl)]
  rw [show (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add).1 * (single 0 1 1 + single 1 0 1)
      * (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add).1ᴴ
      = -(single 0 0 (1 : ℂ) - single 1 1 1) by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, single_apply, Matrix.vecMul, dotProduct] <;>
      first
        | linear_combination (2 : ℂ) * invSqrtTwo_mul_self
        | linear_combination (-2 : ℂ) * invSqrtTwo_mul_self]
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, planeInclusion_single,
    planeInclusion_single, map_neg, adjMat_diagDiff]
  rfl

/-- For `p ≠ q`, an endomorphism commuting with the adjoint action scales the difference of the
  diagonal matrix units at `p` and at `q` by the coefficient of the matrix unit at `(p, q)`. -/
lemma map_diagDiff_eq_smul (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
      L (adjRep N g A) = adjRep N g (L A)) {p q : Fin N} (hpq : p ≠ q) :
    L (diagDiff p q) = adjMat N (L (offDiag p q)) p q • diagDiff p q := by
  have h := hL (planeEmbed p q hpq (rotation invSqrtTwo invSqrtTwo invSqrtTwo_sq_add))
    (offDiag p q + offDiag q p)
  rw [adjRep_eighthTurn_offDiag, map_neg, map_add, map_offDiag_eq_smul hL (Ne.symm hpq),
    map_offDiag_eq_smul hL hpq, coeff_offDiag_swap hL hpq, ← smul_add, map_smul,
    adjRep_eighthTurn_offDiag, smul_neg] at h
  exact neg_injective h

/-- For distinct `p`, `q` and `r`, the coefficients of the matrix units at `(p, q)` and at
  `(p, r)` agree: the difference of the diagonal units at `p` and `r` is the sum of those at `p`
  and `q` and at `q` and `r`. -/
lemma coeff_offDiag_eq (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
      L (adjRep N g A) = adjRep N g (L A)) {p q r : Fin N} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) : adjMat N (L (offDiag p r)) p r = adjMat N (L (offDiag p q)) p q := by
  have hsum : diagDiff p r = diagDiff p q + diagDiff q r :=
    adjMat_injective (by simp)
  have h := congrArg L hsum
  rw [map_add, map_diagDiff_eq_smul hL hpr, map_diagDiff_eq_smul hL hpq,
    map_diagDiff_eq_smul hL hqr] at h
  have h' := congrArg (fun A => adjMat N A p p) h
  simpa [single_apply, hpq, hpr, Ne.symm hpq, Ne.symm hpr] using h'

/-- All the matrix units off the diagonal have the same coefficient under an endomorphism
  commuting with the adjoint action. -/
lemma exists_coeff_offDiag_eq (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
      L (adjRep N g A) = adjRep N g (L A)) :
    ∃ μ : ℂ, ∀ x y : Fin N, x ≠ y → adjMat N (L (offDiag x y)) x y = μ := by
  by_cases hN : 2 ≤ N
  · set a : Fin N := ⟨0, by omega⟩
    set b : Fin N := ⟨1, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have ha : ∀ y, a ≠ y → adjMat N (L (offDiag a y)) a y = adjMat N (L (offDiag a b)) a b :=
      fun y hy => by
        by_cases hyb : y = b
        · rw [hyb]
        · exact coeff_offDiag_eq hL hab hy (Ne.symm hyb)
    refine ⟨adjMat N (L (offDiag a b)) a b, fun x y hxy => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      exact ha y hxy
    · by_cases hya : y = a
      · subst hya
        rw [coeff_offDiag_swap hL (Ne.symm hxy)]
        exact ha x (Ne.symm hxa)
      · rw [coeff_offDiag_eq hL hxa hxy (Ne.symm hya), coeff_offDiag_swap hL (Ne.symm hxa)]
        exact ha x (Ne.symm hxa)
  · refine ⟨0, fun x y hxy => absurd ?_ hxy⟩
    ext
    omega

/-- An element of the complexified Lie algebra is the combination of the entries of its matrix off
  the diagonal against the matrix
  units, and of its diagonal entries against the differences of the diagonal matrix units at a
  fixed coordinate. -/
lemma eq_sum_offDiag_add_sum_diagDiff (A : SUAlgebraComplexified N) (x₀ : Fin N) :
    A = ∑ x, ∑ y, adjMat N A x y • offDiag x y + ∑ x, adjMat N A x x • diagDiff x x₀ := by
  have htr : ∑ x, adjMat N A x x = 0 := trace_adjMat A
  refine adjMat_injective (Matrix.ext fun i j => ?_)
  have hoff : ∀ x y, adjMat N (offDiag x y) i j = if x = i ∧ y = j ∧ i ≠ j then 1 else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [adjMat_offDiag, ite_true, Matrix.zero_apply]
      split_ifs with h
      · exact absurd (h.1.symm.trans h.2.1) h.2.2
      · rfl
    · rw [adjMat_offDiag_of_ne hxy, single_apply]
      by_cases h : x = i ∧ y = j
      · obtain ⟨rfl, rfl⟩ := h
        simp [hxy]
      · rw [ite_eq_right_iff.mpr fun h' => absurd h' h,
          ite_eq_right_iff.mpr fun h' => absurd ⟨h'.1, h'.2.1⟩ h]
  simp only [map_add, map_sum, map_smul, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, adjMat_diagDiff, Matrix.sub_apply, hoff,
    single_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  by_cases hij : i = j
  · subst hij
    have hx₀ : (∑ x, if x₀ = i then adjMat N A x x else 0) = 0 := by
      split_ifs <;> simp [htr]
    simp only [ne_eq, not_true_eq_false, and_false, ite_false, Finset.sum_const_zero, and_self,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, hx₀, sub_zero, zero_add]
  · have h2 : ∀ x : Fin N, ¬(x = i ∧ x = j) := fun x h => hij (h.1.symm.trans h.2)
    simp only [h2, ite_false, Finset.sum_const_zero, sub_zero, add_zero]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp),
      Finset.sum_eq_single j (fun y _ hy => by simp [hy]) (by simp)]
    simp [hij]

/-- An endomorphism of the complexified Lie algebra commuting with the adjoint action of every
  element of `SU(N)` is scalar: a form of Schur's lemma for the adjoint representation. -/
lemma eq_smul_id_of_commute_adjRep (hL : ∀ (g : SU N) (A : SUAlgebraComplexified N),
      L (adjRep N g A) = adjRep N g (L A)) :
    ∃ z : ℂ, L = z • LinearMap.id := by
  obtain ⟨μ, hμ⟩ := exists_coeff_offDiag_eq hL
  refine ⟨μ, LinearMap.ext fun A => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (SUAlgebraComplexified 0) :=
      ⟨fun A B => adjMat_injective (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  have hoff : ∀ x y, L (offDiag x y) = μ • offDiag x y := fun x y => by
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [map_offDiag_eq_smul hL hxy, hμ x y hxy]
  have hdiag : ∀ x y, L (diagDiff x y) = μ • diagDiff x y := fun x y => by
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [map_diagDiff_eq_smul hL hxy, hμ x y hxy]
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  conv_lhs => rw [eq_sum_offDiag_add_sum_diagDiff A ⟨0, hN⟩]
  conv_rhs => rw [eq_sum_offDiag_add_sum_diagDiff A ⟨0, hN⟩]
  simp only [map_add, map_sum, map_smul, hoff, hdiag, smul_add, Finset.smul_sum, smul_comm μ]

end suTensor
