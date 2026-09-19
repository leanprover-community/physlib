/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Notation
/-!

# The hat map on three-dimensional vectors

The hat map sends a vector `ω : Fin 3 → ℝ` to the skew-symmetric matrix `[ω]ₓ` characterised by
`[ω]ₓ *ᵥ v = ω ⨯₃ v`. It realises the correspondence between `ℝ³` and the skew-symmetric `3 × 3`
matrices (the Lie algebra `𝖘𝖔(3)`), and underlies the angular velocity of a rigid body.

-/

@[expose] public section

namespace Matrix

/-- The hat map `[ω]ₓ`: the skew-symmetric `3 × 3` matrix acting as the cross product with `ω`,
i.e. `[ω]ₓ *ᵥ v = ω ⨯₃ v`. -/
def crossProductMatrix (ω : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -ω 2, ω 1; ω 2, 0, -ω 0; -ω 1, ω 0, 0]

/-- The hat matrix acts on a vector as the cross product. -/
@[simp]
lemma crossProductMatrix_mulVec (ω v : Fin 3 → ℝ) :
    crossProductMatrix ω *ᵥ v = ω ⨯₃ v := by
  funext i
  fin_cases i <;>
    simp [crossProductMatrix, mulVec, dotProduct, Fin.sum_univ_three, cross_apply] <;> ring

/-- The hat map produces skew-symmetric matrices. -/
@[simp]
lemma crossProductMatrix_transpose (ω : Fin 3 → ℝ) :
    (crossProductMatrix ω)ᵀ = - crossProductMatrix ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossProductMatrix]

/-- The vee map: reads the vector off a `3 × 3` matrix. It is a left inverse of the hat map. -/
def crossProductVee (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ := ![A 2 1, A 0 2, A 1 0]

/-- The vee map is a left inverse of the hat map. -/
@[simp]
lemma crossProductVee_crossProductMatrix (ω : Fin 3 → ℝ) :
    crossProductVee (crossProductMatrix ω) = ω := by
  funext i
  fin_cases i <;> simp [crossProductVee, crossProductMatrix]

/-- On skew-symmetric matrices the hat map is also a right inverse of the vee map: if `Aᵀ = -A`
then `[Aᵛ]ₓ = A`. Together with `crossProductVee_crossProductMatrix` this identifies `ℝ³` with the
skew-symmetric `3 × 3` matrices `𝖘𝖔(3)`. -/
lemma crossProductMatrix_crossProductVee {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = -A) :
    crossProductMatrix (crossProductVee A) = A := by
  have h : ∀ i j, A i j = - A j i := fun i j => by
    simpa using congrFun (congrFun hA j) i
  have hdiag : ∀ i, A i i = 0 := fun i => CharZero.eq_neg_self_iff.mp (h i i)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossProductVee, crossProductMatrix] <;>
    first
      | exact (h _ _).symm
      | exact (hdiag _).symm

end Matrix
