/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
/-!
# The adjoint matrices of `SU(2)` and `SU(3)`

`su2AdjointMatrix U` and `su3AdjointMatrix U` are the real matrices of `X ↦ U X U⁻¹` on
`su(2)` and `su(3)` in the Pauli and Gell-Mann bases, read off with the trace pairing
`(X, Y) ↦ ½ tr (X Y)`. They are the `su(2)` and `su(3)` blocks of `GaugeAlgebra.adjointMatrix`,
which gives their orthonormal rows and their transposition at `U⁻¹`.

- A. The adjoint matrix of `SU(2)`
- B. The adjoint matrix of `SU(3)`
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The adjoint matrix of `SU(2)`

-/

open PauliMatrix in
/-- The adjoint matrix of an element of `SU(2)`: the trace pairing of the Pauli basis of
  `su(2)` with the Pauli basis conjugated by that element. -/
noncomputable def su2AdjointMatrix (U : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
      (U.1 * pauliMatrix (Sum.inr j) * star U.1))).re

open PauliMatrix in
/-- The entries of the adjoint matrix. -/
@[simp]
lemma su2AdjointMatrix_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    su2AdjointMatrix U i j
      = 2⁻¹ * (Matrix.trace (pauliMatrix (Sum.inr i) *
          (U.1 * pauliMatrix (Sum.inr j) * star U.1))).re := rfl

/-- The rows of the adjoint matrix are orthonormal. -/
lemma sum_su2AdjointMatrix_row_mul (U : specialUnitaryGroup (Fin 2) ℂ) (c d : Fin 3) :
    ∑ a : Fin 3, su2AdjointMatrix U c a * su2AdjointMatrix U d a
      = if c = d then 1 else 0 :=
  GaugeAlgebra.sum_adjointMatrix_inr_inl_row_mul (1, U, 1) c d

/-- The adjoint matrix of the inverse is the transpose. -/
lemma su2AdjointMatrix_inv (U : specialUnitaryGroup (Fin 2) ℂ) (a b : Fin 3) :
    su2AdjointMatrix U⁻¹ a b = su2AdjointMatrix U b a := by
  have h := GaugeAlgebra.adjointMatrix_inv_apply (1, U, 1) (Sum.inr (Sum.inl a))
    (Sum.inr (Sum.inl b))
  rwa [show ((1, U, 1) : GaugeGroupI)⁻¹ = (1, U⁻¹, 1) from by simp] at h

/-!

## B. The adjoint matrix of `SU(3)`

-/

/-- The adjoint matrix of `U ∈ SU(3)`: the trace pairing of the Gell-Mann basis with the
  Gell-Mann basis conjugated by `U`. -/
noncomputable def su3AdjointMatrix (U : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j =>
    2⁻¹ * (Matrix.trace (gellMannMatrix i * (U.1 * gellMannMatrix j * star U.1))).re

@[simp]
lemma su3AdjointMatrix_apply (U : specialUnitaryGroup (Fin 3) ℂ) (i j : Fin 8) :
    su3AdjointMatrix U i j
      = 2⁻¹ * (Matrix.trace (gellMannMatrix i * (U.1 * gellMannMatrix j * star U.1))).re :=
  rfl

/-- The rows of the adjoint matrix are orthonormal. -/
lemma sum_su3AdjointMatrix_row_mul (U : specialUnitaryGroup (Fin 3) ℂ) (c d : Fin 8) :
    ∑ a : Fin 8, su3AdjointMatrix U c a * su3AdjointMatrix U d a
      = if c = d then 1 else 0 :=
  GaugeAlgebra.sum_adjointMatrix_inl_row_mul (U, 1, 1) c d

/-- The adjoint matrix of the inverse is the transpose. -/
lemma su3AdjointMatrix_inv (U : specialUnitaryGroup (Fin 3) ℂ) (a b : Fin 8) :
    su3AdjointMatrix U⁻¹ a b = su3AdjointMatrix U b a := by
  have h := GaugeAlgebra.adjointMatrix_inv_apply (U, 1, 1) (Sum.inl a) (Sum.inl b)
  rwa [show ((U, 1, 1) : GaugeGroupI)⁻¹ = (U⁻¹, 1, 1) from by simp] at h

end StandardModel
