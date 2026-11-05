/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.Relativity.SL2C.ToSpecialOrthogonal

/-!

# The homomorphism from `U(2)` to `SO(3)`

The homomorphism from `U(2)` to `SO(3)` by conjugation, with kernel the scalars, and surjective.

## i. Overview

For `U(2)`, the conjugation representation `SULieAlgebra.conj` on the traceless hermitian
matrices has, in the Pauli basis (the Gell-Mann basis reindexed by `GellMannIndex.equivTwo`), the
matrix `unitaryToSpecialOrthogonal U`. Every unitary `U` is `w V` with `V ∈ SU(2)` and `|w| = 1`
(`exists_smul_specialUnitary`, `w² = det U`), and the phase `w` drops out of the conjugation. So
the matrix is `toSpecialOrthogonal V`, which shows that it lies in `SO(3)`. The homomorphism
restricts to `toSpecialOrthogonal` on `SU(2)`, its kernel consists of the scalar unitaries, and
it is surjective.

The conventions are those of `toSpecialOrthogonal`.

## ii. Key results

- `unitaryToSpecialOrthogonal` : the homomorphism from `U(2)` to `SO(3)`, by conjugation.
- `unitaryToSpecialOrthogonal_comp_inclusion` : its restriction to `SU(2)`.
- `unitaryToSpecialOrthogonal_eq_one_iff` : its kernel consists of the scalars.
- `unitaryToSpecialOrthogonal_surjective` : it is surjective.

## iii. Table of contents

- A. The homomorphism from `U(2)` to `SO(3)`

## iv. References

## A. The homomorphism from `U(2)` to `SO(3)`

-/

@[expose] public section

namespace Lorentz

namespace SL2C

open Matrix MatrixGroups Complex PauliMatrix SULieAlgebra

noncomputable section

/-- The entries of the matrix of the conjugation `x ↦ U x U†` in the Pauli basis of `su(2)` are
`re tr (σ_i U σ_j U†) / 2`. -/
lemma toMatrix_conj_apply (U : unitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    LinearMap.toMatrixAlgEquiv (gellMannBasis.reindex GellMannIndex.equivTwo) (conj U) i j =
      (pauliMatrix (Sum.inr i) * (U.1 * pauliMatrix (Sum.inr j) * star U.1)).trace.re / 2 := by
  rw [LinearMap.toMatrixAlgEquiv_apply, Module.Basis.repr_reindex_apply,
    Module.Basis.reindex_apply, gellMannBasis_repr_apply, adjointContr_tmul, gellMannBasis_apply,
    val_conj_apply, gellMannMatrices_two, gellMannMatrices_two]

/-- Every unitary `2 × 2` matrix is a phase `w` times a special unitary matrix, with
`w² = det U`. -/
lemma exists_smul_specialUnitary (U : unitaryGroup (Fin 2) ℂ) :
    ∃ w : ℂ, ∃ V : specialUnitaryGroup (Fin 2) ℂ, normSq w = 1 ∧ U.1 = w • V.1 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq U.1.det two_pos
  have hdet : normSq U.1.det = 1 := by
    have h := congrArg det (mem_unitaryGroup_iff.mp U.2)
    rw [det_mul, star_eq_conjTranspose, det_conjTranspose, det_one, star_def, mul_conj] at h
    exact_mod_cast h
  have hw1 : normSq w = 1 := by
    have h := congrArg normSq hw
    rw [map_pow, hdet] at h
    exact (pow_eq_one_iff_of_nonneg (normSq_nonneg w) two_ne_zero).mp h
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  have hww : w * star w = 1 := by rw [star_def, mul_conj, hw1, ofReal_one]
  refine ⟨w, ⟨w⁻¹ • U.1, ?_⟩, hw1, ?_⟩
  · rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, det_smul, ← hw]
    refine ⟨?_, by simp [hw0]⟩
    rw [star_smul, smul_mul_smul, mem_unitaryGroup_iff.mp U.2, star_inv₀, ← mul_inv, hww,
      inv_one, one_smul]
  · simp [smul_smul, hw0]

/-- The phase drops out of the conjugation: if `U = w V` with `|w| = 1` and `V ∈ SU(2)`, the
matrix of the conjugation by `U` is `toSpecialOrthogonal V`. -/
lemma toMatrix_conj_eq_of_eq_smul (U : unitaryGroup (Fin 2) ℂ) (w : ℂ)
    (V : specialUnitaryGroup (Fin 2) ℂ) (hw : normSq w = 1) (hU : U.1 = w • V.1) :
    LinearMap.toMatrixAlgEquiv (gellMannBasis.reindex GellMannIndex.equivTwo) (conj U) =
      (toSpecialOrthogonal V).1 := by
  have hww : w * star w = 1 := by rw [star_def, mul_conj, hw, ofReal_one]
  ext i j
  rw [toMatrix_conj_apply, toSpecialOrthogonal_apply, hU, star_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (star w), hww, one_smul]

/-- The matrix of the conjugation by a unitary matrix is a rotation. -/
lemma toMatrix_conj_mem_specialOrthogonalGroup (U : unitaryGroup (Fin 2) ℂ) :
    LinearMap.toMatrixAlgEquiv (gellMannBasis.reindex GellMannIndex.equivTwo) (conj U) ∈
      specialOrthogonalGroup (Fin 3) ℝ := by
  obtain ⟨w, V, hw, hU⟩ := exists_smul_specialUnitary U
  rw [toMatrix_conj_eq_of_eq_smul U w V hw hU]
  exact (toSpecialOrthogonal V).2

/-- The homomorphism from `U(2)` to `SO(3)`: the matrix of the conjugation `x ↦ U x U†` on the
traceless hermitian matrices in the Pauli basis. -/
def unitaryToSpecialOrthogonal : unitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ :=
  ((MonoidHom.ofClass (LinearMap.toMatrixAlgEquiv
    (gellMannBasis.reindex GellMannIndex.equivTwo))).comp conj).codRestrict _
      toMatrix_conj_mem_specialOrthogonalGroup

/-- The matrix `unitaryToSpecialOrthogonal U` is the matrix of `SULieAlgebra.conj U` in the
Pauli basis. -/
lemma unitaryToSpecialOrthogonal_val (U : unitaryGroup (Fin 2) ℂ) :
    (unitaryToSpecialOrthogonal U).1 =
      LinearMap.toMatrix (gellMannBasis.reindex GellMannIndex.equivTwo)
        (gellMannBasis.reindex GellMannIndex.equivTwo) (conj U) :=
  rfl

/-- On `SU(2)`, the homomorphism `unitaryToSpecialOrthogonal` is `toSpecialOrthogonal`. -/
lemma unitaryToSpecialOrthogonal_comp_inclusion :
    unitaryToSpecialOrthogonal.comp (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup) =
      toSpecialOrthogonal :=
  MonoidHom.ext fun V => Subtype.ext <| toMatrix_conj_eq_of_eq_smul _ 1 V (by simp) (by simp)

/-- The kernel of `unitaryToSpecialOrthogonal` consists of the scalar unitary matrices. -/
lemma unitaryToSpecialOrthogonal_eq_one_iff (U : unitaryGroup (Fin 2) ℂ) :
    unitaryToSpecialOrthogonal U = 1 ↔ ∃ c : ℂ, U.1 = c • 1 := by
  constructor
  · obtain ⟨w, V, hw, hU⟩ := exists_smul_specialUnitary U
    have h : unitaryToSpecialOrthogonal U = toSpecialOrthogonal V :=
      Subtype.ext (toMatrix_conj_eq_of_eq_smul U w V hw hU)
    rw [h, toSpecialOrthogonal_eq_one_iff]
    rintro (hV | hV)
    · exact ⟨w, by rw [hU, hV]⟩
    · exact ⟨-w, by rw [hU, hV, smul_neg, neg_smul]⟩
  · rintro ⟨c, hc⟩
    have h := congrFun (congrFun (mem_unitaryGroup_iff.mp U.2) 0) 0
    rw [hc, star_smul, star_one, smul_mul_smul, mul_one, Matrix.smul_apply, one_apply_eq,
      smul_eq_mul, mul_one, star_def, mul_conj] at h
    refine Subtype.ext ((toMatrix_conj_eq_of_eq_smul U c 1 (by exact_mod_cast h)
      (by simpa using hc)).trans ?_)
    rw [map_one]

/-- The homomorphism `unitaryToSpecialOrthogonal` is surjective. -/
lemma unitaryToSpecialOrthogonal_surjective : Function.Surjective unitaryToSpecialOrthogonal :=
  fun R => by
    obtain ⟨V, rfl⟩ := toSpecialOrthogonal_surjective R
    exact ⟨_, congrArg (· V) unitaryToSpecialOrthogonal_comp_inclusion⟩

end

end SL2C

end Lorentz
