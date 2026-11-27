/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.Relativity.SL2C.Cover
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.GellMann.Adjoint
public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.GellMann.SpecialCases
/-!

# The double cover of `SO(3)` by `SU(2)`

The homomorphism from `SU(2)` to `SO(3)`, obtained by restricting `toLorentzGroup`, with kernel
`{1, -1}` and surjective, and its relation to the adjoint action.

## i. Overview

A special unitary matrix is an element of `SL(2, ℂ)` (`ofSpecialUnitary`), and since it is unitary
its image under `toLorentzGroup` fixes the time axis, so it lies in `LorentzGroup.Rotations 3`
(`toLorentzGroup_mem_rotations_of_mem_unitaryGroup`). Composing with the inverse of
`LorentzGroup.ofSpecialOrthogonal` gives the homomorphism `toSpecialOrthogonal` from
`specialUnitaryGroup (Fin 2) ℂ` to `specialOrthogonalGroup (Fin 3) ℝ`. Its kernel is `{1, -1}`,
from `toLorentzGroup_eq_one_iff`, and it is surjective, from `exists_unitary_toLorentzGroup_eq`.

In the Pauli basis of `su(2)`, the Gell-Mann basis reindexed by `GellMannIndex.equivTwo`, the
rotation `toSpecialOrthogonal U` is the matrix `SULieAlgebra.adjointGellMannBasis U` of the
adjoint action `x ↦ U x U†` (`reindex_adjointGellMannBasis`).

Conventions. The spatial indices `0, 1, 2` label `x, y, z`, with `σ_i = pauliMatrix (Sum.inr i)`.
The rotation `R = toSpecialOrthogonal U` has entries `R_ij = re tr (σ_i U σ_j U†) / 2`
(`toSpecialOrthogonal_apply`): the two minus signs of the covariant basis `pauliSelfAdjoint'`
used by `toLorentzGroup` cancel in the spatial block. So `R` is the active rotation with
`U σ_j U† = ∑ i, R_ij σ_i` (`mul_pauliMatrix_mul_star_eq_sum`), its columns being the images of
the Pauli matrices.

## ii. Key results

- `ofSpecialUnitary` : the inclusion of `SU(2)` into `SL(2, ℂ)`.
- `toLorentzGroup_mem_rotations_of_mem_unitaryGroup` : unitary elements map to rotations.
- `toSpecialOrthogonal` : the homomorphism from `SU(2)` to `SO(3)`.
- `toSpecialOrthogonal_apply` : its entries `re tr (σ_i U σ_j U†) / 2`.
- `mul_pauliMatrix_mul_star_eq_sum` : `U σ_j U† = ∑ i, R_ij σ_i`.
- `toSpecialOrthogonal_eq_one_iff` : its kernel is `{1, -1}`.
- `toSpecialOrthogonal_surjective` : it is surjective.
- `reindex_adjointGellMannBasis` : for `SU(2)`, it is the adjoint action in the Pauli basis.

## iii. Table of contents

- A. Unitary elements of `SL(2, ℂ)`
- B. The homomorphism from `SU(2)` to `SO(3)`
- C. The adjoint action in the Gell-Mann basis

## iv. References

## A. Unitary elements of `SL(2, ℂ)`

-/

@[expose] public section

namespace Lorentz

namespace SL2C

open Matrix MatrixGroups Complex PauliMatrix SULieAlgebra

noncomputable section

/-- The inclusion of the special unitary group `SU(2)` into `SL(2, ℂ)`. -/
def ofSpecialUnitary : specialUnitaryGroup (Fin 2) ℂ →* SL(2, ℂ) where
  toFun U := ⟨U.1, (mem_specialUnitaryGroup_iff.mp U.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The underlying matrix of `ofSpecialUnitary U` is that of `U`. -/
@[simp]
lemma ofSpecialUnitary_val (U : specialUnitaryGroup (Fin 2) ℂ) : (ofSpecialUnitary U).1 = U.1 :=
  rfl

/-- The image of a unitary element of `SL(2, ℂ)` in the Lorentz group is a rotation. -/
lemma toLorentzGroup_mem_rotations_of_mem_unitaryGroup (M : SL(2, ℂ))
    (hM : M.1 ∈ unitaryGroup (Fin 2) ℂ) : toLorentzGroup M ∈ LorentzGroup.Rotations 3 := by
  refine ⟨ofReal_injective ?_, toLorentzGroup_det_one M⟩
  rw [toLorentzGroup_eq_trace, ← star_eq_conjTranspose]
  simp [pauliSelfAdjoint', pauliMatrix_inl_zero_eq_one, mem_unitaryGroup_iff.mp hM]

/-!

## B. The homomorphism from `SU(2)` to `SO(3)`

-/

/-- The homomorphism from `SU(2)` to `SO(3)`, the spatial block of `toLorentzGroup`. -/
def toSpecialOrthogonal :
    specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ :=
  LorentzGroup.ofSpecialOrthogonal.symm.toMonoidHom.comp <|
    (toLorentzGroup.comp ofSpecialUnitary).codRestrict _ fun U =>
      toLorentzGroup_mem_rotations_of_mem_unitaryGroup _ (mem_specialUnitaryGroup_iff.mp U.2).1

/-- The entries of `toSpecialOrthogonal U` are the spatial entries of `toLorentzGroup`. -/
lemma toSpecialOrthogonal_val_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    (toSpecialOrthogonal U).1 i j =
      (toLorentzGroup (ofSpecialUnitary U)).1 (Sum.inr i) (Sum.inr j) :=
  rfl

/-- The entries of `toSpecialOrthogonal U` are `re tr (σ_i U σ_j U†) / 2`. -/
lemma toSpecialOrthogonal_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    (toSpecialOrthogonal U).1 i j =
      (pauliMatrix (Sum.inr i) * (U.1 * pauliMatrix (Sum.inr j) * star U.1)).trace.re / 2 := by
  have h := congrArg re (toLorentzGroup_eq_trace (ofSpecialUnitary U) (Sum.inr i) (Sum.inr j))
  rw [ofReal_re] at h
  rw [toSpecialOrthogonal_val_apply, h, star_eq_conjTranspose]
  fin_cases i <;> fin_cases j <;> simp [pauliSelfAdjoint']

/-- Conjugation by `U` rotates the Pauli matrices actively, `U σ_j U† = ∑ i, R_ij σ_i` with
`R = toSpecialOrthogonal U`. -/
lemma mul_pauliMatrix_mul_star_eq_sum (U : specialUnitaryGroup (Fin 2) ℂ) (j : Fin 3) :
    U.1 * pauliMatrix (Sum.inr j) * star U.1 =
      ∑ i, ((toSpecialOrthogonal U).1 i j : ℂ) • pauliMatrix (Sum.inr i) := by
  have hΛ : (toLorentzGroup (ofSpecialUnitary U)).1 =
      (LorentzGroup.ofSpecialOrthogonal (toSpecialOrthogonal U)).1.1 := by
    rw [toSpecialOrthogonal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    rfl
  have h := congrArg Subtype.val (toSelfAdjointMap_basis (M := ofSpecialUnitary U) (Sum.inr j))
  simp only [toSpecialOrthogonal_val_apply, hΛ, Fin.sum_univ_three, star_eq_conjTranspose]
  fin_cases j <;> simp [hΛ, pauliBasis', Fintype.sum_sum_type, Fin.sum_univ_three,
    pauliSelfAdjoint', LorentzGroup.ofSpecialOrthogonal] at h ⊢ <;>
    rw [← neg_inj, h] <;> simp [← Complex.coe_smul] <;> abel

/-- The kernel of `toSpecialOrthogonal` is `{1, -1}`. -/
lemma toSpecialOrthogonal_eq_one_iff (U : specialUnitaryGroup (Fin 2) ℂ) :
    toSpecialOrthogonal U = 1 ↔ U.1 = 1 ∨ U.1 = -1 := by
  rw [← ofSpecialUnitary_val, ← toLorentzGroup_eq_one_iff, toSpecialOrthogonal,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq, map_one,
    Subtype.ext_iff]
  rfl

/-- The homomorphism `toSpecialOrthogonal` is surjective. -/
lemma toSpecialOrthogonal_surjective : Function.Surjective toSpecialOrthogonal := fun R => by
  obtain ⟨M, hM, hR⟩ := exists_unitary_toLorentzGroup_eq (LorentzGroup.ofSpecialOrthogonal R)
  refine ⟨⟨M.1, mem_specialUnitaryGroup_iff.mpr ⟨hM, M.2⟩⟩, ?_⟩
  rw [toSpecialOrthogonal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_eq]
  exact Subtype.ext hR

/-!

## C. The adjoint action in the Gell-Mann basis

-/

/-- For `SU(2)`, the matrix of the adjoint action in the Gell-Mann basis, reindexed by
`GellMannIndex.equivTwo`, is `toSpecialOrthogonal`. -/
lemma reindex_adjointGellMannBasis (U : specialUnitaryGroup (Fin 2) ℂ) :
    reindex GellMannIndex.equivTwo GellMannIndex.equivTwo (adjointGellMannBasis U) =
      (toSpecialOrthogonal U).1 := by
  ext i j
  rw [reindex_apply, submatrix_apply, adjointGellMannBasis_apply, gellMannMatrices_two,
    gellMannMatrices_two, toSpecialOrthogonal_apply]

end
end SL2C
end Lorentz
