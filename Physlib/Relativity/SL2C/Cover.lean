/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.Relativity.SL2C.CayleyKlein
public import Physlib.Relativity.LorentzGroup.Restricted.FromBoostRotation
public import Physlib.Mathematics.Groups.SO3.Basic
/-!
# `SL(2, ℂ)` is a double cover of the restricted Lorentz group

## i. Overview

The homomorphism `toRestrictedLorentzGroup` from `SL(2, ℂ)` to the restricted Lorentz group is
surjective; together with the kernel `{1, -1}` (`toLorentzGroup_eq_one_iff`), this makes
`SL(2, ℂ)` a double cover. Rotations come from the unitary elements, written with
their Cayley–Klein parameters `a b`; the time axis is moved to any velocity by a lower
triangular element. The proof follows the boost and rotation decomposition
`LorentzGroup.exists_boost_mul_rotation`.

## ii. Key results

- `exists_unitary_toLorentzGroup_eq` : every rotation is the image of a unitary element.
- `toRestrictedLorentzGroup_surjective` : the homomorphism to the restricted Lorentz group is
  surjective.

## iii. Table of contents

- A. Rotations
- B. Boosts and surjectivity

## iv. References

* B. Oblak, *From the Lorentz Group to the Celestial Sphere*, arXiv:1508.00920,
  Section 2.3.2.

-/

@[expose] public section

namespace Lorentz

namespace SL2C

open Matrix MatrixGroups Complex PauliMatrix

noncomputable section

/-!

## A. Rotations

-/

/-- Every rotation is the image of a unitary element of `SL(2, ℂ)`. -/
lemma exists_unitary_toLorentzGroup_eq (Λ : LorentzGroup.Rotations 3) :
    ∃ M : SL(2, ℂ), M.1 ∈ unitaryGroup (Fin 2) ℂ ∧ toLorentzGroup M = Λ := by
  open LorentzGroup in
  set A := ofSpecialOrthogonal.symm Λ
  have hA := (Matrix.mem_orthogonalGroup_iff' (A := A.1)).mp
    (mem_specialOrthogonalGroup_iff.mp A.2).1
  have hn : A.1 0 2 ^ 2 + A.1 1 2 ^ 2 + A.1 2 2 ^ 2 = 1 := by
    have := congrFun (congrFun hA 2) 2
    simp only [mul_apply, transpose_apply, Fin.sum_univ_three, one_apply_eq] at this
    linarith
  obtain ⟨a, b, h, hab⟩ := exists_cayleyKleinRotation_apply_two (fun i => A.1 i 2) hn
  set B := (ofSpecialOrthogonal (d := 3)).symm (cayleyKleinRotation a b h)
  have hab' : ∀ i, B.1 i 2 = A.1 i 2 := fun i => hab i
  have hB' := (Matrix.mem_orthogonalGroup_iff' (A := B.1)).mp
    (mem_specialOrthogonalGroup_iff.mp B.2).1
  set C := B⁻¹ * A
  have hC : ∀ i, C.1 i 2 = if i = 2 then 1 else 0 := fun i => by
    have := congrFun (congrFun hB' i) 2
    simp only [mul_apply, transpose_apply, Fin.sum_univ_three, one_apply] at this ⊢
    rw [← this]
    change (star B.1 * A.1) i 2 = _
    simp only [mul_apply, star_apply, star_trivial, Fin.sum_univ_three, ← hab']
  have hC' : C.1 = !![C.1 0 0, C.1 0 1, 0; -C.1 0 1, C.1 0 0, 0; 0, 0, 1] :=
    GroupTheory.SO3.eq_of_apply_two
      ⟨C.1, (mem_specialOrthogonalGroup_iff.mp C.2).2,
        (Matrix.mem_orthogonalGroup_iff _ _).mp (mem_specialOrthogonalGroup_iff.mp C.2).1⟩ hC
  have hcs : C.1 0 0 ^ 2 + C.1 0 1 ^ 2 = 1 := by
    have h1 := (Matrix.mem_orthogonalGroup_iff' (A := C.1)).mp
      (mem_specialOrthogonalGroup_iff.mp C.2).1
    rw [hC'] at h1
    have := congrFun (congrFun h1 0) 0
    simp [mul_apply, Fin.sum_univ_three] at this
    linarith
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (⟨C.1 0 0, C.1 0 1⟩ : ℂ) two_pos
  have hw1 : normSq w = 1 := by
    have h1 := congrArg normSq hw
    rw [map_pow, normSq_mk (C.1 0 0)] at h1
    exact (pow_eq_one_iff_of_nonneg (normSq_nonneg w) two_ne_zero).mp (by nlinarith)
  have hV : (ofSpecialOrthogonal (d := 3)).symm
      (cayleyKleinRotation w 0 (by simpa using hw1)) = C := by
    apply Subtype.ext
    rw [hC']
    ext i j
    change (cayleyKleinRotation w 0 _).1.1 (Sum.inr i) (Sum.inr j) = _
    rw [cayleyKleinRotation_inr_inr]
    fin_cases i <;> fin_cases j <;> simp [hw, hw1]
  refine ⟨cayleyKlein a b h * cayleyKlein w 0 (by simpa using hw1),
    Submonoid.mul_mem _ (cayleyKlein_mem_unitaryGroup ..) (cayleyKlein_mem_unitaryGroup ..), ?_⟩
  have hΛ : Λ = ofSpecialOrthogonal B * ofSpecialOrthogonal C := by
    rw [← map_mul, mul_inv_cancel_left, MulEquiv.apply_symm_apply]
  rw [map_mul, hΛ, Subgroup.coe_mul, ← hV, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  rfl

/-!

## B. Boosts and surjectivity

-/

/-- Every velocity is the image of the time axis under some element of `SL(2, ℂ)`. -/
lemma exists_toVector_toLorentzGroup_eq (u : Velocity 3) :
    ∃ M : SL(2, ℂ), LorentzGroup.toVector (toLorentzGroup M) = u.1 := by
  obtain ⟨hu, h0⟩ := Velocity.mem_iff.mp u.2
  rw [Vector.minkowskiProduct_toCoord, Fin.sum_univ_three] at hu
  have hz : 0 < u.1 (Sum.inl 0) - u.1 (Sum.inr 2) := by
    simp only [Vector.timeComponent] at h0
    nlinarith
  set x := √(u.1 (Sum.inl 0) - u.1 (Sum.inr 2))
  have hx : x ^ 2 = u.1 (Sum.inl 0) - u.1 (Sum.inr 2) := Real.sq_sqrt hz.le
  have hx0 : 0 < x := Real.sqrt_pos.mpr hz
  let M : SL(2, ℂ) := ⟨!![(x : ℂ), 0; ⟨-u.1 (Sum.inr 0) / x, -u.1 (Sum.inr 1) / x⟩, (x : ℂ)⁻¹],
    by rw [det_fin_two_of]; field_simp; simp [hx0.ne']⟩
  refine ⟨M, ?_⟩
  rw [LorentzGroup.toVector_eq_fun]
  funext μ
  refine (congrFun (toLorentzGroup_fst_col M) μ).trans ?_
  rcases μ with μ | μ <;> fin_cases μ <;>
    simp [M, Complex.sq_norm, normSq_mk] <;> field_simp <;> nlinarith

/-- The homomorphism from `SL(2, ℂ)` to the restricted Lorentz group is surjective. -/
lemma toRestrictedLorentzGroup_surjective : Function.Surjective toRestrictedLorentzGroup := by
  intro Λ
  obtain ⟨M, hM⟩ := exists_toVector_toLorentzGroup_eq (LorentzGroup.toVelocity Λ)
  have hR : (toLorentzGroup M)⁻¹ * Λ ∈ LorentzGroup.Rotations 3 := by
    refine ⟨?_, ?_⟩
    · rw [← LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one, LorentzGroup.toVector_mul]
      change _ • (LorentzGroup.toVelocity Λ).1 = _
      rw [← hM, ← LorentzGroup.toVector_mul, inv_mul_cancel,
        LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one]
      simp
    · rw [← map_inv]
      exact LorentzGroup.isProper_mul (toLorentzGroup_det_one _) Λ.2.1
  obtain ⟨N, -, hN⟩ := exists_unitary_toLorentzGroup_eq ⟨_, hR⟩
  refine ⟨M * N, Subtype.ext ?_⟩
  change toLorentzGroup (M * N) = Λ
  rw [map_mul, hN, mul_inv_cancel_left]

end

end SL2C

end Lorentz
