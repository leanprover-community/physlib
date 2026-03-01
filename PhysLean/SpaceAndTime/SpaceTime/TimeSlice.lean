/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.Derivatives
import PhysLean.SpaceAndTime.TimeAndSpace.Basic
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Mathematics.FDerivCurry
/-!
# Time slice

Time slicing functions on spacetime, turning them into a function
`Time → Space d → M`.

This is useful when going from relativistic physics (defined using `SpaceTime`)
to non-relativistic physics (defined using `Space` and `Time`).

-/

noncomputable section

namespace SpaceTime

open Time
open Space

/-- The timeslice of a function `SpaceTime d → M` forming a function
  `Time → Space d → M`. -/
def timeSlice {d : ℕ} {M : Type} (c : SpeedOfLight := 1) :
    (SpaceTime d → M) ≃ (Time → Space d → M) where
  toFun f := Function.curry (f ∘ (toTimeAndSpace c).symm)
  invFun f := Function.uncurry f ∘ toTimeAndSpace c
  left_inv f := by
    funext x
    simp
  right_inv f := by
    funext x t
    simp

lemma timeSlice_contDiff {d : ℕ} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M]
    {n} (c : SpeedOfLight) (f : SpaceTime d → M) (h : ContDiff ℝ n f) :
    ContDiff ℝ n ↿(timeSlice c f) := by
  change ContDiff ℝ n (f ∘ (toTimeAndSpace c).symm)
  apply ContDiff.comp
  · exact h
  · exact ContinuousLinearEquiv.contDiff (toTimeAndSpace c).symm

lemma timeSlice_differentiable {d : ℕ} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (c : SpeedOfLight)
    (f : SpaceTime d → M) (h : Differentiable ℝ f) :
    Differentiable ℝ ↿(timeSlice c f) := by
  change Differentiable ℝ (f ∘ (toTimeAndSpace c).symm)
  apply Differentiable.comp
  · exact h
  · exact ContinuousLinearEquiv.differentiable (toTimeAndSpace c).symm

/-- The timeslice of a function `SpaceTime d → M` forming a function
  `Time → Space d → M`, as a linear equivalence. -/
def timeSliceLinearEquiv {d : ℕ} {M : Type} [AddCommGroup M] [Module ℝ M]
    (c : SpeedOfLight := 1) :
    (SpaceTime d → M) ≃ₗ[ℝ] (Time → Space d → M) where
  toFun := timeSlice c
  invFun := (timeSlice c).symm
  map_add' f g := by
    ext t x
    simp [timeSlice]
  map_smul' := by
    intros c f
    ext t x
    simp [timeSlice]
  left_inv f := by simp
  right_inv f := by simp

lemma timeSliceLinearEquiv_apply {d : ℕ} {M : Type} [AddCommGroup M] [Module ℝ M]
    (c : SpeedOfLight) (f : SpaceTime d → M) : timeSliceLinearEquiv c f = timeSlice c f := by
  simp [timeSliceLinearEquiv, timeSlice]

lemma timeSliceLinearEquiv_symm_apply {d : ℕ} {M : Type} [AddCommGroup M] [Module ℝ M]
    (c : SpeedOfLight) (f : Time → Space d → M) :
    (timeSliceLinearEquiv c).symm f = (timeSlice c).symm f := by
  simp [timeSliceLinearEquiv, timeSlice]

/-!

## B. Time slices of distributions

-/
open Distribution SchwartzMap

/-- The time slice of a distribution on `SpaceTime d` to form a distribution
  on `Time × Space d`. -/
noncomputable def distTimeSlice {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : SpeedOfLight := 1) :
    ((SpaceTime d) →d[ℝ] M) ≃L[ℝ] ((Time × Space d) →d[ℝ] M) where
  toFun f :=
    f ∘L compCLMOfContinuousLinearEquiv (F := ℝ) ℝ (SpaceTime.toTimeAndSpace c (d := d))
  invFun f := f ∘L compCLMOfContinuousLinearEquiv
      (F := ℝ) ℝ (SpaceTime.toTimeAndSpace c (d := d)).symm
  left_inv f := by
    ext κ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    congr
    ext x
    simp [compCLMOfContinuousLinearEquiv_apply]
  right_inv f := by
    ext κ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    congr
    ext x
    simp
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp
  continuous_toFun := ((compCLMOfContinuousLinearEquiv ℝ (toTimeAndSpace c)).precomp M).continuous
  continuous_invFun :=
    ((compCLMOfContinuousLinearEquiv ℝ (toTimeAndSpace c).symm).precomp M).continuous

lemma distTimeSlice_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : SpeedOfLight) (f : (SpaceTime d) →d[ℝ] M)
    (κ : 𝓢(Time × Space d, ℝ)) : distTimeSlice c f κ =
    f (compCLMOfContinuousLinearEquiv ℝ (toTimeAndSpace c) κ) := by rfl

lemma distTimeSlice_symm_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : SpeedOfLight) (f : (Time × (Space d)) →d[ℝ] M)
    (κ : 𝓢(SpaceTime d, ℝ)) : (distTimeSlice c).symm f κ =
    f (compCLMOfContinuousLinearEquiv ℝ (toTimeAndSpace c).symm κ) := by rfl

/-!

### B.1. Time slices and derivatives

-/

lemma distTimeSlice_distDeriv_inl {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {c : SpeedOfLight}
    (f : (SpaceTime d) →d[ℝ] M) :
    distTimeSlice c (distDeriv (Sum.inl 0) f) =
    (1/c.val) • Space.distTimeDeriv (distTimeSlice c f) := by
  ext κ
  rw [distTimeSlice_apply, distDeriv_apply, fderivD_apply]
  simp only [Fin.isValue, one_div, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [distTimeDeriv_apply, fderivD_apply, distTimeSlice_apply]
  simp only [Fin.isValue, smul_neg, neg_inj]
  rw [← map_smul]
  congr
  ext x
  change fderiv ℝ (κ ∘ toTimeAndSpace c) x (Lorentz.Vector.basis (Sum.inl 0)) =
    c.val⁻¹ • fderiv ℝ κ (toTimeAndSpace c x) (1, 0)
  rw [fderiv_comp]
  simp only [toTimeAndSpace_fderiv, Fin.isValue, ContinuousLinearMap.coe_comp',
    ContinuousLinearEquiv.coe_coe, Function.comp_apply, smul_eq_mul]
  rw [toTimeAndSpace_basis_inl']
  rw [map_smul]
  simp only [one_div, smul_eq_mul]
  · apply Differentiable.differentiableAt
    exact SchwartzMap.differentiable κ
  · fun_prop

lemma distDeriv_inl_distTimeSlice_symm {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {c : SpeedOfLight}
    (f : (Time × Space d) →d[ℝ] M) :
    distDeriv (Sum.inl 0) ((distTimeSlice c).symm f) =
    (1/c.val) • (distTimeSlice c).symm (Space.distTimeDeriv f) := by
  obtain ⟨f, rfl⟩ := (distTimeSlice c).surjective f
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  apply (distTimeSlice c).injective
  simp only [Fin.isValue, one_div, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  rw [distTimeSlice_distDeriv_inl]
  simp

lemma distTimeSlice_symm_distTimeDeriv_eq {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {c : SpeedOfLight}
    (f : (Time × Space d) →d[ℝ] M) :
    (distTimeSlice c).symm (Space.distTimeDeriv f) =
    c.val • distDeriv (Sum.inl 0) ((distTimeSlice c).symm f) := by
  rw [distDeriv_inl_distTimeSlice_symm]
  simp

lemma distTimeSlice_distDeriv_inr {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {c : SpeedOfLight}
    (i : Fin d) (f : (SpaceTime d) →d[ℝ] M) :
    distTimeSlice c (distDeriv (Sum.inr i) f) =
    Space.distSpaceDeriv i (distTimeSlice c f) := by
  ext κ
  rw [distTimeSlice_apply, distDeriv_apply, fderivD_apply]
  rw [distSpaceDeriv_apply, fderivD_apply, distTimeSlice_apply]
  simp only [neg_inj]
  congr 1
  ext x
  change fderiv ℝ (κ ∘ toTimeAndSpace c) x (Lorentz.Vector.basis (Sum.inr i)) =
    fderiv ℝ κ (toTimeAndSpace c x) (0, Space.basis i)
  rw [fderiv_comp]
  simp only [toTimeAndSpace_fderiv, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    Function.comp_apply]
  rw [toTimeAndSpace_basis_inr]
  · apply Differentiable.differentiableAt
    exact SchwartzMap.differentiable κ
  · fun_prop

lemma distDeriv_inr_distTimeSlice_symm {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {c : SpeedOfLight}
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M) :
    distDeriv (Sum.inr i) ((distTimeSlice c).symm f) =
    (distTimeSlice c).symm (Space.distSpaceDeriv i f) := by
  obtain ⟨f, rfl⟩ := (distTimeSlice c).surjective f
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  apply (distTimeSlice c).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [distTimeSlice_distDeriv_inr]

end SpaceTime

end
