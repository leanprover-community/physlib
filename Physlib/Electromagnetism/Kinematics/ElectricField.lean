/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.ScalarPotential
public import Physlib.Electromagnetism.Kinematics.FieldStrength
public import Physlib.Electromagnetism.Basic
/-!

# The Electric Field

## i. Overview

The electric field is defined in terms of the electromagnetic potential `A` as
`E = - ∇ φ - ∂ₜ \vec A`.

In this module we define the electric field, and prove lemmas about it.

## ii. Key results

- `electricField` : The electric field from the electromagnetic potential.
- `electricField_eq_toFieldStrength_eval` : The electric field expressed in terms of the
  components of the field strength tensor.

## iii. Table of contents

- A. Definition of the Electric Field
- B. Relation to the field strength tensor
- C. Smoothness of the electric field
- D. Differentiability of the electric field
- E. Time derivative of the vector potential in terms of the electric field
- F. Derivatives of the electric field in terms of field strength tensor

## iv. References

* None.
-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

open Space Time

/-!

## A. Definition of the Electric Field

-/

/-- The electric field from the electromagnetic potential. -/
noncomputable def electricField {d} (c : SpeedOfLight := 1)
    (A : ElectromagneticPotential d) : ElectricField d :=
  fun t x => - ∇ (A.scalarPotential c t) x - ∂ₜ (fun t => A.vectorPotential c t x) t

lemma electricField_eq {c : SpeedOfLight} (A : ElectromagneticPotential d) :
    A.electricField c = fun t x =>
      - ∇ (A.scalarPotential c t) x - ∂ₜ (fun t => A.vectorPotential c t x) t := rfl

/-!

## B. Relation to constructors

-/

open MeasureTheory Matrix Space InnerProductSpace Time in
/-- The electric field of the electromagnetic potential created from the electric field
  `E` and the magnetic field `B` is `E`, as long as Gauss's law for magnetism and
  Faraday's law are satisfied. -/
lemma ofElectromagneticField_electricField {c : SpeedOfLight}
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (E_contDiff : ContDiff ℝ 1 ↿E) (B_contDiff : ContDiff ℝ 2 ↿B)
    (B_grad : ∀ t, ∇ ⬝ (B t) = 0) (faraday : ∀ t x, curl (E t) x = - ∂ₜ (B · x) t) :
    (ofElectromagneticField c E B).electricField c = E := by
  have h0 := B_contDiff.of_le (m := 1) (by simp)
  ext1 t
  ext1 x
  suffices h : E t x + ∂ₜ (fun t => (ofElectromagneticField c E B).vectorPotential c t x) t =
      - ∇ ((ofElectromagneticField c E B).scalarPotential c t) x by
    simp only [electricField]
    rw [sub_eq_iff_eq_add', ← h, add_comm]
  convert congrFun (eq_grad_integral_of_curl_zero (fun x => E t x +
      ∂ₜ (fun t => (ofElectromagneticField c E B).vectorPotential c t x) t) ?_ ?_) x
  · simp [ofElectromagneticField_scalarPotential_eq_add_vectorPotential _ _ B (by fun_prop)]
    rw [fun_grad_neg]
    simp
  · simp only [Time.deriv]
    fun_prop
  · rw [fun_curl_add]
    ext1 x
    simp [faraday]
    suffices h : ∂ₜ (B · x) t = curl (fun x =>
        ∂ₜ ((ofElectromagneticField c E B).vectorPotential c · x) t) x by
      simp [h]
    rw [← Space.time_deriv_curl_commute]
    · congr
      funext t
      have h1 := eq_neg_curl_of_div_zero (B t) (by fun_prop) (B_grad t)
      conv_lhs => rw [h1]
      simp only [ofElectromagneticField_vectorPotential]
      rw [fun_curl_neg]
      simp only [WithLp.equiv_apply, WithLp.ofLp_smul, map_smul, LinearMap.smul_apply,
        WithLp.equiv_symm_apply, WithLp.toLp_smul, Pi.neg_apply]
      intro x
      apply Differentiable.differentiableAt
      apply ContDiff.differentiable (n := 1) _ (by simp)
      apply contDiff_parametric_intervalIntegral_of_contDiff
      refine contDiff_euclidean.mpr ?_
      intro i
      let C : (Space) × ℝ → EuclideanSpace ℝ (Fin 3) := fun p =>
        let x:= p.1
        let u := p.2
        (u • basis.repr x) ⨯ₑ₃ B t (u • x)
      suffices h : ContDiff ℝ 1 (fun x => C x i) by
        convert! h
        exact 1
      fin_cases i
      all_goals
      · simp [C, crossProduct]
        fun_prop
    · fun_prop
    · fun_prop
    · simp only [Time.deriv]
      fun_prop

/-!

## B. Relation to the field strength tensor

The electric field can be expressed in terms of the field strength tensor as
`E_i = - c * F_0^i`.
-/

lemma electricField_eq_toFieldStrength_eval {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (t : Time)
    (x : Space d) (i : Fin d) (hA : Differentiable ℝ A) :
    A.electricField c t x i = - c *
    toScalar {A.toFieldStrength ((toTimeAndSpace c).symm (t, x)) | [Sum.inl 0] [Sum.inr i]}ᵀ := by
  rw [toFieldStrength_eval_apply_eq_single]
  simp only [Fin.isValue, inl_0_inl_0, one_mul, inr_i_inr_i, neg_mul, sub_neg_eq_add]
  rw [electricField]
  simp only [PiLp.sub_apply, PiLp.neg_apply, Fin.isValue, mul_add, neg_add_rev]
  congr
  · simp only [grad_apply, Fin.isValue]
    trans c * ∂_ (Sum.inr i) (fun x => A x (Sum.inl 0)) ((toTimeAndSpace c).symm (t, x)); swap
    · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq]
      rw [Lorentz.Vector.fderiv_apply]
      exact hA
    · rw [SpaceTime.deriv_sum_inr c]
      simp [scalarPotential]
      change Space.deriv i (fun y => c * A ((toTimeAndSpace c).symm (t, y)) (Sum.inl 0)) x = _
      rw [Space.deriv_eq_fderiv_basis, fderiv_const_mul]
      simp [← Space.deriv_eq_fderiv_basis]
      · fun_prop
      · fun_prop
  · exact 2
  · rw [SpaceTime.deriv_sum_inl c]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [Time.deriv_eq, Time.deriv_eq]
    rw [vectorPotential]
    simp [timeSlice]
    rw [Lorentz.Vector.fderiv_apply]
    change ((fderiv ℝ (fun t => WithLp.toLp 2 fun i =>
        A ((toTimeAndSpace c).symm (t, x)) (Sum.inr i)) t) 1).ofLp i = _
    rw [← Time.fderiv_euclid]
    · apply Time.differentiable_euclid
      intro i
      simp only
      fun_prop
    · fun_prop
    · exact hA
  · exact 1

lemma toFieldStrength_eval_inl_inr_eq_electricField {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) (i : Fin d) (hA : Differentiable ℝ A) :
    toScalar {A.toFieldStrength x | [Sum.inl 0] [Sum.inr i]}ᵀ =
    - (1 /c) * A.electricField c (x.time c) x.space i := by
  rw [electricField_eq_toFieldStrength_eval A (x.time c) x.space i hA]
  simp

lemma toFieldStrength_eval_inr_inl_eq_electricField {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) (i : Fin d) (hA : Differentiable ℝ A) :
    toScalar {A.toFieldStrength x | [Sum.inr i] [Sum.inl 0]}ᵀ =
    (1 /c) * A.electricField c (x.time c) x.space i := by
  rw [toFieldStrength_eval_antisymm A x (Sum.inr i) (Sum.inl 0),
    toFieldStrength_eval_inl_inr_eq_electricField A x i hA]
  ring
/-!

## C. Smoothness of the electric field

-/

lemma electricField_contDiff {n} {c : SpeedOfLight} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n ↿(A.electricField c) := by
  rw [@contDiff_euclidean]
  intro i
  conv =>
    enter [3, x];
    change A.electricField c x.1 x.2 i
    rw [electricField_eq_toFieldStrength_eval (A) x.1 x.2 i (hA.differentiable (by simp))]
  apply ContDiff.mul
  · fun_prop
  exact (toFieldStrength_eval_contDiff hA).comp
    (ContinuousLinearEquiv.contDiff (toTimeAndSpace c).symm)

lemma electricField_apply_contDiff {n} {c : SpeedOfLight} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n (↿(fun t x => A.electricField c t x i)) :=
  (ContinuousLinearMap.contDiff (𝕜 := ℝ) (EuclideanSpace.proj i)).comp (electricField_contDiff hA)

lemma electricField_apply_contDiff_space {n} {A : ElectromagneticPotential d}
    {c : SpeedOfLight}
    (hA : ContDiff ℝ (n + 1) A) (t : Time) :
    ContDiff ℝ n (fun x => A.electricField c t x i) :=
  (electricField_apply_contDiff hA).comp (f := fun x => (t, x)) (by fun_prop)

lemma electricField_apply_contDiff_time {n} {c : SpeedOfLight} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) (x : Space d) :
    ContDiff ℝ n (fun t => A.electricField c t x i) :=
  (electricField_apply_contDiff hA).comp (f := fun t => (t, x)) (by fun_prop)

/-!

## D. Differentiability of the electric field

-/

lemma electricField_differentiable {A : ElectromagneticPotential d} {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) : Differentiable ℝ (↿(A.electricField c)) :=
  (electricField_contDiff (n := 1) hA).differentiable one_ne_zero

lemma electricField_differentiable_time {A : ElectromagneticPotential d} {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) (x : Space d) : Differentiable ℝ (A.electricField c · x) :=
  (electricField_differentiable hA).comp (f := fun t => (t, x)) (by fun_prop)

lemma electricField_differentiable_space {A : ElectromagneticPotential d} {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) (t : Time) : Differentiable ℝ (A.electricField c t) :=
  (electricField_differentiable hA).comp (f := fun x => (t, x)) (by fun_prop)

lemma electricField_apply_differentiable {A : ElectromagneticPotential d}
    {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ (fun (tx : Time × Space d) => A.electricField c tx.1 tx.2 i) :=
  (ContinuousLinearMap.differentiable (𝕜 := ℝ) (EuclideanSpace.proj i)).comp
    (electricField_differentiable hA)
lemma electricField_apply_differentiable_space {A : ElectromagneticPotential d}
    {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) (t : Time) (i : Fin d) :
    Differentiable ℝ (fun x => A.electricField c t x i) :=
  (electricField_apply_differentiable hA).comp (f := fun x => (t, x)) (by fun_prop)

lemma electricField_apply_differentiable_time {A : ElectromagneticPotential d}
    {c : SpeedOfLight}
    (hA : ContDiff ℝ 2 A) (x : Space d) (i : Fin d) :
    Differentiable ℝ (fun t => A.electricField c t x i) :=
  (electricField_apply_differentiable hA).comp (f := fun t => (t, x)) (by fun_prop)

/-!

## E. Time derivative of the vector potential in terms of the electric field

-/

lemma time_deriv_vectorPotential_eq_electricField {d} {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (t : Time) (x : Space d) :
    ∂ₜ (fun t => A.vectorPotential c t x) t =
    - A.electricField c t x - ∇ (A.scalarPotential c t) x := by
  rw [electricField]
  abel

lemma time_deriv_comp_vectorPotential_eq_electricField {d} {A : ElectromagneticPotential d}
    {c : SpeedOfLight}
    (hA : Differentiable ℝ A)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (fun t => A.vectorPotential c t x i) t =
    - A.electricField c t x i - ∂[i] (A.scalarPotential c t) x := by
  rw [Time.deriv_euclid, time_deriv_vectorPotential_eq_electricField]
  simp
  rfl
  apply vectorPotential_differentiable_time A hA x

/-!

## F. Derivatives of the electric field in terms of field strength tensor

-/

open Space

lemma time_deriv_electricField_eq_toFieldStrength_eval {d} {A : ElectromagneticPotential d}
    {c : SpeedOfLight} (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (fun t => A.electricField c t x) t i =
    - c ^ 2 * ∂_ (Sum.inl 0) (fun x => toScalar {A.toFieldStrength x | [Sum.inl 0] [Sum.inr i]}ᵀ)
    ((toTimeAndSpace c).symm (t, x)) := by
  rw [SpaceTime.deriv_sum_inl c]
  simp only [one_div, ContinuousLinearEquiv.apply_symm_apply, Fin.isValue, smul_eq_mul, neg_mul]
  rw [← Time.deriv_euclid]
  conv_lhs =>
    enter [1, t]
    rw [electricField_eq_toFieldStrength_eval (c := c) A t x i (hA.differentiable (by simp))]
  rw [Time.deriv_eq, fderiv_const_mul]
  simp [← Time.deriv_eq]
  field_simp
  · exact (toFieldStrength_eval_differentiable_time hA x).differentiableAt
  · apply electricField_differentiable_time hA x
  · apply toFieldStrength_eval_differentiable hA

lemma div_electricField_eq_toFieldStrength_eval {d} {A : ElectromagneticPotential d}
    {c : SpeedOfLight} (hA : ContDiff ℝ 2 A) (t : Time) (x : Space d) :
    (∇ ⬝ A.electricField c t) x = c * ∑ (μ : (Fin 1 ⊕ Fin d)),
      (∂_ μ (fun x => toScalar {A.toFieldStrength x | [μ] [Sum.inl 0]}ᵀ)
        ((toTimeAndSpace c).symm (t, x))) := by
  rw [Finset.mul_sum]
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, toFieldStrength_eval_diag_eq_zero, SpaceTime.deriv_zero, Pi.ofNat_apply,
    mul_zero, zero_add]
  conv_rhs =>
    enter [2, i]
    rw [SpaceTime.deriv_sum_inr c _ (toFieldStrength_eval_differentiable hA)]
  rw [Space.div]
  congr
  funext i
  simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.isValue]
  conv_lhs =>
    enter [2, y]
    rw [electricField_eq_toFieldStrength_eval (c := c) A t y i (hA.differentiable (by simp))]
    rw [toFieldStrength_eval_antisymm]
  rw [Space.deriv_eq_fderiv_basis, fderiv_const_mul]
  simp [← Space.deriv_eq_fderiv_basis]
  exact (toFieldStrength_eval_differentiable_space hA t).neg.differentiableAt
end ElectromagneticPotential

end Electromagnetism
