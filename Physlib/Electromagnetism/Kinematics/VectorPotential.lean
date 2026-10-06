/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Kinematics.EMPotential
/-!

# The vector Potential

## i. Overview

The electromagnetic potential is given by
`A = (1/c φ, \vec A)`
where `φ` is the scalar potential and `\vec A` is the vector potential.

In this module we define the vector potential, and prove lemmas about it.

Since `A` is relativistic it is a function of `SpaceTime d`, whilst
the vector potential is non-relativistic and is therefore a function of `Time` and `Space d`.

## ii. Key results

- `ElectromagneticPotential.vectorPotential` : The vector potential from an
  electromagnetic potential.

## iii. Table of contents

- A. Definition of the Vector Potential
- B. Smoothness of the vector potential
- C. Differentiablity of the vector potential

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

/-!

## A. Definition of the Vector Potential

-/

/-- The vector potential from the electromagnetic potential. -/
noncomputable def vectorPotential {d} (c : SpeedOfLight := 1) (A : ElectromagneticPotential d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) := timeSlice c <|
  fun x => WithLp.toLp 2 fun i => A x (Sum.inr i)

/-!

## B. Relation to constructors

-/

@[simp]
lemma ofScalarPotential_vectorPotential {d} (c : SpeedOfLight)
    (φ : Time → Space d → ℝ) : (ofScalarPotential c φ).vectorPotential c = 0 := by
  simp only [vectorPotential, ofScalarPotential]
  rfl

@[simp]
lemma ofStaticScalarPotential_vectorPotential {d} (c : SpeedOfLight)
    (φ : Space d → ℝ) : (ofStaticScalarPotential c φ).vectorPotential c = 0 := by
  simp [ofStaticScalarPotential]

@[simp]
lemma ofVectorPotential_vectorPotential {d} (c : SpeedOfLight)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (ofVectorPotential c A).vectorPotential c = A := by
  ext i
  simp [vectorPotential, ofVectorPotential]

@[simp]
lemma ofStaticVectorPotential_vectorPotential {d} (c : SpeedOfLight)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    (ofStaticVectorPotential c A).vectorPotential c = fun _ => A := by
  simp [ofStaticVectorPotential]

@[simp]
lemma ofPotentials_vectorPotential {d} (c : SpeedOfLight) (φ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (ofPotentials c φ A).vectorPotential c = A := by
  ext i
  simp [vectorPotential, ofPotentials]

@[simp]
lemma ofStaticPotentials_vectorPotential {d} (c : SpeedOfLight) (φ : Space d → ℝ)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    (ofStaticPotentials c φ A).vectorPotential c = fun _ => A := by
  simp [ofStaticPotentials_eq_ofPotentials]

/-!

## B.1. ofElectromagneticField

-/

open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_vectorPotential (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) :
    (ofElectromagneticField c E B).vectorPotential c =
    fun t x => - ∫ u in 0..(1 : ℝ), (u • Space.basis.repr x) ⨯ₑ₃ B t (u • x) ∂volume := by
  simp [ofElectromagneticField]

open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_vectorPotential_apply {t x} (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) (i : Fin 3) (hB : Continuous ↿B) :
    (ofElectromagneticField c E B).vectorPotential c t x i =
    - ∫ u in 0..(1 : ℝ), ((u • Space.basis.repr x) ⨯ₑ₃ B t (u • x)) i ∂volume := by
  simp [ofElectromagneticField_vectorPotential]
  rw [intervalIntegral.integral_of_le (by simp), intervalIntegral.integral_of_le (by simp)]
  rw [MeasureTheory.eval_integral_piLp]
  simp only [PiLp.smul_apply, smul_eq_mul]
  intro i
  apply MeasureTheory.IntegrableOn.integrable
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le]
  apply Continuous.intervalIntegrable
  fun_prop
  simp

open MeasureTheory Matrix Space InnerProductSpace Time in
lemma ofElectromagneticField_vectorPotential_apply_eq_expand {t x} {c : SpeedOfLight}
    {E : Time → Space 3 → EuclideanSpace ℝ (Fin 3)}
    {B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)} (hB : Continuous ↿B) (i : Fin 3) :
    (ofElectromagneticField c E B).vectorPotential c t x i =
    x (i + 2) * ∫ u in 0..(1 : ℝ), u * B t (u • x) (i + 1) ∂volume -
    x (i + 1) * ∫ u in 0..(1 : ℝ), u * B t (u • x) (i + 2) ∂volume := by
  fin_cases i
  all_goals
  · rw [ofElectromagneticField_vectorPotential_apply _ _ _ _ hB]
    simp [crossProduct]
    ring_nf
    rw [intervalIntegral.integral_sub, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    ring_nf
    congr
    · ext u
      ring
    · ext u
      ring
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop

open MeasureTheory Matrix Space InnerProductSpace Time in
@[fun_prop]
lemma contDiff_vectorPotential_ofElectromagneticField {n : ℕ} (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hB : ContDiff ℝ n ↿B) : ContDiff ℝ n ↿((ofElectromagneticField c E B).vectorPotential c) := by
  let A : Time → Space → EuclideanSpace ℝ (Fin 3) := fun t x =>
    - ∫ u in 0..(1 : ℝ), (u • basis.repr x) ⨯ₑ₃ B t (u • x) ∂(volume)
  have h1 : ContDiff ℝ n ↿A := by
    simp only [WithLp.equiv_apply, A]
    apply ContDiff.neg
    apply contDiff_parametric_intervalIntegral_of_contDiff
    refine contDiff_euclidean.mpr ?_
    intro i
    let C : (Time × Space) × ℝ → EuclideanSpace ℝ (Fin 3) := fun p =>
      let (t, x) := p.1
      let u := p.2
      (u • basis.repr x) ⨯ₑ₃ B t (u • x)
    change ContDiff ℝ n (fun x => C x i)
    fin_cases i
    all_goals
    · simp [C, crossProduct]
      fun_prop
  suffices h : ContDiff ℝ n ↿A by
    convert h
    simp [ofElectromagneticField_vectorPotential, A]
  fun_prop

/-- At a fixed time, the vector potential of `ofElectromagneticField` is `C^n` in space if the
  magnetic field is `C^n` in space at that time. -/
@[fun_prop]
lemma contDiff_vectorPotential_ofElectromagneticField_space {n : ℕ} (c : SpeedOfLight)
    (E : Time → Space 3 → EuclideanSpace ℝ (Fin 3))
    (B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) (t : Time) (hB : ContDiff ℝ n (B t)) :
    ContDiff ℝ n ((ofElectromagneticField c E B).vectorPotential c t) := by
  rw [ofElectromagneticField_vectorPotential]
  apply ContDiff.neg
  apply contDiff_parametric_intervalIntegral_of_contDiff
  refine contDiff_euclidean.mpr ?_
  intro i
  fin_cases i
  all_goals
  · simp [Function.HasUncurry.uncurry, crossProduct]
    fun_prop

open InnerProductSpace
lemma vectorPotential_inner_radial_eq_zero_ofElectromagneticField
    {c : SpeedOfLight} {E B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)}
    {t : Time} {x : Space 3} {a : ℝ} (hB : Continuous ↿B) :
    ⟪(ofElectromagneticField c E B).vectorPotential c t (a • x), Space.basis.repr x⟫_ℝ = 0 := by
  rw [real_inner_comm]
  rw [PiLp.inner_apply]
  have h1 (a b : ℝ) : ⟪a, b⟫_ℝ = b * a:= by rfl
  simp only [Space.basis_repr_apply, ofElectromagneticField_vectorPotential_apply_eq_expand hB,
    Fin.isValue, Space.smul_apply, h1, Fin.sum_univ_three, zero_add, Fin.reduceAdd]
  ring

open Time
@[simp]
lemma time_deriv_vectorPotential_inner_radial_eq_zero_ofElectromagneticField
    {c : SpeedOfLight} {E B : Time → Space 3 → EuclideanSpace ℝ (Fin 3)}
    {t : Time} {x : Space 3} {a : ℝ} (hB : ContDiff ℝ 1 ↿B) :
    ⟪∂ₜ ((ofElectromagneticField c E B).vectorPotential c · (a • x)) t,
      Space.basis.repr x⟫_ℝ = 0 := by
  trans ∂ₜ (fun t => ⟪(ofElectromagneticField c E B).vectorPotential c t (a • x),
    Space.basis.repr x⟫_ℝ) t
  · rw [Time.deriv, Time.deriv]
    rw [fderiv_inner_apply]
    simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, inner_zero_right,
      zero_add]
    apply Differentiable.differentiableAt
    fun_prop
    fun_prop
  conv_lhs =>
    enter [1, t]
    rw [vectorPotential_inner_radial_eq_zero_ofElectromagneticField (by fun_prop)]
  simp

/-!

## B. Smoothness of the vector potential

We prove various lemmas about the smoothness of the vector potential from
the smoothness of the electromagnetic potential.

-/

@[fun_prop]
lemma vectorPotential_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n ↿(A.vectorPotential c) := by
  simp [vectorPotential]
  apply timeSlice_contDiff
  refine contDiff_euclidean.mpr ?_
  have h1 : ∀ i, ContDiff ℝ n (fun x => A x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hA
  exact fun i => h1 (Sum.inr i)

open ContDiff
@[fun_prop]
lemma vectorPotential_contDiff_of_smooth {n : ℕ} {d} {c : SpeedOfLight}
    (A : ElectromagneticPotential d) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ n ↿(A.vectorPotential c) := by
  apply vectorPotential_contDiff
  exact hA.of_le (ENat.LEInfty.out)

@[fun_prop]
lemma vectorPotential_apply_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d) : ContDiff ℝ n ↿(fun t x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿(A.vectorPotential c))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA

/-!

## C. Differentiablity of the vector potential

We prove various lemmas about the differentiablity of the vector potential from
the differentiablity of the electromagnetic potential.

-/

@[fun_prop]
lemma vectorPotential_differentiable {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ ↿(A.vectorPotential c) := by
  simp [vectorPotential]
  apply timeSlice_differentiable
  refine differentiable_euclidean.mpr ?_
  have h1 : ∀ i, Differentiable ℝ (fun x => A x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hA
  exact fun i => h1 (Sum.inr i)

@[fun_prop]
lemma vectorPotential_differentiable_time {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (x : Space d) : Differentiable ℝ (A.vectorPotential c · x) := by
  fun_prop

end ElectromagneticPotential

end Electromagnetism
