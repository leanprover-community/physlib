/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Electromagnetism.Kinematics.EMPotential
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
- `DistElectromagneticPotential.vectorPotential` : The vector potential from an
  electromagnetic potential which is a distribution.

## iii. Table of contents

- A. Definition of the Vector Potential
- B. Smoothness of the vector potential
- C. Differentiablity of the vector potential
- D. Vector potential for distributions

## iv. References

-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
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

## B. Smoothness of the vector potential

We prove various lemmas about the smoothness of the vector potential from
the smoothness of the electromagnetic potential.

-/

lemma vectorPotential_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n ↿(A.vectorPotential c) := by
  simp [vectorPotential]
  apply timeSlice_contDiff
  refine contDiff_euclidean.mpr ?_
  have h1 : ∀ i, ContDiff ℝ n (fun x => A x i) := by
    rw [SpaceTime.contDiff_vector]
    exact hA
  exact fun i => h1 (Sum.inr i)

lemma vectorPotential_apply_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d) : ContDiff ℝ n ↿(fun t x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿(A.vectorPotential c))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA

lemma vectorPotential_comp_contDiff {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (i : Fin d) : ContDiff ℝ n ↿(fun t x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ ↿(A.vectorPotential c))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff A hA

lemma vectorPotential_contDiff_space {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) : ContDiff ℝ n (A.vectorPotential c t) := by
  change ContDiff ℝ n (↿(A.vectorPotential c) ∘ fun x => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact vectorPotential_contDiff A hA
  · fun_prop

lemma vectorPotential_apply_contDiff_space {n} {d} {c : SpeedOfLight}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (t : Time) (i : Fin d) :
    ContDiff ℝ n (fun x => A.vectorPotential c t x i) := by
  change ContDiff ℝ n (EuclideanSpace.proj i ∘ (↿(A.vectorPotential c) ∘ fun x => (t, x)))
  refine ContDiff.comp ?_ ?_
  · exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (EuclideanSpace.proj i)
  · exact vectorPotential_contDiff_space A hA t

lemma vectorPotential_contDiff_time {n} {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) (x : Space d) : ContDiff ℝ n (A.vectorPotential c · x) := by
  change ContDiff ℝ n (↿(A.vectorPotential c) ∘ fun t => (t, x))
  refine ContDiff.comp ?_ ?_
  · exact vectorPotential_contDiff A hA
  · fun_prop

/-!

## C. Differentiablity of the vector potential

We prove various lemmas about the differentiablity of the vector potential from
the differentiablity of the electromagnetic potential.

-/

lemma vectorPotential_differentiable {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ ↿(A.vectorPotential c) := by
  simp [vectorPotential]
  apply timeSlice_differentiable
  refine differentiable_euclidean.mpr ?_
  have h1 : ∀ i, Differentiable ℝ (fun x => A x i) := by
    rw [SpaceTime.differentiable_vector]
    exact hA
  exact fun i => h1 (Sum.inr i)

lemma vectorPotential_differentiable_time {d} {c : SpeedOfLight} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (x : Space d) : Differentiable ℝ (A.vectorPotential c · x) := by
  change Differentiable ℝ (↿(A.vectorPotential c) ∘ fun t => (t, x))
  refine Differentiable.comp ?_ ?_
  · exact vectorPotential_differentiable A hA
  · fun_prop

end ElectromagneticPotential

/-!

## D. Vector potential for distributions

-/

namespace DistElectromagneticPotential
open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix SchwartzMap
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-- The vector potential of an electromagnetic potential which is a distribution. -/
noncomputable def vectorPotential {d} (c : SpeedOfLight) :
    DistElectromagneticPotential d →ₗ[ℝ]
    (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun A := Lorentz.Vector.spatialCLM d ∘L distTimeSlice c A
  map_add' A₁ A₂ := by
    ext ε
    simp [distTimeSlice]
  map_smul' r A := by
    ext ε i
    simp only [distTimeSlice, map_smul, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
      Pi.smul_apply, Function.comp_apply,
      Real.ringHom_apply, PiLp.smul_apply, smul_eq_mul]

end DistElectromagneticPotential

end Electromagnetism
