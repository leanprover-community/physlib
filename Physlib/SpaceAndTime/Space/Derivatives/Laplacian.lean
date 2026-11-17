/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Div
/-!

# The Laplacian operator on `Space d`

## i. Overview

In this module we define the Laplacian operator on functions and vector-valued
functions defined on `Space d`.

## ii. Key results

- `laplacian` : The Laplacian operator on scalar functions on `Space d`.
- `laplacianVec` : The Laplacian operator on vector-valued functions on `Space d`.
- `distLaplacian` : The Laplacian operator on distributions on `Space d`.
- `laplacian_comp_linearIsometryEquiv` : The Laplacian commutes with composition by a linear
  isometry of `Space d`.
- `laplacianVec_comp_linearIsometryEquiv` : The vector Laplacian commutes with composition by a
  linear isometry of `Space d`.

## iii. Table of contents

- A. Laplacian on functions to ℝ
  - A.1. Relation between laplacian and divergence of gradient
- B. Laplacian on vector valued functions
- C. Laplacian of distributions
  - C.1. Laplacian of constant distributions
- D. Composition with a linear isometry

## iv. References

* None.
-/

@[expose] public section

namespace Space

/-!

## A. Laplacian on functions to ℝ

-/

/-- The scalar `laplacian` operator. -/
noncomputable def laplacian {d} (f : Space d → ℝ) : Space d → ℝ :=
    ∇ ⬝ ∇ f

@[inherit_doc laplacian]
scoped[Space] notation "Δ" => laplacian

/-!

### A.1. Relation between laplacian and divergence of gradient

-/

lemma laplacian_eq_sum_snd_deriv {d} (f : Space d → ℝ) :
    Δ f = fun x => ∑ i, ∂[i] (∂[i] f) x := by
  unfold laplacian div grad
  simp

/-!

## B. Laplacian on vector valued functions

-/

/-- The vector `laplacianVec` operator. -/
noncomputable def laplacianVec {d} (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x => WithLp.toLp 2 fun i =>
  -- get i-th component of `f`
  Δ (fun x => f x i) x

@[inherit_doc laplacianVec]
scoped[Space] notation "Δᵥ" => laplacianVec

open Physlib Distribution

/-!

## C. Laplacian of distributions

-/

/-- The distributional `distLaplacian` operator. -/
noncomputable def distLaplacian {d} :
    ((Space d) →d[ℝ] ℝ) →ₗ[ℝ] (Space d) →d[ℝ] ℝ :=
    distDiv ∘ₗ distGrad

@[inherit_doc distLaplacian]
scoped[Space] notation "Δᵈ" => distLaplacian

/-!

### C.1. Laplacian of constant distributions

-/

@[simp]
lemma distLaplacian_const {d : ℕ} (c : ℝ) :
    Δᵈ (Distribution.const ℝ (Space d) c) = 0 := by
  simp [distLaplacian, distGrad_const]

/-!

## D. Composition with a linear isometry

-/

/-- The Laplacian of `f ∘ R` at `x` is the Laplacian of `f` at `R x`, for a linear isometry `R`
  of space. -/
lemma laplacian_comp_linearIsometryEquiv {d : ℕ} (f : Space d → ℝ) (R : Space d ≃ₗᵢ[ℝ] Space d)
    (x : Space d) (hf : DifferentiableAt ℝ (fderiv ℝ f) (R x)) :
    Δ (fun y => f (R y)) x = Δ f (R x) := by
  have hR (g : Space d → ℝ) (y : Space d) : fderiv ℝ (fun y => g (R y)) y =
      (fderiv ℝ g (R y)).comp (R.toContinuousLinearEquiv : Space d →L[ℝ] Space d) :=
    R.toContinuousLinearEquiv.comp_right_fderiv
  -- Second derivatives of `f` at `R x`; this is where `hf` is used.
  have h2 (v w : Space d) : fderiv ℝ (fun z => fderiv ℝ f z v) (R x) w =
      fderiv ℝ (fderiv ℝ f) (R x) w v := by
    rw [fderiv_clm_apply hf (differentiableAt_const v)]
    simp
  have hL (i : Fin d) : ∂[i] (∂[i] (fun y => f (R y))) x =
      fderiv ℝ (fderiv ℝ f) (R x) (R (basis i)) (R (basis i)) := by
    have e : ∂[i] (fun y => f (R y)) = fun y => fderiv ℝ f (R y) (R (basis i)) := by
      funext y
      rw [deriv_eq, hR f y]
      rfl
    rw [deriv_eq, e, hR (fun z => fderiv ℝ f z (R (basis i))) x]
    exact h2 _ _
  have hr (i : Fin d) : ∂[i] (∂[i] f) (R x) = fderiv ℝ (fderiv ℝ f) (R x) (basis i) (basis i) := by
    rw [deriv_eq, show ∂[i] f = fun z => fderiv ℝ f z (basis i) from funext (deriv_eq _ _)]
    exact h2 _ _
  -- The Laplacian of Mathlib at `R x`, computed in two orthonormal bases.
  have ht := (congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (basis.map R)) (R x)).symm.trans
    (congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f basis) (R x))
  calc Δ (fun y => f (R y)) x
      = ∑ i, fderiv ℝ (fderiv ℝ f) (R x) (R (basis i)) (R (basis i)) := by
        rw [laplacian_eq_sum_snd_deriv]
        exact Finset.sum_congr rfl fun i _ => hL i
    _ = ∑ i, fderiv ℝ (fderiv ℝ f) (R x) (basis i) (basis i) := by
        simpa [iteratedFDeriv_two_apply, OrthonormalBasis.map_apply] using ht
    _ = Δ f (R x) := by
        rw [laplacian_eq_sum_snd_deriv]
        exact (Finset.sum_congr rfl fun i _ => hr i).symm

/-- The vector Laplacian of `f ∘ R` at `x` is the vector Laplacian of `f` at `R x`, for a linear
  isometry `R` of space. -/
lemma laplacianVec_comp_linearIsometryEquiv {d : ℕ} (f : Space d → EuclideanSpace ℝ (Fin d))
    (R : Space d ≃ₗᵢ[ℝ] Space d) (x : Space d)
    (hf : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fun y => f y i)) (R x)) :
    Δᵥ (fun y => f (R y)) x = Δᵥ f (R x) := by
  ext i
  exact laplacian_comp_linearIsometryEquiv (fun y => f y i) R x (hf i)

end Space
