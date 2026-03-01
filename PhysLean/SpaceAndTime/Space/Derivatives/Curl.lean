/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Laplacian
/-!

# Curl on Space

## i. Overview

In this module we define the curl of functions and distributions on 3-dimensional
space `Space 3`.

We also prove some basic vector-identities involving of the curl operator.

## ii. Key results

- `curl` : The curl operator on functions from `Space 3` to `EuclideanSpace ℝ (Fin 3)`.
- `distCurl` : The curl operator on distributions from `Space 3` to `EuclideanSpace ℝ (Fin 3)`.
- `div_of_curl_eq_zero` : The divergence of the curl of a function is zero.
- `distCurl_distGrad_eq_zero` : The curl of the gradient of a distribution is zero.

## iii. Table of contents

- A. The curl on functions
  - A.1. The curl on the zero function
  - A.2. The curl on a constant function
  - A.3. The curl distributes over addition
  - A.4. The curl distributes over scalar multiplication
  - A.5. The curl of a linear map is a linear map
  - A.6. Preliminary lemmas about second derivatives
  - A.7. The div of a curl is zero
  - A.8. The curl of a curl
- B. The curl on distributions
  - B.1. The components of the curl
  - B.2. Basic equalities
  - B.3. The curl of a grad is zero

## iv. References

-/

namespace Space

/-!

## A. The curl on functions

-/

/-- The vector calculus operator `curl`. -/
noncomputable def curl (f : Space → EuclideanSpace ℝ (Fin 3)) :
    Space → EuclideanSpace ℝ (Fin 3) := fun x =>
  -- get i-th component of `f`
  let fi i x := (f x) i
  -- derivative of i-th component in j-th coordinate
  -- ∂fᵢ/∂xⱼ
  let df i j x := ∂[j] (fi i) x
  WithLp.toLp 2 fun i =>
    match i with
    | 0 => df 2 1 x - df 1 2 x
    | 1 => df 0 2 x - df 2 0 x
    | 2 => df 1 0 x - df 0 1 x

@[inherit_doc curl]
macro (name := curlNotation) "∇" "×" f:term:100 : term => `(curl $f)

/-!

### A.1. The curl on the zero function

-/

@[simp]
lemma curl_zero : ∇ × (0 : Space → EuclideanSpace ℝ (Fin 3)) = 0 := by
  unfold curl Space.deriv
  simp only [Fin.isValue, Pi.ofNat_apply, fderiv_fun_const, ContinuousLinearMap.zero_apply,
    sub_self]
  ext x i
  fin_cases i <;>
  rfl

/-!

### A.2. The curl on a constant function

-/

@[simp]
lemma curl_const : ∇ × (fun _ : Space => v₃) = 0 := by
  unfold curl Space.deriv
  simp only [Fin.isValue, fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply,
    sub_self]
  ext x i
  fin_cases i <;>
  rfl

/-!

### A.3. The curl distributes over addition

-/

lemma curl_add (f1 f2 : Space → EuclideanSpace ℝ (Fin 3))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ × (f1 + f2) = ∇ × f1 + ∇ × f2 := by
  unfold curl
  ext x i
  fin_cases i <;>
  · simp only [Fin.isValue, Pi.add_apply, PiLp.add_apply, Fin.zero_eta]
    repeat rw [deriv_coord_add]
    simp only [Fin.isValue, Pi.add_apply]
    ring
    repeat assumption

/-!

### A.4. The curl distributes over scalar multiplication

-/

lemma curl_smul (f : Space → EuclideanSpace ℝ (Fin 3)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ × (k • f) = k • ∇ × f := by
  unfold curl
  ext x i
  fin_cases i <;>
  · simp only [Fin.isValue, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta]
    rw [deriv_coord_smul, deriv_coord_smul, mul_sub]
    repeat fun_prop

/-!

### A.5. The curl of a linear map is a linear map

-/

variable {W} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma curl_linear_map (f : W → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ w, Differentiable ℝ (f w))
    (hf' : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun w => ∇ × (f w)) := by
  constructor
  · intro w w'
    rw [hf'.map_add]
    rw [curl_add]
    repeat fun_prop
  · intros k w
    rw [hf'.map_smul]
    rw [curl_smul]
    fun_prop

/-!

### A.6. Preliminary lemmas about second derivatives

-/

/-- Second derivatives distribute coordinate-wise over addition (all three components for div). -/
lemma deriv_coord_2nd_add (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∂[i] (fun x => ∂[u] (fun x => f x u) x + (∂[v] (fun x => f x v) x + ∂[w] (fun x => f x w) x)) =
    (∂[i] (∂[u] (fun x => f x u))) + (∂[i] (∂[v] (fun x => f x v))) +
    (∂[i] (∂[w] (fun x => f x w))) := by
  unfold deriv
  ext x
  rw [fderiv_fun_add, fderiv_fun_add]
  simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
  ring
  repeat fun_prop

/-- Second derivatives distribute coordinate-wise over subtraction (two components for curl). -/
lemma deriv_coord_2nd_sub (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∂[u] (fun x => ∂[v] (fun x => f x w) x - ∂[w] (fun x => f x v) x) =
    (∂[u] (∂[v] (fun x => f x w))) - (∂[u] (∂[w] (fun x => f x v))) := by
  unfold deriv
  ext x
  simp only [Pi.sub_apply]
  rw [fderiv_fun_sub]
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply]
  repeat fun_prop

/-!

### A.7. The div of a curl is zero

-/

lemma div_of_curl_eq_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇ ⬝ (∇ × f) = 0 := by
  unfold div curl Finset.sum
  ext x
  simp only [Fin.isValue, Fin.univ_val_map, List.ofFn_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero,
    Pi.zero_apply]
  rw [deriv_coord_2nd_sub, deriv_coord_2nd_sub, deriv_coord_2nd_sub]
  simp only [Fin.isValue, Pi.sub_apply]
  rw [deriv_commute fun x => f x 0, deriv_commute fun x => f x 1,
    deriv_commute fun x => f x 2]
  simp only [Fin.isValue, sub_add_sub_cancel', sub_self]
  repeat
    try apply contDiff_euclidean.mp
    exact hf

/-!

### A.8. The curl of a curl

-/

lemma curl_of_curl (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇ × (∇ × f) = ∇ (∇ ⬝ f) - Δ f := by
  unfold laplacianVec laplacian div grad curl Finset.sum
  simp only [Fin.isValue, Fin.univ_val_map, List.ofFn_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  ext x i
  fin_cases i <;>
  · simp only [Fin.isValue, Fin.reduceFinMk, Pi.sub_apply]
    rw [deriv_coord_2nd_sub, deriv_coord_2nd_sub]
    simp only [Fin.isValue, Pi.sub_apply, PiLp.sub_apply]
    rw [deriv_coord_2nd_add]
    rw [deriv_commute fun x => f x 0, deriv_commute fun x => f x 1,
      deriv_commute fun x => f x 2]
    simp only [Fin.isValue, Pi.add_apply]
    ring
    repeat
      try apply contDiff_euclidean.mp
      exact hf

/-!

## B. The curl on distributions

-/

open MeasureTheory SchwartzMap InnerProductSpace Distribution

/-- The curl of a distribution `Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))` as a distribution
  `Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))`. -/
noncomputable def distCurl : (Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) →ₗ[ℝ]
    (Space) →d[ℝ] (EuclideanSpace ℝ (Fin 3)) where
  toFun f :=
    let curl : (Space →L[ℝ] (EuclideanSpace ℝ (Fin 3))) →L[ℝ] (EuclideanSpace ℝ (Fin 3)) := {
      toFun dfdx:= WithLp.toLp 2 fun i =>
        match i with
        | 0 => dfdx (basis 2) 1 - dfdx (basis 1) 2
        | 1 => dfdx (basis 0) 2 - dfdx (basis 2) 0
        | 2 => dfdx (basis 1) 0 - dfdx (basis 0) 1
      map_add' v1 v2 := by
        ext i
        fin_cases i
        all_goals
          simp only [Fin.isValue, ContinuousLinearMap.add_apply, PiLp.add_apply, Fin.zero_eta]
          ring
      map_smul' a v := by
        ext i
        fin_cases i
        all_goals
          simp only [Fin.isValue, ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.smul_apply,
            smul_eq_mul, RingHom.id_apply, Fin.reduceFinMk]
          ring
      cont := by
        apply Continuous.comp
        · fun_prop
        rw [continuous_pi_iff]
        intro i
        fin_cases i
        all_goals
          fun_prop
        }
    curl.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    ext x
    simp
  map_smul' a f := by
    ext x
    simp

/-!

### B.1. The components of the curl

-/

lemma distCurl_apply_zero (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    distCurl f η 0 = - f (SchwartzMap.evalCLM ℝ Space ℝ (basis 2) (fderivCLM ℝ Space ℝ η)) 1
    + f (SchwartzMap.evalCLM ℝ Space ℝ (basis 1) (fderivCLM ℝ Space ℝ η)) 2 := by
  simp [distCurl]
  rw [fderivD_apply, fderivD_apply]
  simp

lemma distCurl_apply_one (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    distCurl f η 1 = - f (SchwartzMap.evalCLM ℝ Space ℝ (basis 0) (fderivCLM ℝ Space ℝ η)) 2
    + f (SchwartzMap.evalCLM ℝ Space ℝ (basis 2) (fderivCLM ℝ Space ℝ η)) 0 := by
  simp [distCurl]
  rw [fderivD_apply, fderivD_apply]
  simp

lemma distCurl_apply_two (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    distCurl f η 2 = - f (SchwartzMap.evalCLM ℝ Space ℝ (basis 1) (fderivCLM ℝ Space ℝ η)) 0
    + f (SchwartzMap.evalCLM ℝ Space ℝ (basis 0) (fderivCLM ℝ Space ℝ η)) 1 := by
  simp [distCurl]
  rw [fderivD_apply, fderivD_apply]
  simp

/-!

### B.2. Basic equalities

-/

lemma distCurl_apply (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    distCurl f η = WithLp.toLp 2 fun
    | 0 => - f (SchwartzMap.evalCLM ℝ Space ℝ (basis 2) (fderivCLM ℝ Space ℝ η)) 1
      + f (SchwartzMap.evalCLM ℝ Space ℝ (basis 1) (fderivCLM ℝ Space ℝ η)) 2
    | 1 => - f (SchwartzMap.evalCLM ℝ Space ℝ (basis 0) (fderivCLM ℝ Space ℝ η)) 2
      + f (SchwartzMap.evalCLM ℝ Space ℝ (basis 2) (fderivCLM ℝ Space ℝ η)) 0
    | 2 => - f (SchwartzMap.evalCLM ℝ Space ℝ (basis 1) (fderivCLM ℝ Space ℝ η)) 0
      + f (SchwartzMap.evalCLM ℝ Space ℝ (basis 0) (fderivCLM ℝ Space ℝ η)) 1 := by
  ext i
  fin_cases i
  · simp [distCurl_apply_zero]
  · simp [distCurl_apply_one]
  · simp [distCurl_apply_two]

/-!

### B.3. The curl of a grad is zero

-/

/-- The curl of a grad is equal to zero. -/
@[simp]
lemma distCurl_distGrad_eq_zero (f : (Space) →d[ℝ] ℝ) :
    distCurl (distGrad f) = 0 := by
  ext η i
  fin_cases i
  all_goals
  · dsimp
    try rw [distCurl_apply_zero]
    try rw [distCurl_apply_one]
    try rw [distCurl_apply_two]
    rw [distGrad_eq_sum_basis, distGrad_eq_sum_basis]
    simp [Pi.single_apply]
    rw [← map_neg, ← map_add, ← ContinuousLinearMap.map_zero f]
    congr
    ext x
    simp only [Fin.isValue, SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.zero_apply]
    rw [schwartMap_fderiv_comm]
    change ((SchwartzMap.evalCLM ℝ Space ℝ _)
      ((fderivCLM ℝ Space ℝ) ((SchwartzMap.evalCLM ℝ Space ℝ _) ((fderivCLM ℝ Space ℝ) η)))) x +
      - ((SchwartzMap.evalCLM ℝ Space ℝ _)
        ((fderivCLM ℝ Space ℝ) ((SchwartzMap.evalCLM ℝ Space ℝ _) ((fderivCLM ℝ Space ℝ) η)))) x = _
    simp

end Space
