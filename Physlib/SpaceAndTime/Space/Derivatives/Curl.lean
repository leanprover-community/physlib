/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Laplacian
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Physlib.SpaceAndTime.Space.CrossProduct
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Physlib.Mathematics.LeviCivita.Basic

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
- `curl_eq_sum_leviCivitaSymbol` : The components of the curl as a contraction with the
  Levi-Civita symbol.

## iii. Table of contents

- A. The curl on functions
  - A.1. The curl on the zero function
  - A.2. The curl on a constant function
  - A.3. Basic operations on curl
  - A.4. The curl of a linear map is a linear map
  - A.5. Preliminary lemmas about second derivatives
  - A.6. The div of a curl is zero
  - A.7. The curl of a grad is zero
  - A.8. The curl of a curl
  - A.9. A divergence-free field is a curl
  - A.10. A curl-free field is a gradient
  - A.11. The curl in terms of the Levi-Civita symbol
- B. The curl on distributions
  - B.1. The components of the curl
  - B.2. Basic equalities
  - B.3. The curl of a grad is zero

## iv. References

* None.
-/

@[expose] public section

open Physlib

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
  WithLp.toLp 2 fun i => ∂[(i+1)] (fi (i+2)) x - ∂[(i+2)] (fi (i+1)) x

@[inherit_doc curl]
macro (name := curlNotation) "∇" "⨯" f:term:100 : term => `(curl $f)

/-!

### A.1. The curl on the zero function

-/

@[simp]
lemma curl_zero : ∇ ⨯ (0 : Space → EuclideanSpace ℝ (Fin 3)) = 0 := by
  unfold curl Space.deriv
  simp only [Fin.isValue, Pi.zero_apply, PiLp.zero_apply, fderiv_fun_const,
    _root_.zero_apply, sub_self]
  rfl

/-!

### A.2. The curl on a constant function

-/

@[simp]
lemma curl_const : ∇ ⨯ (fun _ : Space => v₃) = 0 := by
  unfold curl Space.deriv
  simp only [Fin.isValue, fderiv_fun_const, Pi.zero_apply, _root_.zero_apply,
    sub_self]
  rfl

/-!

### A.3. Basic operations on curl

-/

@[to_fun]
lemma curl_add (f1 f2 : Space → EuclideanSpace ℝ (Fin 3))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ ⨯ (f1 + f2) = ∇ ⨯ f1 + ∇ ⨯ f2 := by
  unfold curl
  ext x i
  fin_cases i <;>
  · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceAdd, zero_add, Pi.add_apply, PiLp.add_apply]
    repeat rw [deriv_coord_add]
    simp only [Fin.isValue, Pi.add_apply]
    ring
    repeat assumption

@[to_fun]
lemma curl_smul (f : Space → EuclideanSpace ℝ (Fin 3)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ ⨯ (k • f) = k • ∇ ⨯ f := by
  unfold curl
  ext x i
  simp only [Fin.isValue, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [deriv_coord_smul, deriv_coord_smul, mul_sub]
  repeat fun_prop

@[to_fun]
lemma curl_neg (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : Differentiable ℝ f) :
    ∇ ⨯ (-f) = -∇ ⨯ f := by
  rw [← neg_one_smul ℝ, curl_smul _ _ hf, neg_one_smul]

@[to_fun]
lemma curl_sub (f1 f2 : Space → EuclideanSpace ℝ (Fin 3))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ ⨯ (f1 - f2) = ∇ ⨯ f1 - ∇ ⨯ f2 := by
  rw [sub_eq_add_neg, curl_add, curl_neg, sub_eq_add_neg]
  repeat fun_prop

/-!

### A.4. The curl of a linear map is a linear map

-/

variable {W} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma curl_linear_map (f : W → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ w, Differentiable ℝ (f w))
    (hf' : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun w => ∇ ⨯ (f w)) := by
  constructor
  · intro w w'
    rw [hf'.map_add, curl_add]
    repeat fun_prop
  · intros k w
    rw [hf'.map_smul, curl_smul]
    fun_prop

/-!

### A.5. Preliminary lemmas about second derivatives

-/

/-- Second derivatives distribute coordinate-wise over addition (all three components for div). -/
lemma deriv_coord_2nd_add (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∂[i] (fun x => ∂[u] (fun x => f x u) x + (∂[v] (fun x => f x v) x + ∂[w] (fun x => f x w) x)) =
    (∂[i] (∂[u] (fun x => f x u))) + (∂[i] (∂[v] (fun x => f x v))) +
    (∂[i] (∂[w] (fun x => f x w))) := by
  repeat rw [deriv_eq_fderiv_fun]
  ext x
  rw [fderiv_fun_add, fderiv_fun_add]
  simp only [_root_.add_apply, Pi.add_apply]
  ring
  repeat fun_prop

/-- Second derivatives distribute coordinate-wise over subtraction (two components for curl). -/
lemma deriv_coord_2nd_sub (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∂[u] (fun x => ∂[v] (fun x => f x w) x - ∂[w] (fun x => f x v) x) =
    (∂[u] (∂[v] (fun x => f x w))) - (∂[u] (∂[w] (fun x => f x v))) := by
  repeat rw [deriv_eq_fderiv_fun]
  ext x
  simp only [Pi.sub_apply]
  rw [fderiv_fun_sub]
  simp only [FunLike.coe_sub, Pi.sub_apply]
  repeat fun_prop

/-!

### A.6. The div of a curl is zero

-/

lemma div_of_curl_eq_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇ ⬝ (∇ ⨯ f) = 0 := by
  unfold div curl Finset.sum
  ext x
  simp only [Fin.isValue, Fin.univ_val_map, List.ofFn_succ, zero_add, Fin.succ_zero_eq_one,
    Fin.reduceAdd, Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons,
    List.sum_nil, add_zero, Pi.ofNat_apply]
  rw [deriv_coord_2nd_sub, deriv_coord_2nd_sub, deriv_coord_2nd_sub]
  simp only [Fin.isValue, Pi.sub_apply]
  rw [deriv_commute fun x => f x 0, deriv_commute fun x => f x 1,
    deriv_commute fun x => f x 2]
  simp only [Fin.isValue, sub_add_sub_cancel', sub_self]
  repeat
    try apply contDiff_euclidean.mp
    exact hf

/-!

### A.7. The curl of a grad is zero

-/

lemma curl_of_grad_eq_zero (f : Space → ℝ) (hf : ContDiff ℝ 2 f) :
    ∇ ⨯ (∇ f) = 0 := by
  unfold curl grad
  ext x i
  simp only [Fin.isValue, Pi.zero_apply, PiLp.zero_apply]
  rw [deriv_commute _ hf]
  simp only [Fin.isValue, sub_self]

/-!

### A.8. The curl of a curl

-/

lemma curl_of_curl (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇ ⨯ (∇ ⨯ f) = ∇ (∇ ⬝ f) - Δᵥ f := by
  unfold laplacianVec laplacian div grad curl Finset.sum
  simp only [Fin.isValue, Fin.univ_val_map, List.ofFn_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  ext x i
  fin_cases i <;>
  · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd, zero_add, Pi.sub_apply, PiLp.sub_apply]
    rw [deriv_coord_2nd_sub, deriv_coord_2nd_sub]
    simp only [Fin.isValue, Pi.sub_apply]
    rw [deriv_coord_2nd_add]
    rw [deriv_commute fun x => f x 0, deriv_commute fun x => f x 1,
      deriv_commute fun x => f x 2]
    simp only [Fin.isValue, Pi.add_apply]
    ring
    repeat fun_prop

/-!

### A.9. A divergence-free field is a curl

We now prove that if the divergence of a function is zero,
then it is equal to the curl of some function.

This proof is involved, thus we have split it up into private definitions and lemmas.
The proof is by explicit construction. If `f` has divergence zero,
then we construct
```
∫ t in 0..1, (t • x) ⨯ f (t • x)
```
and show that the curl of this is equal to `f`.

We call the integrand of this function the `homotopyOperatorIntegrand`.
We build API around this to help in our proof.

-/
open Matrix MeasureTheory

/-- The homotopy operator is defined as `∫ t in 0..1, (t • x) ⨯ f (t • x)`.
  This is the integrand of that function. -/
private noncomputable def homotopyOperatorIntegrand (f : Space → EuclideanSpace ℝ (Fin 3)) :
  Space → ℝ → EuclideanSpace ℝ (Fin 3) := fun x t => (t • basis.repr x) ⨯ₑ₃ f (t • x)

private lemma homotopyOperatorIntegrand_eq (f : Space → EuclideanSpace ℝ (Fin 3)) :
    homotopyOperatorIntegrand f = fun x t => (t • basis.repr x) ⨯ₑ₃ f (t • x) := by rfl
@[fun_prop]
private lemma differentiable_homotopyOperatorIntegrand_space {f : Space → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) (t : ℝ) :
    Differentiable ℝ (homotopyOperatorIntegrand f · t) := by
  simp [homotopyOperatorIntegrand]
  refine differentiable_euclidean.mpr ?_
  intro i
  fin_cases i
  all_goals
  · simp [crossProduct]
    fun_prop

@[fun_prop]
private lemma homotopyOperatorIntegrand_continuous_param {f : Space → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) (x : Space) : Continuous (homotopyOperatorIntegrand f x ·) := by
  simp [homotopyOperatorIntegrand]
  have hf (i : Fin 3) : Continuous (fun t => f ((t : ℝ) • x) i) := by
    change Continuous (EuclideanSpace.proj i ∘ f ∘ fun t => t • x)
    apply Continuous.comp (by fun_prop)
    apply Continuous.comp ?_ ?_
    · exact hf.continuous
    · fun_prop
  refine Continuous.comp' (by fun_prop) ?_
  refine continuous_pi ?_
  intro i
  fin_cases i
  all_goals
  · simp [crossProduct]
    refine Continuous.fun_mul (by fun_prop) ?_
    refine Continuous.sub ?_ ?_
    all_goals
    · apply Continuous.mul ?_ ?_
      · fun_prop
      · exact hf _

private lemma intervalIntegrable_homotopyOperatorIntegrand {f : Space → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) (x : Space) :
    IntervalIntegrable (homotopyOperatorIntegrand f x ·) volume (0 : ℝ) 1 :=
  Continuous.intervalIntegrable (by fun_prop) 0 1

private lemma fderiv_homotopyOperatorIntegrand_eq_fderiv_crossProduct
    {f : Space → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) (x : Space) (t : ℝ) (y : Space) (i : Fin 3) :
    fderiv ℝ (homotopyOperatorIntegrand f · t) x y i =
    t • (fderiv ℝ (fun x => (WithLp.toLp 2 ((crossProduct (basis.repr x).ofLp)
      (f (t • x)).ofLp)).ofLp i) x) y := by
  have cross_diff (t : ℝ) : Differentiable ℝ (fun x => WithLp.toLp 2
        ((crossProduct (basis.repr x).ofLp) (f (t • x)).ofLp)) := by
    refine differentiable_euclidean.mpr ?_
    intro i
    fin_cases i
    all_goals
    · simp [crossProduct]
      fun_prop
  conv_lhs =>
    simp [homotopyOperatorIntegrand]
    rw [fderiv_fun_smul (by fun_prop) (Differentiable.differentiableAt (cross_diff t))]
    simp
  change t • (fderiv ℝ (fun x => WithLp.toLp 2
    ((crossProduct (basis.repr x).ofLp) (f (t • x)).ofLp)) x) y _ = _
  trans t • ((fderiv ℝ (fun x => WithLp.toLp 2
    ((crossProduct (basis.repr x).ofLp) (f (t • x)).ofLp) i) x) y)
  · change _ = t • (fderiv ℝ (EuclideanSpace.proj i ∘
      (fun x => (WithLp.toLp 2 ((crossProduct (basis.repr x).ofLp) (f (t • x)).ofLp)))) x) y
    rw [fderiv_comp]
    simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
      PiLp.proj_apply]
    · fun_prop
    · exact Differentiable.differentiableAt (cross_diff t)
  rfl

private lemma fderiv_homotopyOperatorIntegrand_apply_eq {f : Space → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) (x : Space) (t : ℝ) (y : Space) (i : Fin 3) :
    fderiv ℝ (homotopyOperatorIntegrand f · t) x y i =
      t * (x (i+1) * t * fderiv ℝ f (t • x) y (i+2) + f (t • x) (i+2) * y (i+1) -
      (x (i+2) * t * fderiv ℝ f (t • x) y (i+1) + f (t • x) (i+1) * y (i+2))) := by
  have fderiv_f (x : Space) (t : ℝ) (y : Space)
      (i : Fin 3) : (fderiv ℝ (fun x => (f (t • x)).ofLp i) x) y = t * fderiv ℝ f (t • x) y i := by
    change (fderiv ℝ (EuclideanSpace.proj i ∘ f ∘ fun x => t • x) x) y = _
    rw [fderiv_comp _ (by fun_prop) (by fun_prop),
      fderiv_comp _ (by fun_prop) (by fun_prop), fderiv_fun_smul (by fun_prop) (by fun_prop)]
    simp only [Function.comp_apply, ContinuousLinearMap.fderiv, fderiv_fun_id, fderiv_fun_const,
      Pi.zero_apply, ContinuousLinearMap.zero_smulRight, add_zero, ContinuousLinearMap.coe_comp,
      FunLike.coe_smul, ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq, map_smul,
      PiLp.proj_apply, smul_eq_mul]
  fin_cases i
  all_goals
    rw [fderiv_homotopyOperatorIntegrand_eq_fderiv_crossProduct]
    simp [crossProduct]
    rw [fderiv_fun_sub (by fun_prop) (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop),
      fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [fderiv_f]
    ring_nf
    simp only [true_or]
    exact hf

private lemma continuous_uncurry_fderiv_homotopyOperatorIntegrand
    {f : Space → EuclideanSpace ℝ (Fin 3)} (hf : ContDiff ℝ 1 f) :
    Continuous (Function.uncurry (fun x t => fderiv ℝ (homotopyOperatorIntegrand f · t) x)) := by
  refine continuous_clm_apply.mpr ?_
  intro y
  suffices h1 : Continuous ((PiLp.continuousLinearEquiv 2 ℝ _).symm ∘
    (PiLp.continuousLinearEquiv 2 ℝ _) ∘
    (fun p : Space × ℝ => fderiv ℝ (homotopyOperatorIntegrand f · p.2) p.1 y)) by
    exact h1
  apply Continuous.comp (by fun_prop) ?_
  apply continuous_pi
  intro i
  change Continuous (fun p : Space × ℝ => fderiv ℝ (homotopyOperatorIntegrand f · p.2) p.1 y i)
  have hf := hf.differentiable (by simp)
  fin_cases i
  all_goals
  · simp [fderiv_homotopyOperatorIntegrand_apply_eq hf]
    fun_prop

private lemma hasFDerivAt_intervalIntegral_homotopyOperatorIntegrand
    {f : Space → EuclideanSpace ℝ (Fin 3)} (hf : ContDiff ℝ 1 f) (x₀ : Space) :
    HasFDerivAt (fun (x : Space) => ∫ (t : ℝ) in 0..1, homotopyOperatorIntegrand f x t ∂(volume))
      (∫ (t : ℝ) in 0..1, fderiv ℝ (homotopyOperatorIntegrand f · t) x₀ ∂(volume)) x₀ := by
  let F : Space → ℝ → EuclideanSpace ℝ (Fin 3) := homotopyOperatorIntegrand f
  let F' : Space → ℝ → Space →L[ℝ] EuclideanSpace ℝ (Fin 3) := fun x t => fderiv ℝ (F · t) x
  let s (x₀) : Set (Space) := Metric.closedBall x₀ 1
  obtain ⟨a, ha⟩ := IsCompact.exists_isMaxOn (s := s x₀ ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))
      (by exact (isCompact_closedBall x₀ 1).prod <|
        ConditionallyCompleteLinearOrder.isCompact_Icc 0 1)
      (f := fun (a : Space × ℝ) => ‖F' a.1 a.2‖)
      (by simp [s])
      (by
        apply (Continuous.comp ?_
          (continuous_uncurry_fderiv_homotopyOperatorIntegrand hf)).continuousOn
        change Continuous (@norm _ ContinuousLinearMap.toSeminormedAddCommGroup.toNorm)
        fun_prop)
  change HasFDerivAt (fun (x : Space) => ∫ (t : ℝ) in 0..1, F x t ∂(volume))
      (∫ (t : ℝ) in 0..1, F' x₀ t ∂(volume)) x₀
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (s := s x₀)
    (bound := fun t => ‖F' a.1 a.2‖)
  · exact Metric.closedBall_mem_nhds x₀ (by simp)
  · filter_upwards with x
    simp [F, homotopyOperatorIntegrand_eq]
    fun_prop
  · exact intervalIntegrable_homotopyOperatorIntegrand (hf.differentiable (by simp)) x₀
  · refine IntervalIntegrable.aestronglyMeasurable' ?_
    simp only [zero_le_one, sup_of_le_right, inf_of_le_left]
    apply Continuous.intervalIntegrable
    exact Continuous.uncurry_left x₀ (continuous_uncurry_fderiv_homotopyOperatorIntegrand hf)
  · filter_upwards with t
    intro h x hx
    have hx2 := ha.2
    rw [isMaxOn_iff] at hx2
    apply hx2 (x, t)
    simp at h
    grind
  · apply Continuous.intervalIntegrable
    fun_prop
  · filter_upwards with t
    intro h x hx
    dsimp [F', F]
    apply (differentiable_homotopyOperatorIntegrand_space _ _).differentiableAt.hasFDerivAt
    exact hf.differentiable (by simp)

private lemma deriv_intervalIntegral_homotopyOperatorIntegrand_sub
    (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 1 f) (i j k m : Fin 3) (x₀ : Space) :
    ∂[i] (fun x => (∫ (t : ℝ) in 0..1, homotopyOperatorIntegrand f x t ∂(volume)) k) x₀
    - ∂[j] (fun x => (∫ (t : ℝ) in 0..1, homotopyOperatorIntegrand f x t ∂(volume)) m) x₀ =
    ∫ (t : ℝ) in 0..1, (fderiv ℝ (homotopyOperatorIntegrand f · t) x₀ (basis i) k -
    fderiv ℝ (homotopyOperatorIntegrand f · t) x₀ (basis j) m) ∂(volume) := by
  let F : Space → ℝ → EuclideanSpace ℝ (Fin 3) := homotopyOperatorIntegrand f
  let F' : Space → ℝ → Space →L[ℝ] EuclideanSpace ℝ (Fin 3) := fun x t => fderiv ℝ (F · t) x
  have F'_continuous : Continuous (Function.uncurry F') := by
    exact continuous_uncurry_fderiv_homotopyOperatorIntegrand (hf)
  have hfderiv (x₀ : Space) : HasFDerivAt (fun (x : Space) => ∫ (t : ℝ) in 0..1, F x t ∂(volume))
      (∫ (t : ℝ) in 0..1, F' x₀ t ∂(volume)) x₀ := by
    exact hasFDerivAt_intervalIntegral_homotopyOperatorIntegrand (hf) x₀
  have F'_apply_apply (x₀ : Space) (y : Space) (i : Fin 3) :
      ((∫ (t : ℝ) in 0..1, F' x₀ t) y).ofLp i =
      (∫ (t : ℝ) in 0..1, F' x₀ t y i) := by
    trans ((∫ (t : ℝ) in 0..1, F' x₀ t y)).ofLp i
    · rw [ContinuousLinearMap.intervalIntegral_apply]
      apply Continuous.intervalIntegrable
      fun_prop
    · rw [intervalIntegral.integral_of_le (by simp), intervalIntegral.integral_of_le (by simp)]
      rw [MeasureTheory.eval_integral_piLp]
      intro i
      apply MeasureTheory.IntegrableOn.integrable
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le]
      apply Continuous.intervalIntegrable
      fun_prop
      simp
  repeat rw [Space.deriv_euclid, Space.deriv, (hfderiv x₀).fderiv]
  rotate_left
  · exact fun x => (hfderiv x).differentiableAt
  · exact fun x => (hfderiv x).differentiableAt
  rw [F'_apply_apply, F'_apply_apply, ← intervalIntegral.integral_sub]
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

lemma eq_neg_curl_of_div_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 1 f)
    (hdiv : ∇ ⬝ f = 0) :
    f = - curl (fun x => ∫ (t : ℝ) in 0..1, (t • basis.repr x) ⨯ₑ₃ f (t • x) ∂(volume)) := by
  have f_differentiable : Differentiable ℝ f := hf.differentiable (by simp)
  have fderiv_f_t (x : Space) (t : ℝ)
      (i : Fin 3) : (fderiv ℝ (fun t => (f (t • x)).ofLp i) t) 1 = fderiv ℝ f (t • x) x i := by
    change (fderiv ℝ (EuclideanSpace.proj i ∘ f ∘ fun (t : ℝ) => t • x) t) 1 = _
    rw [fderiv_comp _ (by fun_prop) (by fun_prop), fderiv_comp _ (by fun_prop) (by fun_prop),
      fderiv_fun_smul (by fun_prop) (by fun_prop)]
    simp only [Function.comp_apply, ContinuousLinearMap.fderiv, fderiv_fun_const, Pi.zero_apply,
      fderiv_fun_id, ContinuousLinearMap.coe_comp, smul_zero, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_id', id_eq, one_smul, zero_add, PiLp.proj_apply]
  have hi (x : Space) (i : Fin 3) : ∫ (t : ℝ) in 0..1, (t * f (t • x) i * 2) -
        t * (- fderiv ℝ f (t • x) (t • x)) i ∂(volume) = f x i := by
    trans ∫ (t : ℝ) in 0..1, fderiv ℝ (fun t => t ^ 2 * f (t • x) i) t 1 ∂(volume)
    · congr
      funext t
      rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
      simp [fderiv_f_t]
      ring
    simp only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul]
    rw [intervalIntegral.integral_deriv_eq_sub (by fun_prop)]
    simp only [one_pow, one_smul, one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_smul, zero_mul, sub_zero]
    · apply Continuous.intervalIntegrable
      fun_prop
  change f = -curl fun x => ∫ (t : ℝ) in 0..1, homotopyOperatorIntegrand f x t
  ext x i
  fin_cases i <;> symm
  all_goals
    simp [curl]
    rw [deriv_intervalIntegral_homotopyOperatorIntegrand_sub _ hf]
    simp [fderiv_homotopyOperatorIntegrand_apply_eq (hf.differentiable (by simp)), basis_apply]
    rw [← hi]
    congr
    funext t
    have hdiv : div f (t • x) = 0 := by simp [hdiv]
    rw [div_eq_sum_fderiv _ (by fun_prop)] at hdiv
    simp [Fin.sum_univ_three] at hdiv
    have hx : x = ∑ i, basis.repr x i • basis i :=
      Eq.symm (OrthonormalBasis.sum_repr basis x)
    conv_rhs =>
      enter [2, 2,1, 1, 2]
      rw [hx]
  · linear_combination (norm := {simp [Fin.sum_univ_three]; ring}) - t ^ 2 * x 0 * hdiv
  · linear_combination (norm := {simp [Fin.sum_univ_three]; ring}) - t ^ 2 * x 1 * hdiv
  · linear_combination (norm := {simp [Fin.sum_univ_three]; ring}) - t ^ 2 * x 2 * hdiv

lemma exists_curl_of_div_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 1 f)
    (hdiv : ∇ ⬝ f = 0) :
    ∃ g : Space → EuclideanSpace ℝ (Fin 3), f = curl g ∧ Differentiable ℝ g := by
  suffices hneg : ∃ g: Space → EuclideanSpace ℝ (Fin 3), f = - curl g ∧ Differentiable ℝ g by
    obtain ⟨g, hcurl, hdifferentiable⟩ := hneg
    use -g
    subst f
    simp_all
    rw [curl_neg]
    fun_prop
  use fun x => ∫ (t : ℝ) in 0..1, homotopyOperatorIntegrand f x t ∂(volume)
  exact ⟨eq_neg_curl_of_div_zero f hf hdiv,
    fun x => (hasFDerivAt_intervalIntegral_homotopyOperatorIntegrand hf x).differentiableAt⟩

TODO "Generalize the statement that a div-free field is a curl
  to time-dependent fields."

/-!

### A.10. A curl-free field is a gradient

We show that if the curl of a function is zero, then it is equal to the gradient of some function.
The key lemma here is
`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`, which is
a more general version of this result in Mathlib. We turn this here into something
more familiar, to the physicists via `deriv_comm_of_curl_zero`.

-/

lemma deriv_comm_of_curl_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : Differentiable ℝ f)
    (hcurl : curl f = 0) (x : Space) (i j : Fin 3) :
    ∂[i] f x j = ∂[j] f x i := by
  fin_cases i <;> fin_cases j
  any_goals rfl
  all_goals
    simp only [Fin.reduceFinMk, Fin.isValue, Fin.zero_eta]
    rw [← deriv_euclid (by fun_prop), ← deriv_euclid (by fun_prop)]
    have hcurl' (i : Fin 3) : curl f x i = 0 := by simp [hcurl]
  · specialize hcurl' 2
    simp [curl] at hcurl'
    linear_combination (norm := ring_nf) hcurl'
  · specialize hcurl' 1
    simp [curl] at hcurl'
    linear_combination (norm := ring_nf) -hcurl'
  · specialize hcurl' 2
    simp [curl] at hcurl'
    linear_combination (norm := ring_nf) -hcurl'
  · specialize hcurl' 0
    simp [curl] at hcurl'
    linear_combination (norm := ring_nf) hcurl'
  · specialize hcurl' 1
    simp [curl] at hcurl'
    linear_combination (norm := ring_nf) hcurl'
  · specialize hcurl' 0
    simp [curl] at hcurl'
    linear_combination (norm := ring_nf) -hcurl'

open InnerProductSpace
lemma exists_grad_of_curl_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : Differentiable ℝ f)
    (hcurl : curl f = 0) : ∃ g : Space → ℝ, f = grad g ∧ Differentiable ℝ g := by
  let s : Set (Space) := Set.univ
  have hs : Convex ℝ s := convex_univ
  have hso : IsOpen s := isOpen_univ
  let ω : Space → Space →L[ℝ] ℝ:= fun a => InnerProductSpace.toDual ℝ _ (basis.repr.symm (f a))
  have hω : DifferentiableOn ℝ ω s := by
    simp [ω]
    refine differentiableOn_univ.mpr ?_
    apply (InnerProductSpace.toDual ℝ (Space)).differentiable.fun_comp
    fun_prop
  have hω_fderiv (a x y : Space) : fderiv ℝ ω a x y =
      ⟪(basis.repr.symm (fderiv ℝ f a x)), y⟫_ℝ:= by
    calc _
      _ = (fderiv ℝ (InnerProductSpace.toDual ℝ _ ∘
        fun a => (basis.repr.symm (f a))) a x) y := by rfl
    rw [fderiv_comp _ (by exact
      (InnerProductSpace.toDual ℝ (Space)).differentiable.differentiableAt) (by fun_prop)]
    erw [(InnerProductSpace.toDual ℝ (Space)).fderiv]
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply]
    erw [InnerProductSpace.toDual_apply_apply]
    rw [fderiv_fun_comp _ (by fun_prop) (by fun_prop)]
    simp
  have hdω: ∀ a ∈ s, ∀ (x y : Space), ((fderiv ℝ ω a) x) y = ((fderiv ℝ ω a) y) x := by
    intro a ha x y
    rw [hω_fderiv, hω_fderiv]
    induction' y using basis_induction_on with i p1 p2 h1 h2 c p1 h1
    rotate_left
    · simp
    · simp [inner_add_left, inner_add_right, h1, h2]
    · simp [inner_smul_left, inner_smul_right, h1]
    induction' x using basis_induction_on with j p1 p2 h1 h2 c p1 h1
    rotate_left
    · simp
    · simp [inner_add_right, ← h1,← h2]
    · simp [inner_smul_right, ← h1]
    simp only [inner_basis, basis_repr_symm_apply]
    rw [← deriv_eq, ← deriv_eq]
    exact deriv_comm_of_curl_zero f hf hcurl a j i
  obtain ⟨g, hg⟩ := Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric hs hso (ω := ω) hω hdω
  use g
  simp [ω, ← hasGradientAt_iff_hasFDerivAt, s] at hg
  apply And.intro _ (fun x => (hg x).differentiableAt)
  ext1 x
  specialize hg x
  simpa using (HasGradientAt.unique (hg.differentiableAt.hasGradientAt_grad x) hg).symm

/-- A constructive form of the statement that if the curl of a function is zero,
  then it is equal to the grad of another function.

  In the context of e.g. electromagnetism the potential given by this lemma corresponds
  to that defined by the work done to move a unit charge from the origin to the
  point `x` along a straight line. -/
lemma eq_grad_integral_of_curl_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 1 f)
    (hcurl : curl f = 0) :
    f = grad (fun x => ∫ t in (0 : ℝ)..1, ⟪f (t • x), basis.repr x⟫_ℝ ∂(volume)) := by
  obtain ⟨g, ⟨rfl, hg⟩⟩ := exists_grad_of_curl_zero f
    (hf.differentiable (by simp)) (by simp [hcurl])
  suffices h1 : ContDiff ℝ 1 g by
    nth_rewrite 1 [eq_integral_grad h1]
    simp
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun x => ((toDual ℝ Space) (basis.repr.symm (∇ g x))), by fun_prop, fun x => ?_⟩
  exact hasGradientAt_iff_hasFDerivAt.mpr (DifferentiableAt.hasGradientAt_grad x (hg x))

TODO "Generalize the statement that a curl-free field is a gradient
  to time-dependent fields."

/-!

### A.11. The curl in terms of the Levi-Civita symbol

-/

open KroneckerDelta in
set_option backward.isDefEq.respectTransparency false in
/-- The components of the curl as a contraction with the Levi-Civita symbol,
`(∇ ⨯ f) x i = ∑ j k, ε_{ijk} ∂[j] fₖ x`. -/
lemma curl_eq_sum_leviCivitaSymbol (f : Space → EuclideanSpace ℝ (Fin 3))
    (x : Space) (i : Fin 3) :
    (∇ ⨯ f) x i = ∑ j, ∑ k, (leviCivitaSymbol ![i, j, k] : ℝ) * ∂[j] (fun y => f y k) x := by
  fin_cases i <;>
    simp only [curl, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd,
      Fin.sum_univ_three, leviCivitaSymbol_eq_det, Matrix.det_fin_three, kroneckerDelta,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] <;>
    norm_num <;>
    ring

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
      toFun dfdx := WithLp.toLp 2 fun i => dfdx (basis (i+2)) (i+1) - dfdx (basis (i+1)) (i+2)
      map_add' v1 v2 := by
        ext i
        simp only [Fin.isValue, _root_.add_apply, PiLp.add_apply]
        ring
      map_smul' a v := by
        ext i
        simp only [Fin.isValue, FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        ring
      cont := by
        apply Continuous.comp
        · fun_prop
        rw [continuous_pi_iff]
        fun_prop
        }
    curl.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by simp
  map_smul' a f := by simp

@[inherit_doc distCurl]
macro (name := distCurlNotation) "∇ᵈ" "⨯" f:term:100 : term => `(distCurl $f)

/-!

### B.1. The components of the curl

-/

lemma distCurl_coord_apply {i : Fin 3}
    (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    (∇ᵈ ⨯ f) η i = - f (SchwartzMap.evalCLM ℝ Space ℝ (basis (i+2)) (fderivCLM ℝ Space ℝ η)) (i+1)
    + f (SchwartzMap.evalCLM ℝ Space ℝ (basis (i+1)) (fderivCLM ℝ Space ℝ η)) (i+2) := by
  simp [distCurl, fderivD_apply]

lemma distCurl_apply_one (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    (∇ᵈ ⨯ f) η 1 = - f (SchwartzMap.evalCLM ℝ Space ℝ (basis 0) (fderivCLM ℝ Space ℝ η)) 2
    + f (SchwartzMap.evalCLM ℝ Space ℝ (basis 2) (fderivCLM ℝ Space ℝ η)) 0 := by
  simpa using distCurl_coord_apply (i := 1) f η

lemma distCurl_apply_two (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    (∇ᵈ ⨯ f) η 2 = - f (SchwartzMap.evalCLM ℝ Space ℝ (basis 1) (fderivCLM ℝ Space ℝ η)) 0
    + f (SchwartzMap.evalCLM ℝ Space ℝ (basis 0) (fderivCLM ℝ Space ℝ η)) 1 := by
  simpa using distCurl_coord_apply (i := 2) f η

/-!

### B.2. Basic equalities

-/

lemma distCurl_apply (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    (∇ᵈ ⨯ f) η = WithLp.toLp 2 fun i =>
      - f (SchwartzMap.evalCLM ℝ Space ℝ (basis (i+2)) (fderivCLM ℝ Space ℝ η)) (i+1)
      + f (SchwartzMap.evalCLM ℝ Space ℝ (basis (i+1)) (fderivCLM ℝ Space ℝ η)) (i+2) := by
  ext i
  simp [distCurl_coord_apply]

/-!

### B.3. The curl of a grad is zero

-/

/-- The curl of a grad is equal to zero. -/
@[simp]
lemma distCurl_distGrad_eq_zero (f : (Space) →d[ℝ] ℝ) :
    ∇ᵈ ⨯ (∇ᵈ f) = 0 := by
  ext η i
  simp only [distCurl_coord_apply, Fin.isValue, _root_.zero_apply, PiLp.zero_apply]
  rw [distGrad_eq_sum_basis, distGrad_eq_sum_basis]
  simp only [Fin.isValue, neg_smul, Finset.sum_neg_distrib, PiLp.neg_apply, WithLp.ofLp_sum,
    WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    neg_neg]
  rw [← map_neg, ← map_add, ← ContinuousLinearMap.map_zero f]
  congr
  ext x
  simp only [Fin.isValue, _root_.add_apply, _root_.neg_apply, _root_.zero_apply]
  rw [schwartMap_fderiv_comm]
  simp

end Space
