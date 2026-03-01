/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.SpaceAndTime.Space.CrossProduct
import PhysLean.SpaceAndTime.TimeAndSpace.Basic
/-!

# Wave equation

## i. Overview

In this module we define the wave equation in `d`-dimensional Euclidean space,
and prove that plane waves are solutions to the wave equation.
By a plne wave we mean a function of the form `f(t, x) = f₀(⟪x, s⟫_ℝ - c * t)` where
`s` is a direction vector and `c` is the propagation speed.

## ii. Key results

- `WaveEquation`: The general form of the wave equation where `c` is the propagation speed.
- `planeWave`: A vector-valued plane wave travelling in the direction of `s` with
  propagation speed `c`.
- `planeWave_waveEquation`: The plane wave satisfies the wave equation.

## iii. Table of contents

- A. The wave equation
- B. Plane wave solutions
  - B.1. Definition of a plane wave
  - B.2. Differentiablity conditions
  - B.3. Time derivatives of plane waves
  - B.4. Space derivatives of plane waves
  - B.5. Laplacian of plane waves
  - B.6. Plane waves satisfy the wave equation
- C. Old lemmas used throughout files

## iv. References

-/

namespace ClassicalMechanics

open Space
open Time
open InnerProductSpace

/-!

## A. The wave equation

-/

/-- The general form of the wave equation where `c` is the propagation speed. -/
def WaveEquation {d} (f : Time → Space d → EuclideanSpace ℝ (Fin d))
    (t : Time) (x : Space d) (c : ℝ) : Prop :=
    c^2 • Δ (f t) x - ∂ₜ (fun t => (∂ₜ (fun t => f t x) t)) t = 0

/-!

## B. Plane wave solutions

-/

/-!

### B.1. Definition of a plane wave

-/

/-- A vector-valued plane wave travelling in the direction of `s` with propagation speed `c`. -/
noncomputable def planeWave (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    (c : ℝ) (s : Direction d) : Time → Space d → EuclideanSpace ℝ (Fin d) :=
    fun t x => f₀ (⟪x, s.unit⟫_ℝ - c * t)

lemma planeWave_eq {d f₀ c x} {s : Direction d} :
    planeWave f₀ c s t x = f₀ (⟪x, s.unit⟫_ℝ - c * t) :=
  rfl

/-!

### B.2. Differentiablity conditions

-/

@[fun_prop]
lemma planeWave_differentiable_time {d f₀ c x} {s : Direction d}
    (h' : Differentiable ℝ f₀) :
    Differentiable ℝ (fun t => planeWave f₀ c s t x) := by
  simp only [planeWave_eq]
  apply Differentiable.comp
  · fun_prop
  · fun_prop

@[fun_prop]
lemma planeWave_differentiable_space {d f₀ c t} {s : Direction d}
    (h' : Differentiable ℝ f₀) :
    Differentiable ℝ (fun x => planeWave f₀ c s t x) := by
  simp only [planeWave_eq]
  apply Differentiable.comp
  · fun_prop
  · apply Differentiable.sub
    · refine Differentiable.inner ℝ ?_ ?_
      · fun_prop
      · fun_prop
    · fun_prop

@[fun_prop]
lemma planeWave_differentiable {s : Direction d}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin d)}
    (h' : Differentiable ℝ f₀) : Differentiable ℝ ↿(planeWave f₀ c s) := by
  unfold planeWave
  change Differentiable ℝ (f₀ ∘ fun ((t : Time), x) => (inner ℝ x s.unit - c * t))
  apply Differentiable.comp
  · fun_prop
  · apply Differentiable.sub
    · apply Differentiable.inner
      repeat fun_prop
    · fun_prop

/-!

### B.3. Time derivatives of plane waves

-/

lemma planeWave_time_deriv {d f₀ c x} {s : Direction d}
    (h' : Differentiable ℝ f₀) :
    ∂ₜ (planeWave f₀ c s · x) = -c • fun t => planeWave (fderiv ℝ f₀ · 1) c s t x := by
  ext t i
  rw [Time.deriv_eq]
  change fderiv ℝ (f₀ ∘ fun t : Time => (inner ℝ x s.unit - c * t)) t 1 i = _
  rw [fderiv_comp, fderiv_const_sub, fderiv_const_mul]
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_smulₛₗ,
    RingHom.id_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    neg_mul, neg_inj, mul_eq_mul_left_iff]
  left
  simp
  rfl
  repeat fun_prop

lemma planeWave_time_deriv_time_deriv {d f₀ c x} {s : Direction d}
    (h' : ContDiff ℝ 2 f₀) :
    ∂ₜ (∂ₜ (planeWave f₀ c s · x)) = c ^ 2 • fun t => planeWave (iteratedDeriv 2 f₀) c s t x := by
  conv_lhs =>
    enter [1, i]
    rw [planeWave_time_deriv (h'.differentiable (by simp))]
  ext t i
  rw [Time.deriv_eq, fderiv_const_smul (by fun_prop)]
  simp only [fderiv_eq_smul_deriv, one_smul, neg_smul, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← Time.deriv_eq, planeWave_time_deriv (by fun_prop)]
  simp only [fderiv_eq_smul_deriv, one_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, neg_mul,
    mul_neg, neg_neg]
  ring_nf
  suffices h : (fun x => _root_.deriv (fun x => _root_.deriv f₀ x) x) =
      fun x => iteratedDeriv 2 f₀ x by rw [h]
  funext x
  erw [iteratedDeriv_succ]
  simp only [iteratedDeriv_one]

/-!

### B.4. Space derivatives of plane waves

-/

open InnerProductSpace

lemma planeWave_space_deriv {d f₀ c} {s : Direction d}
    (h' : Differentiable ℝ f₀) (i : Fin d) :
    Space.deriv i (planeWave f₀ c s t) =
    s.unit i • fun x => planeWave (fderiv ℝ f₀ · 1) c s t x:= by
  ext x j
  rw [Space.deriv_eq]
  change fderiv ℝ
    (f₀ ∘ fun x : Space d => (inner ℝ x s.unit - c * t)) x (Space.basis i) j = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv,
    PiLp.smul_apply, smul_eq_mul, one_smul, Pi.smul_apply]
  rw [fderiv_sub_const]
  rw [fderiv_inner_apply]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
    fderiv_id', ContinuousLinearMap.coe_id', id_eq, basis_inner, zero_add, mul_eq_mul_left_iff]
  left
  simp [planeWave_eq]
  repeat fun_prop

lemma planeWave_apply_space_deriv {d f₀ c} {s : Direction d}
    (h' : Differentiable ℝ f₀) (i j : Fin d) :
    Space.deriv i (fun x => planeWave f₀ c s t x j) =
    s.unit i • fun x => planeWave (fderiv ℝ f₀ · 1) c s t x j := by
  funext x
  rw [Space.deriv_eq_fderiv_basis]
  change fderiv ℝ (EuclideanSpace.proj j ∘ fun x => (planeWave f₀ c s t x)) x (basis i) = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    PiLp.proj_apply, fderiv_eq_smul_deriv, one_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Space.deriv_eq_fderiv_basis, planeWave_space_deriv]
  rfl
  · fun_prop
  · fun_prop
  · fun_prop

lemma planeWave_space_deriv_space_deriv {d f₀ c} {s : Direction d}
    (h' : ContDiff ℝ 2 f₀) (i : Fin d) :
    Space.deriv i (Space.deriv i (planeWave f₀ c s t)) =
    s.unit i ^ 2 • fun x => planeWave (iteratedDeriv 2 f₀ ·) c s t x := by
  conv_lhs =>
    enter [2, j]
    rw [planeWave_space_deriv (h'.differentiable (by simp)) i]
  funext x
  rw [Space.deriv_eq_fderiv_basis, fderiv_const_smul]
  simp only [fderiv_eq_smul_deriv, one_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [← Space.deriv_eq_fderiv_basis, planeWave_space_deriv]
  simp only [fderiv_eq_smul_deriv, one_smul, Pi.smul_apply]
  rw [smul_smul]
  congr 1
  · exact Eq.symm (pow_two (s.unit i))
  · congr
    funext x
    rw [iteratedDeriv_succ]
    simp
  · fun_prop
  · fun_prop

lemma planeWave_apply_space_deriv_space_deriv {d f₀ c} {s : Direction d}
    (h' : ContDiff ℝ 2 f₀) (i j : Fin d) :
    Space.deriv i (Space.deriv i (fun x => planeWave f₀ c s t x j)) =
    (s.unit i) ^ 2 •fun x => planeWave (iteratedDeriv 2 f₀ ·) c s t x j := by
  conv_lhs =>
    enter [2, j]
    rw [planeWave_apply_space_deriv (h'.differentiable (by simp)) i]
  funext x
  rw [Space.deriv_eq_fderiv_basis, fderiv_const_smul]
  simp only [fderiv_eq_smul_deriv, one_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  rw [← Space.deriv_eq_fderiv_basis, planeWave_apply_space_deriv]
  simp only [fderiv_eq_smul_deriv, one_smul, Pi.smul_apply, smul_eq_mul]
  ring_nf
  suffices h : (fun x => _root_.deriv (fun x => _root_.deriv f₀ x) x) =
      fun x => iteratedDeriv 2 f₀ x by rw [h]
  ext x i
  erw [iteratedDeriv_succ']
  simp only [iteratedDeriv_one]
  repeat fun_prop

/-!

### B.5. Laplacian of plane waves

-/

lemma planeWave_laplacian {d f₀ c} {s : Direction d} (h' : ContDiff ℝ 2 f₀) :
    Δ (planeWave f₀ c s t) = fun x => planeWave (iteratedDeriv 2 f₀ ·) c s t x := by
  ext x j
  simp [laplacianVec, laplacian]
  conv_lhs =>
    enter [2, i]
    rw [planeWave_apply_space_deriv_space_deriv h']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_mul]
  simp

/-!

### B.6. Plane waves satisfy the wave equation

-/

/-- The plane wave satisfies the wave equation. -/
theorem planeWave_waveEquation (c : ℝ) (s : Direction d)
    (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (hf₀ : ContDiff ℝ 2 f₀) :
    ∀ t x, WaveEquation (planeWave f₀ c s) t x c := by
  intro t x
  rw [WaveEquation, planeWave_laplacian hf₀, planeWave_time_deriv_time_deriv hf₀]
  simp

/-!

## C. Old lemmas used throughout files

These lemmas will eventually be moved, renamed and/or replaced.

-/

lemma wave_differentiable {s : Direction d} {c : ℝ} {x : Space d} :
    DifferentiableAt ℝ (fun x => inner ℝ x s.unit - c * t) x := by
  apply DifferentiableAt.sub
  apply DifferentiableAt.inner
  repeat fun_prop

lemma wave_dx2 {u v : Fin d} {s : Direction d}
    {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)} {f₀'' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x' 1) (f₀'' x) x) :
    (fderiv ℝ (fun x' => (inner ℝ ((f₀' (inner ℝ x' s.unit - c * t)) (s.unit u))
    (EuclideanSpace.single v 1))) x) (Space.basis u)
    =
    inner ℝ ((s.unit u) ^ 2 • f₀'' (inner ℝ x s.unit - c * t) 1) (EuclideanSpace.single v 1) := by
  rw [fderiv_inner_apply]
  have hdi' : (fderiv ℝ (fun x' => (f₀' (inner ℝ x' s.unit - c * t))
      (s.unit u)) x) (Space.basis u)
      =
      (s.unit u) ^ 2 • (f₀'' (inner ℝ x s.unit - c * t) 1) := by
    change (fderiv ℝ ((fun x' => f₀' x' (s.unit u)) ∘
        fun x' => (inner ℝ x' s.unit - c * t)) x) (Space.basis u) = _
    rw [fderiv_comp, fderiv_fun_sub]
    simp only [fderiv_fun_const, Pi.ofNat_apply, sub_zero, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
    rw [fderiv_inner_apply]
    simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
    trans (fderiv ℝ (fun x' => (f₀' x') (s.unit u • 1)) (inner ℝ x s.unit - c * t)) (s.unit u • 1)
    simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
      basis_inner, zero_add, fderiv_eq_smul_deriv, smul_eq_mul, mul_one]
    conv_lhs =>
      enter [1, 2, x']
      rw [ContinuousLinearMap.map_smul]
    rw [ContinuousLinearMap.map_smul, fderiv_fun_const_smul, pow_two]
    rw [HasFDerivAt.fderiv (h'' (inner ℝ x s.unit - c * t))]
    change s.unit u • s.unit u • (f₀'' (inner ℝ x s.unit - c * t) 1) = _
    rw [← smul_assoc, smul_eq_mul]
    repeat fun_prop
    · conv_lhs =>
        enter [x]
        rw [← mul_one (s.unit u), ← smul_eq_mul, ContinuousLinearMap.map_smul]
      fun_prop
    · exact wave_differentiable
  rw [hdi']
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, inner_zero_right, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, zero_add]
  change DifferentiableAt ℝ ((fun x' => f₀' x' (s.unit u)) ∘
      (fun x => (inner ℝ x s.unit - c * t))) x
  apply DifferentiableAt.comp
  · conv_lhs =>
      enter [x]
      rw [← mul_one (s.unit u), ← smul_eq_mul, ContinuousLinearMap.map_smul]
    fun_prop
  · exact wave_differentiable
  · fun_prop

/-- If `f₀` is a function of `(inner ℝ x s - c * t)`, the fderiv of its components
with respect to spatial coordinates is equal to the corresponding component of
the propagation direction `s` times time derivative. -/
lemma space_fderiv_of_inner_product_wave_eq_space_fderiv
    {t : Time} {f₀ : ℝ → EuclideanSpace ℝ (Fin d)}
    {s : Direction d} {u v : Fin d} (h' : Differentiable ℝ f₀) :
    c * ((fun x' => (fderiv ℝ (fun x => inner ℝ (f₀ (inner ℝ x s.unit - c * t))
    (EuclideanSpace.single v 1)) x') ((Space.basis u))) x)
    =
    - s.unit u * ∂ₜ (fun t => f₀ (inner ℝ x s.unit - c * t)) t v := by
  simp [EuclideanSpace.inner_single_right]
  trans c * (fderiv ℝ (fun x => f₀ (⟪x, s.unit⟫_ℝ - c * t.val) v) x) (Space.basis u)
  · rfl
  erw [← Space.deriv_eq_fderiv_basis, planeWave_apply_space_deriv h' u v,
    planeWave_time_deriv h']
  simp only [fderiv_eq_smul_deriv, one_smul, Pi.smul_apply, smul_eq_mul, PiLp.smul_apply, neg_mul,
    mul_neg, neg_neg]
  ring

lemma time_differentiable_of_eq_planewave {s : Direction d}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin d)} {f : Time → Space d → EuclideanSpace ℝ (Fin d)}
    (h' : Differentiable ℝ f₀) (hf : f = planeWave f₀ c s) :
    Differentiable ℝ fun t => f t x := by
  rw [hf]
  unfold planeWave
  fun_prop

open Matrix

lemma crossProduct_time_differentiable_of_right_eq_planewave {s : Direction}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {f : Time → Space → EuclideanSpace ℝ (Fin 3)}
    (h' : Differentiable ℝ f₀) (hf : f = planeWave f₀ c s) :
    DifferentiableAt ℝ (fun t => Space.basis.repr s.unit ⨯ₑ₃ (f t x)) t := by
  rw [hf, crossProduct]
  unfold planeWave
  apply differentiable_euclid
  intro i
  fin_cases i <;>
  · simp only [Fin.reduceFinMk, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd,
    WithLp.equiv_apply, LinearMap.mk₂_apply, WithLp.equiv_symm_apply, PiLp.toLp_apply, cons_val]
    fun_prop

lemma crossProduct_differentiable_of_right_eq_planewave {s : Direction}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} (h' : Differentiable ℝ f₀) :
    DifferentiableAt ℝ (fun u => Space.basis.repr s.unit ⨯ₑ₃ (f₀ u)) u := by
  rw [crossProduct]
  apply Differentiable.differentiableAt
  apply Differentiable.comp
  · simp only [WithLp.equiv_symm_apply]
    rw [@differentiable_euclidean]
    intro i
    simp only
    fun_prop
  apply differentiable_pi''
  intro i
  fin_cases i <;>
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, WithLp.equiv_apply,
    Fin.reduceFinMk, LinearMap.mk₂_apply, cons_val]
    fun_prop

lemma wave_fderiv_inner_eq_inner_fderiv_proj {f₀ : ℝ → EuclideanSpace ℝ (Fin d)}
    {s : Direction d} {i : Fin d} (h' : Differentiable ℝ f₀) :
    ∀ x y, s.unit i * (fderiv ℝ (fun x => f₀ (inner ℝ x s.unit - c * t)) x) y i
    =
    inner ℝ y s.unit * (fderiv ℝ (fun x => f₀ (inner ℝ x s.unit - c * t) i) x)
    (Space.basis i) := by
  intro x y
  change _ =
      inner ℝ y s.unit * (fderiv ℝ ((EuclideanSpace.proj i) ∘
      fun x => f₀ (inner ℝ x s.unit - c * t)) x) (Space.basis i)
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    PiLp.proj_apply]
  change s.unit i * (fderiv ℝ (f₀ ∘ fun x => (inner ℝ x s.unit - c * t)) x) y i =
      inner ℝ y s.unit * (fderiv ℝ (f₀ ∘ fun x => (inner ℝ x s.unit - c * t)) x)
      (Space.basis i) i
  rw [fderiv_comp, fderiv_fun_sub]
  simp only [fderiv_fun_const, Pi.zero_apply, sub_zero, ContinuousLinearMap.coe_comp',
    Function.comp_apply, differentiableAt_fun_id, differentiableAt_const, fderiv_inner_apply,
    ContinuousLinearMap.zero_apply, inner_zero_right, fderiv_id', ContinuousLinearMap.coe_id',
    id_eq, zero_add]
  simp only [fderiv_eq_smul_deriv, PiLp.smul_apply, smul_eq_mul, basis_inner]
  rw [← mul_one (s.unit i), ← smul_eq_mul (s.unit i)]
  rw [← mul_one (inner ℝ y s.unit), ← smul_eq_mul (inner ℝ y s.unit)]
  simp only [smul_eq_mul, mul_comm, one_mul, ← mul_assoc]
  repeat fun_prop

end ClassicalMechanics
