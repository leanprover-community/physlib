/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Modified.MondFieldTheory
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Euler-Lagrange residual of the AQUAL action

## i. Overview

This module assembles the Euler-Lagrange residual of the AQUAL action in a
one-dimensional model and proves that its vanishing is exactly the MOND field
equation.  The action density depends on the field and its first derivative;
the residual is `dL/dphi - d/dx (dL/dphi')`, with the conjugate momentum
`-(1/4 pi G) mu (|phi'|/a0) phi'` and its derivative written through the free
function's first two derivatives.

The two partial derivatives of the density and the derivative of the conjugate
momentum along the slice are computed, and the algebraic assembly and the
equivalence with `IsAqualSolution` are proved.  A finite-graph version of the
variational derivation is also formalised: the action is a sum over links, its
first variation is computed, summation by parts converts it to a site sum, and
stationarity under all variations vanishing on the boundary is proved equivalent
to the discrete Euler-Lagrange equation at every interior site.  On an interval,
integration by parts and the fundamental lemma of the calculus of variations are
proved.  The Poisson-limit action is differentiated under the integral, the
nonlinear density has a pointwise chain rule for an arbitrary free function and
an interval derivative under `C^1` regularity, and the discrete residual of a
sampled profile is bridged to the continuum residual.  The symmetric second
difference tends to the second derivative for `C^2` profiles, and the whole-line
action follows from the interval one under compact support.  The free function carries
its derivative data and the identification `F' = mu ∘ sqrt` as hypotheses.

## ii. Key results

- `AqualFreeFunction` : the free function with `F' = mu ∘ sqrt` and its two
  derivative facts.
- `aqualLagrangianDensity1D` : the action density at a point.
- `aqualLagrangianDensity1D_deriv_phi`, `..._deriv_phi'` : the two partial
  derivatives, `-rho` and `-(a0^2/8 pi G) F' (2 phi' / a0^2)`.
- `aqualMomentumDensity`, `aqualMomentumDensity_deriv` : the conjugate momentum
  and its derivative along the slice.
- `aqualDivergence1D` : `d/dx (mu (|phi'|/a0) phi')` through `F'` and `F''`.
- `aqualEulerLagrangeResidual_eq` : the residual is the AQUAL residual divided
  by `4 pi G`.
- `aqual_euler_lagrange_iff` : stationarity is the MOND field equation.
- `sum_link_mul_difference` : summation by parts on a finite graph.
- `discrete_stationary_iff` : stationarity of the discrete action is the
  discrete Euler-Lagrange equation away from a chosen Dirichlet set.
- `quadraticProfile_stationary` : the exact quadratic solution on a three-site
  path.
- `aqual_first_variation_eq_integral_residual` : the continuum
  integration-by-parts step for the first-variation integral.
- `aqual_fundamental_lemma` : a continuous residual orthogonal to every
  endpoint-vanishing test function vanishes in the interior.
- `quadraticProfileN_residual` : the general-path quadratic solution.
- `hasDerivAt_aqualPoissonAction` : differentiation under the interval
  integral for the Poisson-limit action.
- `aqualLagrangianDensity1D_hasDerivAt_variation`,
  `hasDerivAt_aqualAction1D` : the pointwise and interval variations for an
  arbitrary nonlinear free function.
- `sampledPath_residual_eq`, `sampledPath_residual_tendsto` : the discrete
  residual of a sampled profile and its continuum limit.
- `secondDifference_tendsto`, `sampledPath_residual_tendsto_of_contDiff` : the
  `C^2` Taylor limit and the unconditional fixed-site residual convergence.
- `hasDerivAt_aqualAction1D_of_hasDerivAt`,
  `hasDerivAt_aqualActionLine_of_support` : the global-derivative and
  compact-support whole-line versions.

## iii. Table of contents

- A. The free function and the one-dimensional density
- B. The residual and stationarity
- C. A discrete variational derivation
- D. A worked example on a three-site path
- E. The continuum integration-by-parts step
- F. The fundamental lemma of the calculus of variations
- G. The general path
- H. Differentiation under the interval integral
- I. The full nonlinear free-function variation
- J. From the discrete residual to the continuum residual

## iv. References

* J. Bekenstein, M. Milgrom, ApJ 286 (1984) 7.
* M. Milgrom, ApJ 270 (1983) 365.
-/

@[expose] public section

namespace GeneralRelativity

/-! ## A. The free function and the one-dimensional density -/

/-- The free function of the AQUAL action with its first two derivatives and the
identification `F' = mu ∘ sqrt` that makes the Euler-Lagrange equation the MOND
equation.  The derivative facts are hypotheses: they express the chain rule for
a specified `F`, not the variation itself. -/
structure AqualFreeFunction where
  /-- The free function `F`. -/
  F : ℝ → ℝ
  /-- Its first derivative. -/
  F' : ℝ → ℝ
  /-- Its second derivative. -/
  F'' : ℝ → ℝ
  /-- The first derivative is `F'` away from zero. -/
  hasDeriv : ∀ y : ℝ, 0 < y → HasDerivAt F (F' y) y
  /-- The second derivative is `F''` away from zero. -/
  hasDeriv' : ∀ y : ℝ, 0 < y → HasDerivAt F' (F'' y) y
  /-- The interpolating identification `F'(y) = mu (sqrt y)`. -/
  interpolating : ∀ y : ℝ, 0 < y → F' y = mondMu (Real.sqrt y)

/-- The AQUAL action density in a one-dimensional model at a point:
`-(a0^2 / (8 pi G)) F(phi'^2 / a0^2) - rho phi`. -/
noncomputable def aqualLagrangianDensity1D (a0 G : ℝ) (F : ℝ → ℝ) (rho phi phi' : ℝ) : ℝ :=
  -(a0 ^ 2 / (8 * Real.pi * G)) * F (phi' ^ 2 / a0 ^ 2) - rho * phi

/-- The conjugate momentum to the field in the one-dimensional model:
`-(1 / (4 pi G)) F'(phi'^2 / a0^2) phi'`, which is `-(1 / (4 pi G)) mu (|phi'|/a0) phi'`. -/
noncomputable def aqualMomentumDensity (a0 G : ℝ) (F' : ℝ → ℝ) (phi' : ℝ → ℝ) : ℝ → ℝ :=
  fun x => -(1 / (4 * Real.pi * G)) * F' (phi' x ^ 2 / a0 ^ 2) * phi' x

/-! ## B. The residual and stationarity -/

/-- The one-dimensional divergence `d/dx [mu (|phi'|/a0) phi']`, written through
`F'` and `F''`. -/
noncomputable def aqualDivergence1D (a0 : ℝ) (phi' phi'' : ℝ) (F' F'' : ℝ → ℝ) : ℝ :=
  F' (phi' ^ 2 / a0 ^ 2) * phi'' +
    F'' (phi' ^ 2 / a0 ^ 2) * (2 * phi' * phi'' / a0 ^ 2) * phi'

/-- The Euler-Lagrange residual `dL/dphi - d/dx (dL/dphi')` in the
one-dimensional model, assembled from `dL/dphi = -rho` and the derivative of the
conjugate momentum. -/
noncomputable def aqualEulerLagrangeResidual (a0 G rho phi' phi'' : ℝ)
    (F' F'' : ℝ → ℝ) : ℝ :=
  -rho + aqualDivergence1D a0 phi' phi'' F' F'' / (4 * Real.pi * G)

/-- The Euler-Lagrange residual is the AQUAL residual divided by `4 pi G`. -/
lemma aqualEulerLagrangeResidual_eq (a0 G rho phi' phi'' : ℝ) (F' F'' : ℝ → ℝ)
    (hG : G ≠ 0) :
    aqualEulerLagrangeResidual a0 G rho phi' phi'' F' F'' =
      (aqualDivergence1D a0 phi' phi'' F' F'' - 4 * Real.pi * G * rho) /
        (4 * Real.pi * G) := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h4 : 4 * Real.pi * G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hG
  unfold aqualEulerLagrangeResidual
  field_simp
  ring

/-- Stationarity of the one-dimensional AQUAL action is the MOND field equation,
with the one-dimensional divergence playing the role of `div (mu grad phi)`. -/
lemma aqual_euler_lagrange_iff (a0 G rho phi' phi'' : ℝ) (F' F'' : ℝ → ℝ)
    (hG : G ≠ 0) :
    aqualEulerLagrangeResidual a0 G rho phi' phi'' F' F'' = 0 ↔
      IsAqualSolution G rho (aqualDivergence1D a0 phi' phi'' F' F'') := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h4 : 4 * Real.pi * G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hG
  constructor
  · intro h
    refine IsAqualSolution.mk ?_
    unfold aqualFieldResidual
    unfold aqualEulerLagrangeResidual at h
    have hd : aqualDivergence1D a0 phi' phi'' F' F'' / (4 * Real.pi * G) = rho := by
      linarith
    have hm : aqualDivergence1D a0 phi' phi'' F' F'' = rho * (4 * Real.pi * G) :=
      (div_eq_iff h4).mp hd
    rw [hm]
    ring
  · intro h
    unfold aqualEulerLagrangeResidual
    have hd : aqualDivergence1D a0 phi' phi'' F' F'' = 4 * Real.pi * G * rho := by
      have := h.field_eq
      unfold aqualFieldResidual at this
      linarith
    rw [hd]
    field_simp
    ring

/-- With the free function's derivative data, stationarity of the
one-dimensional AQUAL action is the MOND field equation. -/
lemma aqualFreeFunction_stationary_iff (A : AqualFreeFunction) (a0 G rho phi' phi'' : ℝ)
    (hG : G ≠ 0) :
    aqualEulerLagrangeResidual a0 G rho phi' phi'' A.F' A.F'' = 0 ↔
      IsAqualSolution G rho (aqualDivergence1D a0 phi' phi'' A.F' A.F'') :=
  aqual_euler_lagrange_iff a0 G rho phi' phi'' A.F' A.F'' hG

/-- The partial derivative of the density with respect to the field is `-rho`. -/
lemma aqualLagrangianDensity1D_deriv_phi (a0 G : ℝ) (F : ℝ → ℝ) (rho phi phi' : ℝ) :
    deriv (fun p : ℝ => aqualLagrangianDensity1D a0 G F rho p phi') phi = -rho := by
  simp [aqualLagrangianDensity1D]

/-- The partial derivative of the density with respect to the field derivative is
`-(a0^2 / (8 pi G)) F'(phi'^2/a0^2) (2 phi' / a0^2)`. -/
lemma aqualLagrangianDensity1D_deriv_phi' (a0 G : ℝ) (F F' : ℝ → ℝ) (rho phi phi' : ℝ)
    (hF : HasDerivAt F (F' (phi' ^ 2 / a0 ^ 2)) (phi' ^ 2 / a0 ^ 2)) :
    deriv (fun q : ℝ => aqualLagrangianDensity1D a0 G F rho phi q) phi' =
      -(a0 ^ 2 / (8 * Real.pi * G)) * F' (phi' ^ 2 / a0 ^ 2) * (2 * phi' / a0 ^ 2) := by
  have hd : deriv (fun q : ℝ => aqualLagrangianDensity1D a0 G F rho phi q) phi'
      = -(a0 ^ 2 / (8 * Real.pi * G)) * deriv (fun q : ℝ => F (q ^ 2 / a0 ^ 2)) phi' := by
    simp [aqualLagrangianDensity1D]
  have hg : DifferentiableAt ℝ (fun q : ℝ => q ^ 2 / a0 ^ 2) phi' := by fun_prop
  have hcomp : deriv (fun q : ℝ => F (q ^ 2 / a0 ^ 2)) phi'
      = deriv F (phi' ^ 2 / a0 ^ 2) * deriv (fun q : ℝ => q ^ 2 / a0 ^ 2) phi' := by
    simpa [Function.comp_def] using deriv_comp phi' hF.differentiableAt hg
  have hdg : deriv (fun q : ℝ => q ^ 2 / a0 ^ 2) phi' = 2 * phi' / a0 ^ 2 := by simp
  rw [hd, hcomp, hF.deriv, hdg]
  ring

/-- The derivative along the slice of the conjugate momentum, in terms of `F'`
and `F''`. -/
lemma aqualMomentumDensity_deriv (a0 G : ℝ) (F' F'' : ℝ → ℝ) (φ ψ : ℝ → ℝ) (x : ℝ)
    (hφ : HasDerivAt φ (ψ x) x)
    (hF : HasDerivAt F' (F'' (φ x ^ 2 / a0 ^ 2)) (φ x ^ 2 / a0 ^ 2)) :
    deriv (fun y => aqualMomentumDensity a0 G F' φ y) x =
      -(1 / (4 * Real.pi * G)) *
        (F'' (φ x ^ 2 / a0 ^ 2) * (2 * φ x * ψ x / a0 ^ 2) * φ x +
          F' (φ x ^ 2 / a0 ^ 2) * ψ x) := by
  have hφdiff : DifferentiableAt ℝ φ x := hφ.differentiableAt
  have hgdiff : DifferentiableAt ℝ (fun y => φ y ^ 2 / a0 ^ 2) x := by
    have h1 : DifferentiableAt ℝ (fun y => φ y ^ 2) x := hφdiff.pow 2
    exact h1.div_const (a0 ^ 2)
  have hcomp : deriv (fun y => F' (φ y ^ 2 / a0 ^ 2)) x
      = F'' (φ x ^ 2 / a0 ^ 2) * deriv (fun y => φ y ^ 2 / a0 ^ 2) x := by
    have h := deriv_comp x hF.differentiableAt hgdiff
    simpa [Function.comp_def, hF.deriv] using h
  have hdg : deriv (fun y => φ y ^ 2 / a0 ^ 2) x = 2 * φ x * ψ x / a0 ^ 2 := by
    have h2 : deriv (fun y => φ y ^ 2) x = 2 * φ x * ψ x := by
      have h := deriv_comp x (by fun_prop : DifferentiableAt ℝ (fun z : ℝ => z ^ 2) (φ x))
        hφdiff
      simpa [Function.comp_def, hφ.deriv] using h
    have h := deriv_div_const (c := fun y => φ y ^ 2) (d := a0 ^ 2) (x := x)
    rw [h, h2]
  have hf : DifferentiableAt ℝ
      (fun y => -(1 / (4 * Real.pi * G)) * F' (φ y ^ 2 / a0 ^ 2)) x := by
    have h := hF.differentiableAt.comp x hgdiff
    exact h.const_mul _
  have hfun : (fun y => aqualMomentumDensity a0 G F' φ y)
      = (fun y => -(1 / (4 * Real.pi * G)) * F' (φ y ^ 2 / a0 ^ 2)) * φ := rfl
  rw [hfun, deriv_mul hf hφdiff, deriv_const_mul_field, hcomp, hdg, hφ.deriv]
  ring

/-! ## C. A discrete variational derivation -/

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The action of the one-dimensional model on a finite graph with link length
`h`, for the free function `F(s) = s`, whose Euler-Lagrange equation is the
Poisson equation.  The measure `h` multiplies both the gradient and the source
term. -/
noncomputable def discreteAction (a b : E → V) (G h : ℝ) (ρ φ : V → ℝ) : ℝ :=
  -(1 / (8 * Real.pi * G)) * (∑ e : E, (φ (b e) - φ (a e)) ^ 2 / h)
    - h * ∑ x : V, ρ x * φ x

/-- The divergence of a link field: the sum of the incoming links minus the sum
of the outgoing links at a site. -/
noncomputable def discreteDivergence (a b : E → V) (d : E → ℝ) (x : V) : ℝ :=
  (∑ e : E, if b e = x then d e else 0) - ∑ e : E, if a e = x then d e else 0

/-- Summation by parts on a finite graph: the link pairing of a difference with
a link field equals the site pairing of the field with the divergence. -/
lemma sum_link_mul_difference (a b : E → V) (d : E → ℝ) (v : V → ℝ) :
    (∑ e : E, d e * (v (b e) - v (a e)))
      = ∑ x : V, v x * discreteDivergence a b d x := by
  have hb : (∑ x : V, v x * (∑ e : E, if b e = x then d e else 0))
      = ∑ e : E, d e * v (b e) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single (b e)]
    · simp [mul_comm]
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hmem
      exact absurd (Finset.mem_univ (b e)) hmem
  have ha : (∑ x : V, v x * (∑ e : E, if a e = x then d e else 0))
      = ∑ e : E, d e * v (a e) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single (a e)]
    · simp [mul_comm]
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hmem
      exact absurd (Finset.mem_univ (a e)) hmem
  simp only [discreteDivergence]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hb, ha]

/-- The link momentum of the discrete model,
`(phi (b e) - phi (a e)) / (4 pi G h)`. -/
noncomputable def discreteMomentum (a b : E → V) (G h : ℝ) (φ : V → ℝ) : E → ℝ :=
  fun e => (φ (b e) - φ (a e)) / (4 * Real.pi * G * h)

/-- The discrete Euler-Lagrange residual at a site. -/
noncomputable def discreteResidual (a b : E → V) (G h : ℝ) (ρ φ : V → ℝ) (x : V) : ℝ :=
  discreteDivergence a b (discreteMomentum a b G h φ) x + h * ρ x

/-- The first variation of the discrete action in the direction `v`. -/
noncomputable def discreteFirstVariation (a b : E → V) (G h : ℝ) (ρ φ v : V → ℝ) : ℝ :=
  -∑ e : E, (1 / (4 * Real.pi * G)) * (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h
    - h * ∑ x : V, ρ x * v x

/-- The first variation is minus the site sum of the variation against the
discrete residual; this is summation by parts followed by collecting terms. -/
lemma discreteFirstVariation_eq_neg_sum (a b : E → V) (G h : ℝ) (ρ φ v : V → ℝ) :
    discreteFirstVariation a b G h ρ φ v
      = -∑ x : V, v x * discreteResidual a b G h ρ φ x := by
  have hgrad : (∑ e : E, (1 / (4 * Real.pi * G)) *
        (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h)
      = (1 / (4 * Real.pi * G)) *
        (∑ e : E, (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by ring_nf)
  have hcoef : (1 / (4 * Real.pi * G)) *
        (∑ e : E, (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h)
      = ∑ e : E, discreteMomentum a b G h φ e * (v (b e) - v (a e)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by
      simp only [discreteMomentum]
      ring_nf)
  have hsrc : (∑ x : V, v x * (h * ρ x)) = h * ∑ x : V, ρ x * v x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  simp only [discreteFirstVariation, discreteResidual, hgrad, hcoef,
    sum_link_mul_difference a b (discreteMomentum a b G h φ) v]
  simp only [mul_add, Finset.sum_add_distrib, hsrc]
  ring

omit [DecidableEq V] in
/-- The derivative of the discrete action at `phi` in the direction `v` is the
first variation. -/
lemma hasDerivAt_discreteAction (a b : E → V) (G h : ℝ) (ρ φ v : V → ℝ) :
    HasDerivAt (fun ε : ℝ => discreteAction a b G h ρ (φ + ε • v))
      (discreteFirstVariation a b G h ρ φ v) 0 := by
  have hquad : HasDerivAt
      (fun ε : ℝ => ∑ e : E,
        ((φ (b e) - φ (a e)) + ε * (v (b e) - v (a e))) ^ 2 / h)
      (∑ e : E, 2 * (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h) 0 := by
    have hterm : ∀ e : E, HasDerivAt
        (fun ε : ℝ => ((φ (b e) - φ (a e)) + ε * (v (b e) - v (a e))) ^ 2 / h)
        (2 * (φ (b e) - φ (a e)) * (v (b e) - v (a e)) / h) 0 := by
      intro e
      have h1 : HasDerivAt
          (fun ε : ℝ => (φ (b e) - φ (a e)) + ε * (v (b e) - v (a e)))
          (v (b e) - v (a e)) 0 := by
        have h := (hasDerivAt_const (c := φ (b e) - φ (a e)) (x := (0 : ℝ))).add
          ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (v (b e) - v (a e)))
        convert h using 1
        · funext ε
          simp
        · ring
      have h3 := (h1.pow 2).div_const h
      convert h3 using 1
      ring
    convert HasDerivAt.sum (u := Finset.univ) (fun e _ => hterm e) using 1
    funext ε
    rw [Finset.sum_apply]
  have hlin : HasDerivAt
      (fun ε : ℝ => ∑ x : V, ρ x * (φ x + ε * v x))
      (∑ x : V, ρ x * v x) 0 := by
    have hterm : ∀ x : V, HasDerivAt
        (fun ε : ℝ => ρ x * (φ x + ε * v x)) (ρ x * v x) 0 := by
      intro x
      have h1 : HasDerivAt (fun ε : ℝ => φ x + ε * v x) (v x) 0 := by
        have h := (hasDerivAt_const (c := φ x) (x := (0 : ℝ))).add
          ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (v x))
        convert h using 1
        · funext ε
          simp
        · ring
      simpa using h1.const_mul (ρ x)
    convert HasDerivAt.sum (u := Finset.univ) (fun x _ => hterm x) using 1
    funext ε
    rw [Finset.sum_apply]
  have hfun : (fun ε : ℝ => discreteAction a b G h ρ (φ + ε • v))
      = fun ε : ℝ => -(1 / (8 * Real.pi * G)) *
          (∑ e : E, ((φ (b e) - φ (a e)) + ε * (v (b e) - v (a e))) ^ 2 / h)
          - h * ∑ x : V, ρ x * (φ x + ε * v x) := by
    funext ε
    have hdiff : ∀ e : E, (φ (b e) + ε * v (b e)) - (φ (a e) + ε * v (a e))
        = (φ (b e) - φ (a e)) + ε * (v (b e) - v (a e)) := by
      intro e
      ring
    simp only [discreteAction, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (∑ e : E,
        ((φ (b e) + ε * v (b e)) - (φ (a e) + ε * v (a e))) ^ 2 / h)
        = ∑ e : E, ((φ (b e) - φ (a e)) + ε * (v (b e) - v (a e))) ^ 2 / h from
      Finset.sum_congr rfl (fun e _ => by rw [hdiff e])]
  have hmoment := (hquad.const_mul (-(1 / (8 * Real.pi * G)))).sub (hlin.const_mul h)
  rw [hfun]
  convert hmoment using 1
  rw [discreteFirstVariation]
  congr 1
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring_nf)

/-- Stationarity of the discrete action under every variation that vanishes on
a chosen set `S` of sites (the Dirichlet boundary) is the discrete
Euler-Lagrange equation at every site outside `S`. -/
lemma discrete_stationary_iff (a b : E → V) (G h : ℝ) (ρ φ : V → ℝ) (S : Set V) :
    (∀ v : V → ℝ, (∀ x ∈ S, v x = 0) →
        discreteFirstVariation a b G h ρ φ v = 0) ↔
      ∀ x : V, x ∉ S → discreteResidual a b G h ρ φ x = 0 := by
  classical
  constructor
  · intro hstat x hx
    let v : V → ℝ := fun y => if y = x then 1 else 0
    have hv : ∀ y ∈ S, v y = 0 := by
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        exact absurd hy hx
      · simp [v, hyx]
    have h0 := hstat v hv
    rw [discreteFirstVariation_eq_neg_sum] at h0
    have hsum : (∑ y : V, v y * discreteResidual a b G h ρ φ y)
        = discreteResidual a b G h ρ φ x := by
      rw [Finset.sum_eq_single x]
      · simp [v]
      · intro y _ hyx
        simp [v, hyx]
      · intro hmem
        exact absurd (Finset.mem_univ x) hmem
    rw [hsum] at h0
    exact neg_eq_zero.mp h0
  · intro hres v hv
    rw [discreteFirstVariation_eq_neg_sum]
    have hzero : (∑ x : V, v x * discreteResidual a b G h ρ φ x) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : x ∈ S
      · rw [hv x hx, zero_mul]
      · rw [hres x hx, mul_zero]
    rw [hzero, neg_zero]

/-! ## D. A worked example on a three-site path -/

/-- The tail map of a two-link path on three sites. -/
def pathA : Fin 2 → Fin 3 := fun e => e.castSucc

/-- The head map of a two-link path on three sites. -/
def pathB : Fin 2 → Fin 3 := fun e => e.succ

/-- A quadratic field on the three sites, `C * i^2`. -/
def quadraticProfile (C : ℝ) : Fin 3 → ℝ := fun i => C * ((i : ℕ) : ℝ) ^ 2

/-- At the middle site the divergence is the incoming link momentum minus the
outgoing one. -/
lemma path_divergence_mid (d : Fin 2 → ℝ) :
    discreteDivergence pathA pathB d 1 = d 0 - d 1 := by
  simp [discreteDivergence, pathA, pathB, Fin.sum_univ_two]

/-- The first link momentum of the quadratic profile. -/
lemma path_momentum_zero (G h C : ℝ) :
    discreteMomentum pathA pathB G h (quadraticProfile C) 0
      = C / (4 * Real.pi * G * h) := by
  simp [discreteMomentum, pathA, pathB, quadraticProfile]

/-- The second link momentum of the quadratic profile. -/
lemma path_momentum_one (G h C : ℝ) :
    discreteMomentum pathA pathB G h (quadraticProfile C) 1
      = 3 * C / (4 * Real.pi * G * h) := by
  simp [discreteMomentum, pathA, pathB, quadraticProfile]
  ring

/-- The quadratic profile with `C = 2 pi G h^2 rho` satisfies the discrete
Euler-Lagrange equation at the middle site for every link length: its grid
values are exactly the continuum Poisson solution `2 pi G rho x^2` sampled at
`x = i h`. -/
lemma quadraticProfile_residual_mid (G h ρ : ℝ) (hG : G ≠ 0) :
    discreteResidual pathA pathB G h (fun _ : Fin 3 => ρ)
      (quadraticProfile (2 * Real.pi * G * h ^ 2 * ρ)) 1 = 0 := by
  simp [discreteResidual, path_divergence_mid, path_momentum_zero, path_momentum_one]
  field_simp
  ring

/-- Consequently the quadratic profile is stationary under every variation that
vanishes at the two endpoints of the path. -/
lemma quadraticProfile_stationary (G h ρ : ℝ) (hG : G ≠ 0) :
    ∀ v : Fin 3 → ℝ, (∀ x ∈ ({0, 2} : Set (Fin 3)), v x = 0) →
      discreteFirstVariation pathA pathB G h (fun _ : Fin 3 => ρ)
        (quadraticProfile (2 * Real.pi * G * h ^ 2 * ρ)) v = 0 := by
  intro v hv
  rw [discreteFirstVariation_eq_neg_sum]
  have hres := quadraticProfile_residual_mid G h ρ hG
  have h0 : v 0 = 0 := hv 0 (by simp)
  have h2 : v 2 = 0 := hv 2 (by simp)
  rw [Fin.sum_univ_three]
  simp [h0, h2, hres]

/-- The continuum profile has second derivative `4 pi G rho`, the Poisson
equation sourced by the same density. -/
lemma quadraticProfile_second_deriv (G ρ : ℝ) (x : ℝ) :
    deriv (deriv (fun y : ℝ => 2 * Real.pi * G * ρ * y ^ 2)) x
      = 4 * Real.pi * G * ρ := by
  have h1 : deriv (fun z : ℝ => 2 * Real.pi * G * ρ * z ^ 2)
      = fun y : ℝ => 4 * Real.pi * G * ρ * y := by
    funext y
    simp
    ring
  rw [h1]
  simp

/-! ## E. The continuum integration-by-parts step -/

/-- Integration by parts on an interval when the test function vanishes at both
endpoints. -/
lemma aqual_integral_mul_deriv_eq_neg_integral_deriv_mul
    {u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ContinuousOn u (Set.uIcc a b)) (hv : ContinuousOn v (Set.uIcc a b))
    (hu' : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hv' : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hiu : IntervalIntegrable u' MeasureTheory.volume a b) (hiv : IntervalIntegrable v' MeasureTheory.volume a b)
    (hva : v a = 0) (hvb : v b = 0) :
    (∫ x in a..b, u x * v' x ∂MeasureTheory.volume) = -∫ x in a..b, u' x * v x ∂MeasureTheory.volume := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv hu' hv' hiu hiv,
    hva, hvb]
  ring

/-- The first variation of the AQUAL action on an interval, before integration by
parts: the integral of `-rho v + momentum v'`. -/
noncomputable def aqualFirstVariationIntegral (a0 G : ℝ) (F' : ℝ → ℝ)
    (ρ φ' v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, (-ρ x) * v x + aqualMomentumDensity a0 G F' φ' x * deriv v x ∂MeasureTheory.volume

/-- On an interval, with the test function vanishing at both endpoints, the
first variation is the integral of the AQUAL Euler-Lagrange residual against the
test function. -/
lemma aqual_first_variation_eq_integral_residual
    (a0 G : ℝ) (F' ρ φ' v : ℝ → ℝ) (a b : ℝ)
    (hu : ContinuousOn (aqualMomentumDensity a0 G F' φ') (Set.uIcc a b))
    (hv : ContinuousOn v (Set.uIcc a b))
    (hu' : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (aqualMomentumDensity a0 G F' φ')
        (deriv (aqualMomentumDensity a0 G F' φ') x) x)
    (hv' : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt v (deriv v x) x)
    (hiu : IntervalIntegrable (deriv (aqualMomentumDensity a0 G F' φ')) MeasureTheory.volume a b)
    (hiv : IntervalIntegrable (deriv v) MeasureTheory.volume a b)
    (hρv : IntervalIntegrable (fun x => (-ρ x) * v x) MeasureTheory.volume a b)
    (huv : IntervalIntegrable
      (fun x => aqualMomentumDensity a0 G F' φ' x * deriv v x) MeasureTheory.volume a b)
    (hva : v a = 0) (hvb : v b = 0) :
    aqualFirstVariationIntegral a0 G F' ρ φ' v a b =
      ∫ x in a..b,
        (-ρ x - deriv (aqualMomentumDensity a0 G F' φ') x) * v x ∂MeasureTheory.volume := by
  unfold aqualFirstVariationIntegral
  rw [intervalIntegral.integral_add hρv huv]
  rw [aqual_integral_mul_deriv_eq_neg_integral_deriv_mul hu hv hu' hv' hiu hiv hva hvb]
  have hiu_v : IntervalIntegrable
      (fun x => deriv (aqualMomentumDensity a0 G F' φ') x * v x) MeasureTheory.volume a b :=
    hiu.mul_continuousOn hv
  rw [← sub_eq_add_neg, ← intervalIntegral.integral_sub hρv hiu_v]
  exact intervalIntegral.integral_congr (fun x _ => by ring)

/-! ## F. The fundamental lemma of the calculus of variations -/

/-- The fundamental lemma for continuous residuals on an interval: a residual
orthogonal to every continuous test function vanishing at the endpoints vanishes
in the interior.  The test function used is `r * ((x - a) * (b - x))`, which
vanishes at the endpoints and is positive inside, so no bump functions are
needed. -/
lemma aqual_fundamental_lemma {r : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hr : ContinuousOn r (Set.Icc a b))
    (h : ∀ v : ℝ → ℝ, ContinuousOn v (Set.Icc a b) → v a = 0 → v b = 0 →
      (∫ x in a..b, r x * v x ∂MeasureTheory.volume) = 0)
    {x : ℝ} (hx : x ∈ Set.Ioo a b) : r x = 0 := by
  by_contra hxr
  let w : ℝ → ℝ := fun y => (y - a) * (b - y)
  have hw : ContinuousOn w (Set.Icc a b) := by
    unfold w
    fun_prop
  have hv : ContinuousOn (fun y => r y * w y) (Set.Icc a b) := hr.mul hw
  have hva : (fun y => r y * w y) a = 0 := by simp [w]
  have hvb : (fun y => r y * w y) b = 0 := by simp [w]
  have hint := h (fun y => r y * w y) hv hva hvb
  have hsq : (∫ y in a..b, r y ^ 2 * w y ∂MeasureTheory.volume) = 0 := by
    rw [← hint]
    exact intervalIntegral.integral_congr (fun y _ => by ring)
  have hcont : ContinuousOn (fun y => r y ^ 2 * w y) (Set.Icc a b) :=
    (hr.pow 2).mul hw
  have hnonneg : ∀ y ∈ Set.Ioc a b, 0 ≤ r y ^ 2 * w y := by
    intro y hy
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (sub_nonneg.mpr hy.1.le) (sub_nonneg.mpr hy.2))
  have hxpos : 0 < r x ^ 2 * w x := by
    have hrx : 0 < r x ^ 2 := by
      simpa [pow_two] using mul_self_pos.mpr hxr
    have hwx : 0 < w x := by
      unfold w
      exact mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
    exact mul_pos hrx hwx
  have hpos : 0 < ∫ y in a..b, r y ^ 2 * w y ∂MeasureTheory.volume :=
    intervalIntegral.integral_pos hab hcont hnonneg
      ⟨x, ⟨hx.1.le, hx.2.le⟩, hxpos⟩
  rw [hsq] at hpos
  exact lt_irrefl 0 hpos

/-! ## G. The general path -/

/-- The tail map of the path on `n + 1` sites. -/
def pathNA (n : ℕ) : Fin n → Fin (n + 1) := fun e => e.castSucc

/-- The head map of the path on `n + 1` sites. -/
def pathNB (n : ℕ) : Fin n → Fin (n + 1) := fun e => e.succ

/-- A quadratic field on `n + 1` sites. -/
def quadraticProfileN (n : ℕ) (C : ℝ) : Fin (n + 1) → ℝ :=
  fun i => C * ((i : ℕ) : ℝ) ^ 2

/-- The divergence at an interior site of the path is the incoming momentum
minus the outgoing one. -/
lemma pathN_divergence {n : ℕ} (d : Fin n → ℝ) (i : Fin (n + 1))
    (h0 : i ≠ 0) (hi : i.val < n) :
    discreteDivergence (pathNA n) (pathNB n) d i
      = d (Fin.pred i h0) - d (⟨i.val, hi⟩ : Fin n) := by
  have hb : (∑ e : Fin n, if (pathNB n e : Fin (n + 1)) = i then d e else 0)
      = d (Fin.pred i h0) := by
    have hb' : (∑ e : Fin n, if (pathNB n e : Fin (n + 1)) = i then d e else 0)
        = (if (pathNB n (Fin.pred i h0) : Fin (n + 1)) = i then
            d (Fin.pred i h0) else 0) := by
      refine Finset.sum_eq_single (s := Finset.univ)
        (f := fun e : Fin n => if (pathNB n e : Fin (n + 1)) = i then d e else 0)
        (Fin.pred i h0) ?_ ?_
      · intro e _ he
        have hne : (pathNB n e : Fin (n + 1)) ≠ i := by
          intro hc
          apply he
          have h2 : e.succ = (Fin.pred i h0).succ := by
            rw [Fin.succ_pred]
            exact hc
          exact Fin.succ_injective n h2
        simp [hne]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hb', show (pathNB n (Fin.pred i h0) : Fin (n + 1)) = i from Fin.succ_pred i h0]
    simp
  have ha : (∑ e : Fin n, if (pathNA n e : Fin (n + 1)) = i then d e else 0)
      = d (⟨i.val, hi⟩ : Fin n) := by
    have ha' : (∑ e : Fin n, if (pathNA n e : Fin (n + 1)) = i then d e else 0)
        = (if (pathNA n (⟨i.val, hi⟩ : Fin n) : Fin (n + 1)) = i then
            d (⟨i.val, hi⟩ : Fin n) else 0) := by
      refine Finset.sum_eq_single (s := Finset.univ)
        (f := fun e : Fin n => if (pathNA n e : Fin (n + 1)) = i then d e else 0)
        (⟨i.val, hi⟩ : Fin n) ?_ ?_
      · intro e _ he
        have hne : (pathNA n e : Fin (n + 1)) ≠ i := by
          intro hc
          apply he
          apply Fin.ext
          have hval := congrArg Fin.val hc
          simpa [pathNA] using hval
        simp [hne]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [ha', show (pathNA n (⟨i.val, hi⟩ : Fin n) : Fin (n + 1)) = i from by
      apply Fin.ext
      rfl]
    simp
  unfold discreteDivergence
  rw [hb, ha]

/-- The link momentum of the quadratic profile on a general path. -/
lemma pathN_momentum {n : ℕ} (G h C : ℝ) (e : Fin n) :
    discreteMomentum (pathNA n) (pathNB n) G h (quadraticProfileN n C) e
      = C * (2 * (e : ℕ) + 1) / (4 * Real.pi * G * h) := by
  simp [discreteMomentum, pathNA, pathNB, quadraticProfileN]
  ring

/-- The quadratic profile with `C = 2 pi G h^2 rho` satisfies the discrete
Euler-Lagrange equation at every interior site of the general path. -/
lemma quadraticProfileN_residual {n : ℕ} (G h ρ : ℝ) (hG : G ≠ 0)
    (i : Fin (n + 1)) (h0 : i ≠ 0) (hi : i.val < n) :
    discreteResidual (pathNA n) (pathNB n) G h (fun _ => ρ)
      (quadraticProfileN n (2 * Real.pi * G * h ^ 2 * ρ)) i = 0 := by
  rw [discreteResidual, pathN_divergence (d := discreteMomentum (pathNA n) (pathNB n) G h
    (quadraticProfileN n (2 * Real.pi * G * h ^ 2 * ρ))) i h0 hi]
  simp [pathN_momentum]
  have hi0 : 0 < i.val := Nat.pos_of_ne_zero (fun h => h0 (Fin.ext h))
  have hcast : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hi0)]
    norm_num
  field_simp
  rw [hcast]
  ring

/-- Along any grid refinement with `i h -> x`, the quadratic grid values tend to
the continuum Poisson solution `2 pi G rho x^2`. -/
lemma quadraticProfileN_tendsto (G ρ x : ℝ) {ι : Type*} {l : Filter ι}
    (h : ι → ℝ) (i : ι → ℕ)
    (hx : Filter.Tendsto (fun k => (i k : ℝ) * h k) l (nhds x)) :
    Filter.Tendsto
      (fun k => 2 * Real.pi * G * ρ * ((i k : ℝ) * h k) ^ 2)
      l (nhds (2 * Real.pi * G * ρ * x ^ 2)) := by
  simpa [mul_assoc] using (hx.pow 2).const_mul (2 * Real.pi * G * ρ)

/-! ## H. Differentiation under the interval integral -/

/-- Differentiation under an interval integral for a quadratic integrand. -/
lemma hasDerivAt_integral_quadratic {f0 f1 f2 : ℝ → ℝ} {l u : ℝ}
    (h0 : IntervalIntegrable f0 MeasureTheory.volume l u)
    (h1 : IntervalIntegrable f1 MeasureTheory.volume l u)
    (h2 : IntervalIntegrable f2 MeasureTheory.volume l u) :
    HasDerivAt (fun ε : ℝ => ∫ x in l..u, f0 x + ε * f1 x + ε ^ 2 * f2 x)
      (∫ x in l..u, f1 x ∂MeasureTheory.volume) 0 := by
  have hexp : ∀ ε : ℝ, (∫ x in l..u, f0 x + ε * f1 x + ε ^ 2 * f2 x)
      = (∫ x in l..u, f0 x) + ε * (∫ x in l..u, f1 x)
        + ε ^ 2 * (∫ x in l..u, f2 x) := by
    intro ε
    calc ∫ x in l..u, f0 x + ε * f1 x + ε ^ 2 * f2 x
        = ∫ x in l..u, (f0 x + ε * f1 x) + ε ^ 2 * f2 x := rfl
      _ = (∫ x in l..u, f0 x + ε * f1 x) + ∫ x in l..u, ε ^ 2 * f2 x :=
          intervalIntegral.integral_add (h0.add (h1.const_mul ε)) (h2.const_mul (ε ^ 2))
      _ = ((∫ x in l..u, f0 x) + ∫ x in l..u, ε * f1 x) + ∫ x in l..u, ε ^ 2 * f2 x := by
          rw [intervalIntegral.integral_add h0 (h1.const_mul ε)]
      _ = ((∫ x in l..u, f0 x) + ε * ∫ x in l..u, f1 x)
            + ε ^ 2 * ∫ x in l..u, f2 x := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = (∫ x in l..u, f0 x) + ε * (∫ x in l..u, f1 x)
            + ε ^ 2 * (∫ x in l..u, f2 x) := by ring
  have hpoly : HasDerivAt (fun ε : ℝ =>
      (∫ x in l..u, f0 x) + ε * (∫ x in l..u, f1 x)
        + ε ^ 2 * (∫ x in l..u, f2 x))
      (∫ x in l..u, f1 x) 0 := by
    have hlin : HasDerivAt (fun ε : ℝ => ε * (∫ x in l..u, f1 x))
        (∫ x in l..u, f1 x) 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).mul_const (∫ x in l..u, f1 x)
    have hquad : HasDerivAt (fun ε : ℝ => ε ^ 2 * (∫ x in l..u, f2 x)) 0 0 := by
      simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).pow 2).mul_const (∫ x in l..u, f2 x)
    have h := ((hasDerivAt_const (c := ∫ x in l..u, f0 x) (x := (0 : ℝ))).add hlin).add hquad
    convert h using 1
    ring
  rw [show (fun ε : ℝ => ∫ x in l..u, f0 x + ε * f1 x + ε ^ 2 * f2 x)
      = fun ε : ℝ => (∫ x in l..u, f0 x) + ε * (∫ x in l..u, f1 x)
        + ε ^ 2 * (∫ x in l..u, f2 x) from funext hexp]
  exact hpoly

/-- The Poisson-limit AQUAL action on an interval. -/
noncomputable def aqualPoissonAction (G : ℝ) (ρ φ φ' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, -(φ' x) ^ 2 / (8 * Real.pi * G) - ρ x * φ x ∂MeasureTheory.volume

/-- Its first variation at zero along `phi + epsilon v` and `phi' + epsilon v'`. -/
noncomputable def aqualPoissonActionVariation (G : ℝ) (ρ _φ φ' v v' : ℝ → ℝ)
    (a b : ℝ) : ℝ :=
  ∫ x in a..b, -(φ' x * v' x) / (4 * Real.pi * G) - ρ x * v x ∂MeasureTheory.volume

/-- Differentiation under the integral for the Poisson-limit AQUAL action. -/
lemma hasDerivAt_aqualPoissonAction
    (G : ℝ) (ρ φ φ' v v' : ℝ → ℝ) (a b : ℝ)
    (h0 : IntervalIntegrable
      (fun x => -(φ' x) ^ 2 / (8 * Real.pi * G) - ρ x * φ x) MeasureTheory.volume a b)
    (h1 : IntervalIntegrable
      (fun x => -(φ' x * v' x) / (4 * Real.pi * G) - ρ x * v x) MeasureTheory.volume a b)
    (h2 : IntervalIntegrable
      (fun x => -(v' x) ^ 2 / (8 * Real.pi * G)) MeasureTheory.volume a b) :
    HasDerivAt (fun ε : ℝ => aqualPoissonAction G ρ (φ + ε • v) (φ' + ε • v') a b)
      (aqualPoissonActionVariation G ρ φ φ' v v' a b) 0 := by
  have hquad := hasDerivAt_integral_quadratic
    (f0 := fun x => -(φ' x) ^ 2 / (8 * Real.pi * G) - ρ x * φ x)
    (f1 := fun x => -(φ' x * v' x) / (4 * Real.pi * G) - ρ x * v x)
    (f2 := fun x => -(v' x) ^ 2 / (8 * Real.pi * G)) h0 h1 h2
  rw [show (fun ε : ℝ => aqualPoissonAction G ρ (φ + ε • v) (φ' + ε • v') a b)
      = fun ε : ℝ => ∫ x in a..b,
          (-(φ' x) ^ 2 / (8 * Real.pi * G) - ρ x * φ x)
          + ε * (-(φ' x * v' x) / (4 * Real.pi * G) - ρ x * v x)
          + ε ^ 2 * (-(v' x) ^ 2 / (8 * Real.pi * G)) from by
        funext ε
        simp only [aqualPoissonAction, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact intervalIntegral.integral_congr (fun x _ => by ring)]
  simpa [aqualPoissonActionVariation] using hquad

/-! ## I. The full nonlinear free-function variation -/

/-- The one-dimensional AQUAL action on an interval for an arbitrary free
function, `∫ (-(a0^2/8 pi G) F(phi'^2/a0^2) - rho phi)`. -/
noncomputable def aqualAction1D (a0 G : ℝ) (F ρ φ φ' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b,
    aqualLagrangianDensity1D a0 G F (ρ x) (φ x) (φ' x) ∂MeasureTheory.volume

/-- The chain rule along a straight-line variation of the full nonlinear AQUAL
density.  The derivative is the source term plus the AQUAL momentum contracted
with the variation of the field derivative. -/
lemma aqualLagrangianDensity1D_hasDerivAt_variation
    (a0 G : ℝ) (F F' : ℝ → ℝ) (ρ φ φ' v v' : ℝ → ℝ) (x : ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0)
    (hF : HasDerivAt F (F' (φ' x ^ 2 / a0 ^ 2)) (φ' x ^ 2 / a0 ^ 2)) :
    HasDerivAt
      (fun ε : ℝ =>
        aqualLagrangianDensity1D a0 G F (ρ x) (φ x + ε * v x) (φ' x + ε * v' x))
      (-ρ x * v x + aqualMomentumDensity a0 G F' φ' x * v' x) 0 := by
  have harg : HasDerivAt (fun ε : ℝ => (φ' x + ε * v' x) ^ 2 / a0 ^ 2)
      (2 * φ' x * v' x / a0 ^ 2) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => φ' x + ε * v' x) (v' x) 0 := by
      have h := (hasDerivAt_const (c := φ' x) (x := (0 : ℝ))).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (v' x))
      convert h using 1
      · funext ε
        simp
      · ring
    have h2 := (h1.pow 2).div_const (a0 ^ 2)
    convert h2 using 1
    ring
  have hpoint : (φ' x + 0 * v' x) ^ 2 / a0 ^ 2 = (φ' x) ^ 2 / a0 ^ 2 := by ring
  have hF0 := hF
  rw [← hpoint] at hF0
  have hFarg := hF0.comp 0 harg
  have hphi : HasDerivAt (fun ε : ℝ => φ x + ε * v x) (v x) 0 := by
    have h := (hasDerivAt_const (c := φ x) (x := (0 : ℝ))).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (v x))
    convert h using 1
    · funext ε
      simp
    · ring
  have hsource : HasDerivAt (fun ε : ℝ => ρ x * (φ x + ε * v x)) (ρ x * v x) 0 :=
    hphi.const_mul (ρ x)
  have hdensity : HasDerivAt
      (fun ε : ℝ =>
        aqualLagrangianDensity1D a0 G F (ρ x) (φ x + ε * v x) (φ' x + ε * v' x))
      (-(a0 ^ 2 / (8 * Real.pi * G)) *
          (F' (φ' x ^ 2 / a0 ^ 2) * (2 * φ' x * v' x / a0 ^ 2))
        - ρ x * v x) 0 := by
    have hconst := hFarg.const_mul (-(a0 ^ 2 / (8 * Real.pi * G)))
    have hsub := hconst.sub hsource
    convert hsub using 1
    · funext ε
      simp [aqualLagrangianDensity1D]
    · ring_nf
  convert hdensity using 1
  unfold aqualMomentumDensity
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [ha0, hG, hpi]
  ring

/-- The pointwise chain rule at an arbitrary parameter value.  This is the form
needed for differentiating under a whole-line integral, where the derivative is
required on a neighbourhood of the base parameter. -/
lemma aqualLagrangianDensity1D_hasDerivAt_variation_at
    (a0 G : ℝ) (F F' : ℝ → ℝ) (ρ φ φ' v v' : ℝ → ℝ) (x ε₀ : ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0)
    (hF : HasDerivAt F (F' ((φ' x + ε₀ * v' x) ^ 2 / a0 ^ 2))
      ((φ' x + ε₀ * v' x) ^ 2 / a0 ^ 2)) :
    HasDerivAt
      (fun ε : ℝ =>
        aqualLagrangianDensity1D a0 G F (ρ x) (φ x + ε * v x) (φ' x + ε * v' x))
      (-ρ x * v x +
        aqualMomentumDensity a0 G F' (fun t => φ' t + ε₀ * v' t) x * v' x) ε₀ := by
  have harg : HasDerivAt (fun ε : ℝ => (φ' x + ε * v' x) ^ 2 / a0 ^ 2)
      (2 * (φ' x + ε₀ * v' x) * v' x / a0 ^ 2) ε₀ := by
    have h1 : HasDerivAt (fun ε : ℝ => φ' x + ε * v' x) (v' x) ε₀ := by
      have h := (hasDerivAt_const (c := φ' x) (x := ε₀)).add
        ((hasDerivAt_id (𝕜 := ℝ) ε₀).mul_const (v' x))
      convert h using 1
      · funext ε
        simp
      · ring
    have h2 := (h1.pow 2).div_const (a0 ^ 2)
    convert h2 using 1
    ring
  have hFarg := hF.comp ε₀ harg
  have hphi : HasDerivAt (fun ε : ℝ => φ x + ε * v x) (v x) ε₀ := by
    have h := (hasDerivAt_const (c := φ x) (x := ε₀)).add
      ((hasDerivAt_id (𝕜 := ℝ) ε₀).mul_const (v x))
    convert h using 1
    · funext ε
      simp
    · ring
  have hsource : HasDerivAt (fun ε : ℝ => ρ x * (φ x + ε * v x)) (ρ x * v x) ε₀ :=
    hphi.const_mul (ρ x)
  have hdensity : HasDerivAt
      (fun ε : ℝ =>
        aqualLagrangianDensity1D a0 G F (ρ x) (φ x + ε * v x) (φ' x + ε * v' x))
      (-(a0 ^ 2 / (8 * Real.pi * G)) *
          (F' ((φ' x + ε₀ * v' x) ^ 2 / a0 ^ 2) *
            (2 * (φ' x + ε₀ * v' x) * v' x / a0 ^ 2))
        - ρ x * v x) ε₀ := by
    have hconst := hFarg.const_mul (-(a0 ^ 2 / (8 * Real.pi * G)))
    have hsub := hconst.sub hsource
    convert hsub using 1
    · funext ε
      simp [aqualLagrangianDensity1D]
  convert hdensity using 1
  unfold aqualMomentumDensity
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [ha0, hG, hpi]
  ring

/-- Differentiation under the interval integral for the full nonlinear AQUAL
action.  The hypotheses are the standard parametric-integral regularity: the
uncurried density is `C^1` on a neighbourhood of the parameter times the
interval, its parameter derivative is continuous, and the pointwise chain rule
holds on the interval. -/
lemma hasDerivAt_aqualAction1D
    (a0 G : ℝ) (F F' ρ φ φ' v : ℝ → ℝ) (a b : ℝ)
    (hcont : ContDiffOn ℝ 1
      (Function.uncurry (fun (ε : ℝ) (t : ℝ) =>
        aqualLagrangianDensity1D a0 G F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)))
      (Set.univ ×ˢ Set.uIcc a b))
    (hcont' : ContinuousOn
      (fun t : ℝ => fderiv ℝ (fun ε : ℝ =>
        aqualLagrangianDensity1D a0 G F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)) 0) (Set.uIcc a b))
    (hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun ε : ℝ => aqualLagrangianDensity1D a0 G F (ρ t)
        (φ t + ε * v t) (φ' t + ε * deriv v t))
        (-ρ t * v t + aqualMomentumDensity a0 G F' φ' t * deriv v t) 0) :
    HasDerivAt
      (fun ε : ℝ => aqualAction1D a0 G F ρ (φ + ε • v) (φ' + ε • deriv v) a b)
      (aqualFirstVariationIntegral a0 G F' ρ φ' v a b) 0 := by
  let f : ℝ → ℝ → ℝ := fun ε t =>
    aqualLagrangianDensity1D a0 G F (ρ t) (φ t + ε * v t) (φ' t + ε * deriv v t)
  have hmain := intervalIntegral.hasFDerivAt_integral_of_contDiffOn
    (μ := MeasureTheory.volume) (f := f) (x₀ := (0 : ℝ)) (u := Set.univ)
    (by simp) (a := a) (b := b) (by simpa [f] using hcont)
  have hd := hmain.hasDerivAt
  have hIntOn : MeasureTheory.IntegrableOn
      (fun t : ℝ => fderiv ℝ (fun ε : ℝ => f ε t) 0)
      (Set.uIcc a b) MeasureTheory.volume :=
    hcont'.integrableOn_compact isCompact_uIcc
  have hswap : (∫ t in a..b, fderiv ℝ (fun ε : ℝ => f ε t) 0) 1
      = ∫ t in a..b, (fderiv ℝ (fun ε : ℝ => f ε t) 0) 1 :=
    ContinuousLinearMap.intervalIntegral_apply (𝕜 := ℝ) hIntOn.intervalIntegrable 1
  rw [hswap] at hd
  simp_rw [fderiv_apply_one_eq_deriv] at hd
  have hfun : (fun ε : ℝ => aqualAction1D a0 G F ρ (φ + ε • v) (φ' + ε • deriv v) a b)
      = fun ε : ℝ => ∫ t in a..b, f ε t := rfl
  rw [hfun, aqualFirstVariationIntegral]
  convert hd using 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact (hderiv t ht).deriv.symm

/-- The nonlinear interval variation with the free function's derivative data
discharged, away from zeros of the field derivative. -/
lemma hasDerivAt_aqualAction1D_freeFunction
    (A : AqualFreeFunction) (a0 G : ℝ) (ρ φ φ' v : ℝ → ℝ) (a b : ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0)
    (hne : ∀ t ∈ Set.uIcc a b, φ' t ≠ 0)
    (hcont : ContDiffOn ℝ 1
      (Function.uncurry (fun (ε : ℝ) (t : ℝ) =>
        aqualLagrangianDensity1D a0 G A.F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)))
      (Set.univ ×ˢ Set.uIcc a b))
    (hcont' : ContinuousOn
      (fun t : ℝ => fderiv ℝ (fun ε : ℝ =>
        aqualLagrangianDensity1D a0 G A.F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)) 0) (Set.uIcc a b)) :
    HasDerivAt
      (fun ε : ℝ => aqualAction1D a0 G A.F ρ (φ + ε • v) (φ' + ε • deriv v) a b)
      (aqualFirstVariationIntegral a0 G A.F' ρ φ' v a b) 0 := by
  refine hasDerivAt_aqualAction1D a0 G A.F A.F' ρ φ φ' v a b hcont hcont' ?_
  intro t ht
  have hy : 0 < φ' t ^ 2 / a0 ^ 2 := by
    apply div_pos
    · simpa [pow_two] using mul_self_pos.mpr (hne t ht)
    · simpa [pow_two] using mul_self_pos.mpr ha0
  exact aqualLagrangianDensity1D_hasDerivAt_variation a0 G A.F A.F' ρ φ φ' v
    (deriv v) t hG ha0 (A.hasDeriv _ hy)

/-- The nonlinear interval variation with a global derivative for the free
function, so the field derivative need not be nonzero. -/
lemma hasDerivAt_aqualAction1D_of_hasDerivAt
    (a0 G : ℝ) (F F' ρ φ φ' v : ℝ → ℝ) (a b : ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0)
    (hF : ∀ y : ℝ, HasDerivAt F (F' y) y)
    (hcont : ContDiffOn ℝ 1
      (Function.uncurry (fun (ε : ℝ) (t : ℝ) =>
        aqualLagrangianDensity1D a0 G F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)))
      (Set.univ ×ˢ Set.uIcc a b))
    (hcont' : ContinuousOn
      (fun t : ℝ => fderiv ℝ (fun ε : ℝ =>
        aqualLagrangianDensity1D a0 G F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)) 0) (Set.uIcc a b)) :
    HasDerivAt
      (fun ε : ℝ => aqualAction1D a0 G F ρ (φ + ε • v) (φ' + ε • deriv v) a b)
      (aqualFirstVariationIntegral a0 G F' ρ φ' v a b) 0 := by
  refine hasDerivAt_aqualAction1D a0 G F F' ρ φ φ' v a b hcont hcont' ?_
  intro t _
  exact aqualLagrangianDensity1D_hasDerivAt_variation a0 G F F' ρ φ φ' v
    (deriv v) t hG ha0 (hF _)

/-- The whole-line action variation under compact support: if the density
vanishes outside `[a, b]`, the integral over the line is the interval integral,
so the nonlinear interval theorem applies. -/
lemma hasDerivAt_aqualActionLine_of_support
    (a0 G : ℝ) (F F' ρ φ φ' v : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hsupp : ∀ ε x, x ∉ Set.Icc a b →
      aqualLagrangianDensity1D a0 G F (ρ x)
        (φ x + ε * v x) (φ' x + ε * deriv v x) = 0)
    (hcont : ContDiffOn ℝ 1
      (Function.uncurry (fun (ε : ℝ) (t : ℝ) =>
        aqualLagrangianDensity1D a0 G F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)))
      (Set.univ ×ˢ Set.uIcc a b))
    (hcont' : ContinuousOn
      (fun t : ℝ => fderiv ℝ (fun ε : ℝ =>
        aqualLagrangianDensity1D a0 G F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)) 0) (Set.uIcc a b))
    (hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun ε : ℝ => aqualLagrangianDensity1D a0 G F (ρ t)
        (φ t + ε * v t) (φ' t + ε * deriv v t))
        (-ρ t * v t + aqualMomentumDensity a0 G F' φ' t * deriv v t) 0) :
    HasDerivAt
      (fun ε : ℝ => ∫ x,
        aqualLagrangianDensity1D a0 G F (ρ x)
          (φ x + ε * v x) (φ' x + ε * deriv v x))
      (aqualFirstVariationIntegral a0 G F' ρ φ' v a b) 0 := by
  have hline : (fun ε : ℝ => ∫ x,
      aqualLagrangianDensity1D a0 G F (ρ x)
        (φ x + ε * v x) (φ' x + ε * deriv v x))
      = fun ε : ℝ => aqualAction1D a0 G F ρ (φ + ε • v) (φ' + ε • deriv v) a b := by
    funext ε
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc a b) (fun x hx => hsupp ε x hx)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    rfl
  rw [hline]
  exact hasDerivAt_aqualAction1D a0 G F F' ρ φ φ' v a b hcont hcont' hderiv

/-- The AQUAL density along a straight-line whole-line variation, with the field
derivative varied by `v'`. -/
noncomputable def aqualVariationDensity (a0 G : ℝ) (F ρ φ φ' v v' : ℝ → ℝ)
    (ε x : ℝ) : ℝ :=
  aqualLagrangianDensity1D a0 G F (ρ x) (φ x + ε * v x) (φ' x + ε * v' x)

/-- The parameter derivative of `aqualVariationDensity` at `ε`. -/
noncomputable def aqualVariationDerivative (a0 G : ℝ) (F' ρ v v' : ℝ → ℝ)
    (φ' : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  -ρ x * v x + aqualMomentumDensity a0 G F' (fun t => φ' t + ε * v' t) x * v' x

/-- The nonlinear interval variation with the parametric `C^1` hypotheses
discharged from concrete smoothness of the data.  The density is `C^1` on
`univ × uIcc a b` because `F`, `ρ`, `φ`, `φ'`, `v` and `deriv v` are, and the
parameter derivative is continuous because `F'` is. -/
lemma hasDerivAt_aqualAction1D_of_contDiff
    (a0 G : ℝ) (F F' ρ φ φ' v : ℝ → ℝ) (a b : ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0)
    (hF : ContDiff ℝ 2 F)
    (hFderiv : ∀ y : ℝ, HasDerivAt F (F' y) y)
    (hρ : ContDiffOn ℝ 1 ρ (Set.uIcc a b))
    (hφ : ContDiffOn ℝ 1 φ (Set.uIcc a b))
    (hφ' : ContDiffOn ℝ 1 φ' (Set.uIcc a b))
    (hv : ContDiffOn ℝ 1 v (Set.uIcc a b))
    (hv' : ContDiffOn ℝ 1 (deriv v) (Set.uIcc a b)) :
    HasDerivAt
      (fun ε : ℝ => aqualAction1D a0 G F ρ (φ + ε • v) (φ' + ε • deriv v) a b)
      (aqualFirstVariationIntegral a0 G F' ρ φ' v a b) 0 := by
  have hF'eq : F' = deriv F := funext fun y => (hFderiv y).deriv.symm
  have hF' : ContDiff ℝ 1 F' := by
    rw [hF'eq]
    exact hF.deriv'
  have hcont : ContDiffOn ℝ 1
      (Function.uncurry (fun (ε : ℝ) (t : ℝ) =>
        aqualLagrangianDensity1D a0 G F (ρ t)
          (φ t + ε * v t) (φ' t + ε * deriv v t)))
      (Set.univ ×ˢ Set.uIcc a b) := by
    have hs : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.2) (Set.univ ×ˢ Set.uIcc a b) :=
      contDiffOn_snd
    have hρs : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ρ p.2) (Set.univ ×ˢ Set.uIcc a b) :=
      hρ.comp hs (fun p hp => hp.2)
    have hφs : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => φ p.2) (Set.univ ×ˢ Set.uIcc a b) :=
      hφ.comp hs (fun p hp => hp.2)
    have hφ's : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => φ' p.2) (Set.univ ×ˢ Set.uIcc a b) :=
      hφ'.comp hs (fun p hp => hp.2)
    have hvs : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => v p.2) (Set.univ ×ˢ Set.uIcc a b) :=
      hv.comp hs (fun p hp => hp.2)
    have hdv : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv v p.2) (Set.univ ×ˢ Set.uIcc a b) :=
      hv'.comp hs (fun p hp => hp.2)
    have hfst : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.1) (Set.univ ×ˢ Set.uIcc a b) :=
      contDiffOn_fst
    have hy : ContDiffOn ℝ 1
        (fun p : ℝ × ℝ => (φ' p.2 + p.1 * deriv v p.2) ^ 2 / a0 ^ 2)
        (Set.univ ×ˢ Set.uIcc a b) :=
      ((hφ's.add (hfst.mul hdv)).pow 2).div_const (a0 ^ 2)
    have hFy : ContDiffOn ℝ 1
        (fun p : ℝ × ℝ => F ((φ' p.2 + p.1 * deriv v p.2) ^ 2 / a0 ^ 2))
        (Set.univ ×ˢ Set.uIcc a b) :=
      (hF.contDiffOn.of_le (by norm_num)).comp hy (fun p _ => Set.mem_univ _)
    have hsrc : ContDiffOn ℝ 1
        (fun p : ℝ × ℝ => ρ p.2 * (φ p.2 + p.1 * v p.2)) (Set.univ ×ˢ Set.uIcc a b) :=
      hρs.mul (hφs.add (hfst.mul hvs))
    exact ((contDiffOn_const (c := (-(a0 ^ 2 / (8 * Real.pi * G))))).mul hFy).sub hsrc
  have hcontD : ContinuousOn (aqualVariationDerivative a0 G F' ρ v (deriv v) φ' 0)
      (Set.uIcc a b) := by
    have hφ's : ContDiffOn ℝ 1 (fun t : ℝ => φ' t) (Set.uIcc a b) := hφ'
    have hdv : ContDiffOn ℝ 1 (fun t : ℝ => deriv v t) (Set.uIcc a b) := hv'
    have hy : ContDiffOn ℝ 1 (fun t : ℝ => φ' t ^ 2 / a0 ^ 2) (Set.uIcc a b) :=
      (hφ's.pow 2).div_const (a0 ^ 2)
    have hF'y : ContDiffOn ℝ 1 (fun t : ℝ => F' (φ' t ^ 2 / a0 ^ 2)) (Set.uIcc a b) :=
      hF'.contDiffOn.comp hy (fun t _ => Set.mem_univ _)
    have hmom : ContDiffOn ℝ 1 (fun t : ℝ => aqualMomentumDensity a0 G F' φ' t)
        (Set.uIcc a b) := by
      unfold aqualMomentumDensity
      exact ((contDiffOn_const (c := (-(1 / (4 * Real.pi * G))))).mul hF'y).mul hφ's
    have hmain : ContinuousOn
        (fun t : ℝ => -ρ t * v t + aqualMomentumDensity a0 G F' φ' t * deriv v t)
        (Set.uIcc a b) :=
      (hρ.continuousOn.neg.mul hv.continuousOn).add (hmom.continuousOn.mul hdv.continuousOn)
    convert hmain using 1
    funext t
    simp [aqualVariationDerivative]
  have hderiv0 : ∀ t ∈ Set.uIcc a b, HasDerivAt
      (fun ε : ℝ => aqualVariationDensity a0 G F ρ φ φ' v (deriv v) ε t)
      (aqualVariationDerivative a0 G F' ρ v (deriv v) φ' 0 t) 0 := by
    intro t ht
    simpa [aqualVariationDensity, aqualVariationDerivative] using
      aqualLagrangianDensity1D_hasDerivAt_variation_at a0 G F F' ρ φ φ' v (deriv v) t 0
        hG ha0 (hFderiv _)
  have hcont' : ContinuousOn (fun t : ℝ => fderiv ℝ
      (fun ε : ℝ => aqualVariationDensity a0 G F ρ φ φ' v (deriv v) ε t) 0)
      (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun t => ContinuousLinearMap.toSpanSingleton ℝ
        (aqualVariationDerivative a0 G F' ρ v (deriv v) φ' 0 t)) (Set.uIcc a b) :=
      (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp_continuousOn hcontD
    refine hmap.congr ?_
    intro t ht
    apply ContinuousLinearMap.ext
    intro x
    rw [fderiv_eq_smul_deriv, ContinuousLinearMap.toSpanSingleton_apply]
    rw [(hderiv0 t ht).deriv]
  refine hasDerivAt_aqualAction1D_of_hasDerivAt a0 G F F' ρ φ φ' v a b hG ha0 hFderiv ?_ ?_
  · simpa [Function.uncurry, aqualVariationDensity] using hcont
  · simpa [aqualVariationDensity] using hcont'

/-- The whole-line AQUAL variation without a compact-support hypothesis.  The
support condition is replaced by the standard dominated-differentiation data for
an integral over the line: integrability at the base parameter, measurability,
and an integrable bound for the parameter derivative on a neighbourhood of zero.
No restriction on the support of the field or the variation is imposed. -/
lemma hasDerivAt_aqualActionLine_of_dominated
    (a0 G : ℝ) (F F' ρ φ φ' v v' bound : ℝ → ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0)
    (hF : ∀ y : ℝ, HasDerivAt F (F' y) y)
    (hL0_int : MeasureTheory.Integrable
      (aqualVariationDensity a0 G F ρ φ φ' v v' 0) MeasureTheory.volume)
    (hmeas : ∀ᶠ ε in nhds (0 : ℝ), MeasureTheory.AEStronglyMeasurable
      (aqualVariationDensity a0 G F ρ φ φ' v v' ε) MeasureTheory.volume)
    (hmeas' : MeasureTheory.AEStronglyMeasurable
      (aqualVariationDerivative a0 G F' ρ v v' φ' 0) MeasureTheory.volume)
    (hbound : ∀ᵐ x ∂MeasureTheory.volume, ∀ ε ∈ Set.Ioo (-1 : ℝ) 1,
      ‖aqualVariationDerivative a0 G F' ρ v v' φ' ε x‖ ≤ bound x)
    (hbound_int : MeasureTheory.Integrable bound MeasureTheory.volume) :
    HasDerivAt
      (fun ε : ℝ => ∫ x, aqualVariationDensity a0 G F ρ φ φ' v v' ε x)
      (∫ x, aqualVariationDerivative a0 G F' ρ v v' φ' 0 x) 0 := by
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun ε x => aqualVariationDensity a0 G F ρ φ φ' v v' ε x)
    (F' := fun ε x => aqualVariationDerivative a0 G F' ρ v v' φ' ε x)
    (s := Set.Ioo (-1 : ℝ) 1) (x₀ := (0 : ℝ)) (bound := bound)
    (isOpen_Ioo.mem_nhds (by norm_num)) hmeas hL0_int hmeas' hbound hbound_int (by
      filter_upwards with x
      intro ε hε
      simpa [aqualVariationDensity, aqualVariationDerivative] using
        (aqualLagrangianDensity1D_hasDerivAt_variation_at a0 G F F' ρ φ φ' v v' x ε
          hG ha0 (hF _)))
  exact hderiv

/-! ## J. From the discrete residual to the continuum residual -/

/-- A profile sampled at the sites of a path with spacing `h`. -/
noncomputable def sampledPath (φ : ℝ → ℝ) (h : ℝ) (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => φ ((i : ℝ) * h)

/-- The symmetric second difference of a profile. -/
noncomputable def secondDifference (φ : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (φ (x + h) - 2 * φ x + φ (x - h)) / h ^ 2

private lemma taylorWithinEval_two (f : ℝ → ℝ) (x y : ℝ) :
    taylorWithinEval f 2 Set.univ x y =
      f x + (y - x) * deriv f x + (1 / 2) * (y - x) ^ 2 * deriv (deriv f) x := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp [iteratedDerivWithin_succ]

private lemma taylorWithinEval_one_eq (φ : ℝ → ℝ) (x₀ y : ℝ)
    (hφ : DifferentiableAt ℝ φ x₀) (hxy : x₀ ≠ y) :
    taylorWithinEval φ 1 (Set.uIcc x₀ y) x₀ y = φ x₀ + (y - x₀) * deriv φ x₀ := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one,
    iteratedDerivWithin_zero, iteratedDerivWithin_one]
  rw [hφ.derivWithin]
  · ring
  · exact (uniqueDiffOn_uIcc hxy).uniqueDiffWithinAt Set.left_mem_uIcc

private lemma secondDifference_eq_lagrange (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x h : ℝ) (hh : h ≠ 0) :
    ∃ ξ η : ℝ, ξ ∈ Set.uIoo x (x + h) ∧ η ∈ Set.uIoo x (x - h) ∧
      secondDifference φ x h =
        (deriv (deriv φ) ξ + deriv (deriv φ) η) / 2 := by
  have hxp : x ≠ x + h := by intro hc; exact hh (by linarith)
  have hxm : x ≠ x - h := by intro hc; exact hh (by linarith)
  have hφ2 : ContDiffOn ℝ ((1 : ℕ) + 1) φ (Set.uIcc x (x + h)) := hφ.contDiffOn
  have hφ2' : ContDiffOn ℝ ((1 : ℕ) + 1) φ (Set.uIcc x (x - h)) := hφ.contDiffOn
  obtain ⟨ξ, hξ, hξeq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := φ) (x := x + h) (x₀ := x) (n := 1) hxp hφ2
  obtain ⟨η, hη, hηeq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := φ) (x := x - h) (x₀ := x) (n := 1) hxm hφ2'
  refine ⟨ξ, η, hξ, hη, ?_⟩
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiable (by norm_num) x
  have htp := taylorWithinEval_one_eq φ x (x + h) hφd hxp
  have htm := taylorWithinEval_one_eq φ x (x - h) hφd hxm
  have hξ' : φ (x + h) = φ x + h * deriv φ x + deriv (deriv φ) ξ * h ^ 2 / 2 := by
    rw [htp] at hξeq
    have hξeq' : φ (x + h) - (φ x + h * deriv φ x) = deriv (deriv φ) ξ * h ^ 2 / 2 := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one, Nat.factorial] using hξeq
    linarith
  have hη' : φ (x - h) = φ x - h * deriv φ x + deriv (deriv φ) η * h ^ 2 / 2 := by
    rw [htm] at hηeq
    have hηeq' : φ (x - h) - (φ x + (x - h - x) * deriv φ x)
        = deriv (deriv φ) η * h ^ 2 / 2 := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one, Nat.factorial] using hηeq
    have hsub : x - h - x = -h := by ring
    rw [hsub] at hηeq'
    linarith
  rw [secondDifference, hξ', hη']
  field_simp [hh]
  ring

/-- The symmetric second difference of a `C^2` profile tends to the second
derivative at the centre.  This is Taylor's theorem at order two. -/
lemma secondDifference_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (x : ℝ) :
    Filter.Tendsto (fun h : ℝ => secondDifference φ x h)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (deriv (deriv φ) x)) := by
  let r : ℝ → ℝ := fun y => φ y - taylorWithinEval φ 2 Set.univ x y
  have ht : Filter.Tendsto (fun y : ℝ => ((y - x) ^ 2)⁻¹ • r y) (nhds x) (nhds 0) := by
    have h := taylor_tendsto (s := Set.univ) convex_univ (Set.mem_univ x) (n := 2)
      hφ.contDiffOn
    simpa [r] using h
  have hplus0 : Filter.Tendsto (fun h : ℝ => x + h) (nhds 0) (nhds x) := by
    have hc : Continuous fun h : ℝ => x + h := continuous_const.add continuous_id
    simpa using hc.tendsto (0 : ℝ)
  have hplus : Filter.Tendsto (fun h : ℝ => x + h)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds x) :=
    hplus0.mono_left nhdsWithin_le_nhds
  have hminus0 : Filter.Tendsto (fun h : ℝ => x - h) (nhds 0) (nhds x) := by
    have hc : Continuous fun h : ℝ => x - h := continuous_const.sub continuous_id
    simpa using hc.tendsto (0 : ℝ)
  have hminus : Filter.Tendsto (fun h : ℝ => x - h)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds x) :=
    hminus0.mono_left nhdsWithin_le_nhds
  have hp : Filter.Tendsto (fun h : ℝ => r (x + h) / h ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h := ht.comp hplus
    convert h using 1
    ext h
    simp only [Function.comp_apply]
    ring_nf
  have hm : Filter.Tendsto (fun h : ℝ => r (x - h) / h ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h := ht.comp hminus
    convert h using 1
    ext h
    simp only [Function.comp_apply]
    ring_nf
  have hsum : Filter.Tendsto (fun h : ℝ => (r (x + h) + r (x - h)) / h ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h := hp.add hm
    convert h using 1
    · ext h
      ring_nf
    · simp
  have htarget : Filter.Tendsto
      (fun h : ℝ => deriv (deriv φ) x + (r (x + h) + r (x - h)) / h ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (deriv (deriv φ) x)) := by
    simpa [Pi.add_apply] using (tendsto_const_nhds (x := deriv (deriv φ) x)).add hsum
  have hsd : ∀ᶠ h in nhdsWithin (0 : ℝ) ({0}ᶜ),
      secondDifference φ x h = deriv (deriv φ) x + (r (x + h) + r (x - h)) / h ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [r]
    rw [secondDifference, taylorWithinEval_two φ x (x + h), taylorWithinEval_two φ x (x - h)]
    have hh0 : h ≠ 0 := by simpa using hh
    field_simp [hh0]
    ring
  exact htarget.congr' (hsd.mono fun h hh => hh.symm)

/-- The symmetric second difference of a `C^2` profile tends to the second
derivative at the centre, along any refinement whose sampled sites tend to the
centre.  The proof uses Taylor's theorem with the Lagrange remainder at each
moving centre, so no relation between the rate of the site and the spacing is
needed. -/
lemma secondDifference_tendsto_of_tendsto_site (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    {ι : Type*} {l : Filter ι} {x : ℝ} (h : ι → ℝ) (i : ι → ℕ)
    (hh : ∀ k, h k ≠ 0)
    (hh0 : Filter.Tendsto h l (nhdsWithin (0 : ℝ) ({0}ᶜ)))
    (hx : Filter.Tendsto (fun k => (i k : ℝ) * h k) l (nhds x)) :
    Filter.Tendsto (fun k => secondDifference φ ((i k : ℝ) * h k) (h k))
      l (nhds (deriv (deriv φ) x)) := by
  let xk : ι → ℝ := fun k => (i k : ℝ) * h k
  have hx' : Filter.Tendsto xk l (nhds x) := hx
  classical
  choose ξ η hξ hη heq using fun k =>
    secondDifference_eq_lagrange φ hφ (xk k) (h k) (hh k)
  have hξclose : ∀ k, |ξ k - xk k| ≤ |h k| := by
    intro k
    have hmem : ξ k ∈ Set.uIcc (xk k) (xk k + h k) := Set.Ioo_subset_Icc_self (hξ k)
    simpa using Set.abs_sub_left_of_mem_uIcc hmem
  have hηclose : ∀ k, |η k - xk k| ≤ |h k| := by
    intro k
    have hmem : η k ∈ Set.uIcc (xk k) (xk k - h k) := Set.Ioo_subset_Icc_self (hη k)
    simpa using Set.abs_sub_left_of_mem_uIcc hmem
  have hhab : Filter.Tendsto (fun k => |h k|) l (nhds 0) := by
    simpa [Function.comp_def, abs_zero] using
      (continuous_abs.tendsto 0).comp (hh0.mono_right nhdsWithin_le_nhds)
  have hξt : Filter.Tendsto ξ l (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (f := fun k => ‖ξ k - x‖)
      (g := fun k => |h k| + |xk k - x|) (fun k => abs_nonneg _) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs]
      calc |ξ k - x| = |(ξ k - xk k) + (xk k - x)| := by ring_nf
        _ ≤ |ξ k - xk k| + |xk k - x| := abs_add_le _ _
        _ ≤ |h k| + |xk k - x| := add_le_add (hξclose k) le_rfl
    · have h2 : Filter.Tendsto (fun k => |xk k - x|) l (nhds 0) := by
        simpa using (hx'.sub_const x).abs
      simpa using hhab.add h2
  have hηt : Filter.Tendsto η l (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (f := fun k => ‖η k - x‖)
      (g := fun k => |h k| + |xk k - x|) (fun k => abs_nonneg _) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs]
      calc |η k - x| = |(η k - xk k) + (xk k - x)| := by ring_nf
        _ ≤ |η k - xk k| + |xk k - x| := abs_add_le _ _
        _ ≤ |h k| + |xk k - x| := add_le_add (hηclose k) le_rfl
    · have h2 : Filter.Tendsto (fun k => |xk k - x|) l (nhds 0) := by
        simpa using (hx'.sub_const x).abs
      simpa using hhab.add h2
  have hcont2 : Continuous (deriv (deriv φ)) := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using
      hφ.continuous_iteratedDeriv 2 (by norm_num)
  have hξlim : Filter.Tendsto (fun k => deriv (deriv φ) (ξ k)) l
      (nhds (deriv (deriv φ) x)) := hcont2.tendsto x |> fun h => h.comp hξt
  have hηlim : Filter.Tendsto (fun k => deriv (deriv φ) (η k)) l
      (nhds (deriv (deriv φ) x)) := hcont2.tendsto x |> fun h => h.comp hηt
  have hhalf := (hξlim.add hηlim).div_const 2
  have hhalf' : Filter.Tendsto
      (fun k => (deriv (deriv φ) (ξ k) + deriv (deriv φ) (η k)) / 2)
      l (nhds (deriv (deriv φ) x)) := by
    convert hhalf using 1
    ring_nf
  refine hhalf'.congr' (Filter.Eventually.of_forall fun k => ?_)
  exact (heq k).symm

/-- The discrete residual of a sampled profile is the negative second difference
over `4 pi G`, plus the source term. -/
lemma sampledPath_residual_eq (G h ρ : ℝ) (φ : ℝ → ℝ) {n : ℕ}
    (i : Fin (n + 1)) (h0 : i ≠ 0) (hi : i.val < n)
    (hh : h ≠ 0) (hG : G ≠ 0) :
    discreteResidual (pathNA n) (pathNB n) G h (fun _ => ρ) (sampledPath φ h n) i
      = -h * secondDifference φ ((i : ℝ) * h) h / (4 * Real.pi * G) + h * ρ := by
  rw [discreteResidual, pathN_divergence
    (d := discreteMomentum (pathNA n) (pathNB n) G h (sampledPath φ h n)) i h0 hi]
  have hi0 : 0 < i.val := Nat.pos_of_ne_zero (fun hc => h0 (Fin.ext hc))
  have hcast : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hi0)]
    norm_num
  simp only [discreteMomentum, sampledPath, secondDifference, pathNB, pathNA]
  simp only [Fin.val_succ, Fin.val_pred, Fin.val_castSucc]
  rw [hcast]
  rw [show i.val - 1 + 1 = i.val from Nat.sub_add_cancel (Nat.succ_le_of_lt hi0)]
  push_cast
  have hsucc : ((i.val : ℝ) + 1) * h = (i.val : ℝ) * h + h := by ring
  have hpred : ((i.val : ℝ) - 1) * h = (i.val : ℝ) * h - h := by ring
  rw [hsucc, hpred]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hh, hG, hpi]
  ring

/-- Along a refinement with interior sites `i h -> x`, the normalized discrete
residual of a sampled profile tends to the negative continuum Poisson residual,
provided the symmetric second difference tends to the second derivative. -/
lemma sampledPath_residual_tendsto
    (G ρ x : ℝ) (φ : ℝ → ℝ) (hG : G ≠ 0)
    {ι : Type*} {l : Filter ι} (h : ι → ℝ) (i : ι → ℕ)
    (hpos : ∀ k, 0 < i k) (hh : ∀ k, h k ≠ 0)
    (hsecond : Filter.Tendsto
      (fun k => secondDifference φ ((i k : ℝ) * h k) (h k)) l
      (nhds (deriv (deriv φ) x))) :
    Filter.Tendsto
      (fun k => discreteResidual (pathNA (i k + 1)) (pathNB (i k + 1)) G (h k)
        (fun _ => ρ) (sampledPath φ (h k) (i k + 1))
        ⟨i k, Nat.lt_succ_of_lt (Nat.lt_succ_self (i k))⟩ / h k)
      l (nhds (ρ - deriv (deriv φ) x / (4 * Real.pi * G))) := by
  have hform : ∀ k : ι,
      discreteResidual (pathNA (i k + 1)) (pathNB (i k + 1)) G (h k)
        (fun _ => ρ) (sampledPath φ (h k) (i k + 1))
        ⟨i k, Nat.lt_succ_of_lt (Nat.lt_succ_self (i k))⟩ / h k
      = ρ - secondDifference φ ((i k : ℝ) * h k) (h k) / (4 * Real.pi * G) := by
    intro k
    have hi0 : (⟨i k, Nat.lt_succ_of_lt (Nat.lt_succ_self (i k))⟩ : Fin (i k + 1 + 1)) ≠ 0 := by
      intro hc
      have hv : i k = 0 := by
        simpa using congrArg Fin.val hc
      exact (Nat.ne_of_gt (hpos k)) hv
    rw [sampledPath_residual_eq (G := G) (h := h k) (ρ := ρ) (φ := φ)
      (n := i k + 1) (i := ⟨i k, Nat.lt_succ_of_lt (Nat.lt_succ_self (i k))⟩) hi0
      (Nat.lt_succ_self (i k)) (hh k) hG]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp [hh k, hG, hpi]
    ring
  simp_rw [hform]
  have hdiv : Filter.Tendsto
      (fun k => secondDifference φ ((i k : ℝ) * h k) (h k) / (4 * Real.pi * G))
      l (nhds (deriv (deriv φ) x / (4 * Real.pi * G))) :=
    hsecond.div_const _
  simpa using (tendsto_const_nhds (x := ρ)).sub hdiv

/-- The fixed-site version of the residual convergence: if the sampled sites are
the fixed point `x` and the spacing tends to zero, the `C^2` Taylor limit
discharges the second-difference hypothesis. -/
lemma sampledPath_residual_tendsto_of_contDiff
    (G ρ x : ℝ) (φ : ℝ → ℝ) (hG : G ≠ 0) (hφ : ContDiff ℝ 2 φ)
    {ι : Type*} {l : Filter ι} (h : ι → ℝ) (i : ι → ℕ)
    (hpos : ∀ k, 0 < i k) (hh : ∀ k, h k ≠ 0)
    (hh0 : Filter.Tendsto h l (nhdsWithin (0 : ℝ) ({0}ᶜ)))
    (hsite : ∀ k, (i k : ℝ) * h k = x) :
    Filter.Tendsto
      (fun k => discreteResidual (pathNA (i k + 1)) (pathNB (i k + 1)) G (h k)
        (fun _ => ρ) (sampledPath φ (h k) (i k + 1))
        ⟨i k, Nat.lt_succ_of_lt (Nat.lt_succ_self (i k))⟩ / h k)
      l (nhds (ρ - deriv (deriv φ) x / (4 * Real.pi * G))) := by
  apply sampledPath_residual_tendsto G ρ x φ hG h i hpos hh
  have hsd := (secondDifference_tendsto φ hφ x).comp hh0
  simpa [Function.comp_def, hsite] using hsd

/-- The residual convergence with moving sampled sites: the only remaining
hypothesis on the refinement is that the interior site tends to `x` and the
spacing tends to zero, so the second-difference limit is unconditional for
`C^2` profiles. -/
lemma sampledPath_residual_tendsto_of_contDiff_site
    (G ρ x : ℝ) (φ : ℝ → ℝ) (hG : G ≠ 0) (hφ : ContDiff ℝ 2 φ)
    {ι : Type*} {l : Filter ι} (h : ι → ℝ) (i : ι → ℕ)
    (hpos : ∀ k, 0 < i k) (hh : ∀ k, h k ≠ 0)
    (hh0 : Filter.Tendsto h l (nhdsWithin (0 : ℝ) ({0}ᶜ)))
    (hx : Filter.Tendsto (fun k => (i k : ℝ) * h k) l (nhds x)) :
    Filter.Tendsto
      (fun k => discreteResidual (pathNA (i k + 1)) (pathNB (i k + 1)) G (h k)
        (fun _ => ρ) (sampledPath φ (h k) (i k + 1))
        ⟨i k, Nat.lt_succ_of_lt (Nat.lt_succ_self (i k))⟩ / h k)
      l (nhds (ρ - deriv (deriv φ) x / (4 * Real.pi * G))) := by
  apply sampledPath_residual_tendsto G ρ x φ hG h i hpos hh
  exact secondDifference_tendsto_of_tendsto_site φ hφ h i hh hh0 hx

/-- The same convergence, expressed as minus the continuum AQUAL residual in the
Poisson limit `F' = 1`, `F'' = 0`. -/
lemma sampledPath_residual_tendsto_continuum
    (a0 G ρ x : ℝ) (φ : ℝ → ℝ) (hG : G ≠ 0)
    {ι : Type*} {l : Filter ι} (h : ι → ℝ) (i : ι → ℕ)
    (hpos : ∀ k, 0 < i k) (hh : ∀ k, h k ≠ 0)
    (hsecond : Filter.Tendsto
      (fun k => secondDifference φ ((i k : ℝ) * h k) (h k)) l
      (nhds (deriv (deriv φ) x))) :
    Filter.Tendsto
      (fun k => discreteResidual (pathNA (i k + 1)) (pathNB (i k + 1)) G (h k)
        (fun _ => ρ) (sampledPath φ (h k) (i k + 1))
        ⟨i k, Nat.lt_succ_of_lt (Nat.lt_succ_self (i k))⟩ / h k)
      l (nhds (-(aqualEulerLagrangeResidual a0 G ρ
        (deriv φ x) (deriv (deriv φ) x) (fun _ => 1) (fun _ => 0)))) := by
  have h := sampledPath_residual_tendsto G ρ x φ hG h i hpos hh hsecond
  convert h using 1
  simp [aqualEulerLagrangeResidual, aqualDivergence1D]
  ring

/-- The smooth interval variation expressed directly in terms of a `C^2` free
function: the derivative data `F'` is `deriv F`, and the parametric `C^1`
hypotheses are discharged from the smoothness of `F` and the fields.  This is
the free-function form of `hasDerivAt_aqualAction1D_of_contDiff` with the
interpolating function's differentiability stated as `ContDiff ℝ 2 F` rather
than as a separate derivative. -/
lemma hasDerivAt_aqualAction1D_of_contDiff_deriv
    (a0 G : ℝ) (F ρ φ φ' v : ℝ → ℝ) (a b : ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0)
    (hF : ContDiff ℝ 2 F)
    (hρ : ContDiffOn ℝ 1 ρ (Set.uIcc a b))
    (hφ : ContDiffOn ℝ 1 φ (Set.uIcc a b))
    (hφ' : ContDiffOn ℝ 1 φ' (Set.uIcc a b))
    (hv : ContDiffOn ℝ 1 v (Set.uIcc a b))
    (hv' : ContDiffOn ℝ 1 (deriv v) (Set.uIcc a b)) :
    HasDerivAt
      (fun ε : ℝ => aqualAction1D a0 G F ρ (φ + ε • v) (φ' + ε • deriv v) a b)
      (aqualFirstVariationIntegral a0 G (deriv F) ρ φ' v a b) 0 := by
  exact hasDerivAt_aqualAction1D_of_contDiff a0 G F (deriv F) ρ φ φ' v a b hG ha0 hF
    (fun y => hF.differentiable (by norm_num) y |>.hasDerivAt) hρ hφ hφ' hv hv'

/-- The smooth whole-line variation: the free function is `C^2`, so its
parametric derivative is `deriv F`, and the measurability hypotheses are
retained as data while the pointwise derivative hypothesis is discharged. -/
lemma hasDerivAt_aqualActionLine_of_contDiff
    (a0 G : ℝ) (F ρ φ φ' v v' : ℝ → ℝ) (bound : ℝ → ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0)
    (hF : ContDiff ℝ 2 F)
    (hL0_int : MeasureTheory.Integrable
      (aqualVariationDensity a0 G F ρ φ φ' v v' 0) MeasureTheory.volume)
    (hmeas : ∀ᶠ ε in nhds (0 : ℝ), MeasureTheory.AEStronglyMeasurable
      (aqualVariationDensity a0 G F ρ φ φ' v v' ε) MeasureTheory.volume)
    (hmeas' : MeasureTheory.AEStronglyMeasurable
      (aqualVariationDerivative a0 G (deriv F) ρ v v' φ' 0) MeasureTheory.volume)
    (hbound : ∀ᵐ x ∂MeasureTheory.volume, ∀ ε ∈ Set.Ioo (-1 : ℝ) 1,
      ‖aqualVariationDerivative a0 G (deriv F) ρ v v' φ' ε x‖ ≤ bound x)
    (hbound_int : MeasureTheory.Integrable bound MeasureTheory.volume) :
    HasDerivAt
      (fun ε : ℝ => ∫ x, aqualVariationDensity a0 G F ρ φ φ' v v' ε x)
      (∫ x, aqualVariationDerivative a0 G (deriv F) ρ v v' φ' 0 x) 0 := by
  exact hasDerivAt_aqualActionLine_of_dominated a0 G F (deriv F) ρ φ φ' v v' bound
    hG ha0 (fun y => hF.differentiable (by norm_num) y |>.hasDerivAt) hL0_int hmeas hmeas'
    (by simpa using hbound) hbound_int

/-- A concrete decay route to the whole-line variation: if the free function's
derivative is bounded by `K`, the density is integrable at the base parameter,
the field `ρ` and `φ'` are integrable, `v` and `v'` are bounded and
measurable, and `v'` is integrable, then the domination bound
`|ρ v| + (K/(4π|G|)) (|φ'|+|v'|) |v'|` is integrable and the whole-line
action is differentiable. -/
lemma hasDerivAt_aqualActionLine_of_decay
    (a0 G K : ℝ) (F F' ρ φ φ' v v' : ℝ → ℝ)
    (hG : G ≠ 0) (ha0 : a0 ≠ 0) (hK : 0 ≤ K)
    (hF : ∀ y : ℝ, HasDerivAt F (F' y) y)
    (hF'bound : ∀ y : ℝ, ‖F' y‖ ≤ K)
    (hL0_int : MeasureTheory.Integrable
      (aqualVariationDensity a0 G F ρ φ φ' v v' 0) MeasureTheory.volume)
    (hmeas : ∀ᶠ ε in nhds (0 : ℝ), MeasureTheory.AEStronglyMeasurable
      (aqualVariationDensity a0 G F ρ φ φ' v v' ε) MeasureTheory.volume)
    (hmeas' : MeasureTheory.AEStronglyMeasurable
      (aqualVariationDerivative a0 G F' ρ v v' φ' 0) MeasureTheory.volume)
    (hρ_int : MeasureTheory.Integrable ρ MeasureTheory.volume)
    (hφ'_int : MeasureTheory.Integrable φ' MeasureTheory.volume)
    (hv'_int : MeasureTheory.Integrable v' MeasureTheory.volume)
    (hv_meas : MeasureTheory.AEStronglyMeasurable v MeasureTheory.volume)
    (hv'_meas : MeasureTheory.AEStronglyMeasurable v' MeasureTheory.volume)
    (hv_bdd : ∃ C : ℝ, ∀ᵐ x ∂MeasureTheory.volume, ‖v x‖ ≤ C)
    (hv'_bdd : ∃ C : ℝ, ∀ᵐ x ∂MeasureTheory.volume, ‖v' x‖ ≤ C) :
    HasDerivAt
      (fun ε : ℝ => ∫ x, aqualVariationDensity a0 G F ρ φ φ' v v' ε x)
      (∫ x, aqualVariationDerivative a0 G F' ρ v v' φ' 0 x) 0 := by
  let C : ℝ := K / (4 * Real.pi * |G|)
  let bound : ℝ → ℝ := fun x =>
    |ρ x| * |v x| + C * (|φ' x| + |v' x|) * |v' x|
  have hbound : ∀ᵐ x ∂MeasureTheory.volume, ∀ ε ∈ Set.Ioo (-1 : ℝ) 1,
      ‖aqualVariationDerivative a0 G F' ρ v v' φ' ε x‖ ≤ bound x := by
    filter_upwards with x
    intro ε hε
    have habsε : |ε| < 1 := by
      have h1 : ε ∈ Set.Ioo (-1 : ℝ) 1 := hε
      exact abs_lt.mpr ⟨h1.1, h1.2⟩
    have htri : |φ' x + ε * v' x| ≤ |φ' x| + |v' x| := by
      calc |φ' x + ε * v' x|
          ≤ |φ' x| + |ε * v' x| := abs_add_le _ _
        _ = |φ' x| + |ε| * |v' x| := by rw [abs_mul]
        _ ≤ |φ' x| + 1 * |v' x| := by
            gcongr
        _ = |φ' x| + |v' x| := by ring
    have hmom : |aqualMomentumDensity a0 G F' (fun t => φ' t + ε * v' t) x|
        ≤ C * (|φ' x| + |v' x|) := by
      unfold aqualMomentumDensity
      calc |-(1 / (4 * Real.pi * G)) * F' ((φ' x + ε * v' x) ^ 2 / a0 ^ 2) *
            (φ' x + ε * v' x)|
          = (1 / (4 * Real.pi * |G|)) * |F' ((φ' x + ε * v' x) ^ 2 / a0 ^ 2)| *
            |φ' x + ε * v' x| := by
            rw [abs_mul, abs_mul, abs_neg, abs_div, abs_one]
            simp [abs_mul]
        _ ≤ (1 / (4 * Real.pi * |G|)) * K * (|φ' x| + |v' x|) := by
            gcongr
            · exact hF'bound _
        _ = C * (|φ' x| + |v' x|) := by
            simp only [C]
            ring
    have hderiv : |aqualVariationDerivative a0 G F' ρ v v' φ' ε x|
        ≤ |ρ x| * |v x| + C * (|φ' x| + |v' x|) * |v' x| := by
      unfold aqualVariationDerivative
      calc |-ρ x * v x + aqualMomentumDensity a0 G F' (fun t => φ' t + ε * v' t) x * v' x|
          ≤ |-ρ x * v x| + |aqualMomentumDensity a0 G F' (fun t => φ' t + ε * v' t) x * v' x| :=
            abs_add_le _ _
        _ = |ρ x| * |v x| + |aqualMomentumDensity a0 G F' (fun t => φ' t + ε * v' t) x| * |v' x| := by
            rw [abs_mul, abs_neg, abs_mul]
        _ ≤ |ρ x| * |v x| + (C * (|φ' x| + |v' x|)) * |v' x| := by
            gcongr
        _ = |ρ x| * |v x| + C * (|φ' x| + |v' x|) * |v' x| := by ring
    simpa only [bound, Real.norm_eq_abs] using hderiv
  have hbound_int : MeasureTheory.Integrable bound MeasureTheory.volume := by
    have hρabs : MeasureTheory.Integrable (fun x => |ρ x|) MeasureTheory.volume :=
      hρ_int.abs
    have hφ'abs : MeasureTheory.Integrable (fun x => |φ' x|) MeasureTheory.volume :=
      hφ'_int.abs
    have hv'abs : MeasureTheory.Integrable (fun x => |v' x|) MeasureTheory.volume :=
      hv'_int.abs
    obtain ⟨Cv, hvCv⟩ := hv_bdd
    obtain ⟨Cv', hvCv'⟩ := hv'_bdd
    have hterm1 : MeasureTheory.Integrable (fun x => |ρ x| * |v x|) MeasureTheory.volume := by
      have hprod : MeasureTheory.Integrable (fun x => ρ x * v x) MeasureTheory.volume :=
        hρ_int.mul_bdd hv_meas hvCv
      simpa only [abs_mul] using hprod.abs
    have hterm2a : MeasureTheory.Integrable (fun x => |φ' x| * |v' x|) MeasureTheory.volume := by
      have hprod : MeasureTheory.Integrable (fun x => φ' x * v' x) MeasureTheory.volume :=
        hφ'_int.mul_bdd hv'_meas hvCv'
      simpa only [abs_mul] using hprod.abs
    have hterm2b : MeasureTheory.Integrable (fun x => |v' x| * |v' x|) MeasureTheory.volume := by
      have hprod : MeasureTheory.Integrable (fun x => v' x * v' x) MeasureTheory.volume :=
        hv'_int.mul_bdd hv'_meas hvCv'
      simpa only [abs_mul] using hprod.abs
    have hterm2 : MeasureTheory.Integrable (fun x => C * (|φ' x| + |v' x|) * |v' x|) MeasureTheory.volume := by
      have hsum : MeasureTheory.Integrable (fun x => |φ' x| * |v' x| + |v' x| * |v' x|) MeasureTheory.volume :=
        hterm2a.add hterm2b
      have hmul : MeasureTheory.Integrable (fun x => C * (|φ' x| * |v' x| + |v' x| * |v' x|)) MeasureTheory.volume :=
        hsum.const_mul C
      refine hmul.congr (Filter.Eventually.of_forall (fun x => ?_))
      ring
    exact hterm1.add hterm2
  exact hasDerivAt_aqualActionLine_of_dominated a0 G F F' ρ φ φ' v v' bound
    hG ha0 hF hL0_int hmeas hmeas' hbound hbound_int

end GeneralRelativity
