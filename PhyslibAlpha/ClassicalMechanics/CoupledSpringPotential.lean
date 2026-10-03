/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import PhyslibAlpha.Mathematics.PartialDerivativeTest
/-!
# Coupled spring potential

The coupled spring potential x₀² + x₀x₁ + x₁² has a local minimum at the origin.

## i. Overview

As a proof of concept, we use the second derivative test in
`PhyslibAlpha.Mathematics.PartialDerivativeTest`
to prove that the coupled spring potential
`U := fun x : EuclideanSpace ℝ (Fin 2) => (x 0)^2 + x 0 * x 1 + (x 1)^2`
has a local minimum at zero.

To apply the test we show the potential is analytic, that its gradient vanishes at the origin, and
that its second derivative quadratic map is positive definite there.

## ii. Key results

- `couplingPotential` : the potential energy of a pair of coupled springs.
- `couplingPotential_gradient_zero` : the gradient of the potential vanishes at the origin.
- `couplingPotential_posDef` : the second derivative quadratic map is positive definite at the
  origin.
- `coupled_spring_potential` : the coupled spring potential has a local minimum at zero.

## iii. Table of contents

- A. The coupled spring potential
- B. Analyticity and derivatives
- C. The local minimum at the origin

## iv. References

* None.

-/

@[expose] public section


/-!

## A. The coupled spring potential

-/

/-- The potential energy of a pair of coupled springs. -/
noncomputable def couplingPotential (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (x 0) ^ 2 + x 0 * x 1 + (x 1) ^ 2

/-!

## B. Analyticity and derivatives

-/

/-
The coupling potential is analytic everywhere (it is a polynomial).
-/
lemma couplingPotential_analyticAt (z : EuclideanSpace ℝ (Fin 2)) :
    AnalyticAt ℝ couplingPotential z := by
  have h0 : AnalyticAt ℝ (fun x : EuclideanSpace ℝ (Fin 2) => x 0) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) 0).analyticAt z
  have h1 : AnalyticAt ℝ (fun x : EuclideanSpace ℝ (Fin 2) => x 1) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) 1).analyticAt z
  unfold couplingPotential
  exact ((h0.pow 2).add (h0.mul h1)).add (h1.pow 2)

/-
The derivative of the coupling potential at any point, as an explicit
linear functional.
-/
lemma couplingPotential_hasFDerivAt (x : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt couplingPotential
      ((2 * x 0 + x 1) • (EuclideanSpace.proj (𝕜 := ℝ) 0)
        + (x 0 + 2 * x 1) • (EuclideanSpace.proj (𝕜 := ℝ) 1)) x := by
  have h0 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => x 0)
    (EuclideanSpace.proj (𝕜 := ℝ) 0) x := by
    exact ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) 0)
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => x 1)
    (EuclideanSpace.proj (𝕜 := ℝ) 1) x := by
    norm_num [hasFDerivAt_iff_isLittleO_nhds_zero];
  convert! HasFDerivAt.add (HasFDerivAt.add (h0.pow 2) (h0.mul h1)) (h1.pow 2) using 1
  ext; norm_num; ring

/-
The gradient of the coupling potential vanishes at the origin.
-/
lemma couplingPotential_gradient_zero :
    gradient couplingPotential (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) = 0 := by
  convert! (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm_apply_eq.mpr ?_;
  convert! HasFDerivAt.fderiv (couplingPotential_hasFDerivAt _) using 1
  norm_num [fderiv_apply_one_eq_deriv]

/-
The value of the second derivative quadratic map of the coupling potential.
-/
lemma couplingPotential_iteratedFDeriv_two (z : EuclideanSpace ℝ (Fin 2))
    (a b : EuclideanSpace ℝ (Fin 2)) :
    iteratedFDeriv ℝ 2 couplingPotential z ![a, b]
      = 2 * a 0 * b 0 + a 0 * b 1 + a 1 * b 0 + 2 * a 1 * b 1 := by
  have h_second_deriv : fderiv ℝ (fderiv ℝ couplingPotential) z
    = (2 • (EuclideanSpace.proj (𝕜 := ℝ) 0).smulRight
    (EuclideanSpace.proj (𝕜 := ℝ) 0) + (EuclideanSpace.proj (𝕜 := ℝ) 0).smulRight
    (EuclideanSpace.proj (𝕜 := ℝ) 1) + (EuclideanSpace.proj (𝕜 := ℝ) 1).smulRight
    (EuclideanSpace.proj (𝕜 := ℝ) 0) + 2 • (EuclideanSpace.proj (𝕜 := ℝ) 1).smulRight
    (EuclideanSpace.proj (𝕜 := ℝ) 1)) := by
    refine' HasFDerivAt.fderiv _;
    rw [show fderiv ℝ couplingPotential = _ from funext fun x =>
      HasFDerivAt.fderiv (couplingPotential_hasFDerivAt x)];
    rw [hasFDerivAt_iff_isLittleO_nhds_zero];
    norm_num [Asymptotics.isLittleO_iff];
    intro ε hε; filter_upwards [Metric.ball_mem_nhds _ hε] with x hx; ring_nf;
    erw [show ((z.ofLp 0 * 2 + x.ofLp 0 * 2 + z.ofLp 1 + x.ofLp 1) • EuclideanSpace.proj 0
      + (z.ofLp 0 + x.ofLp 0 + z.ofLp 1 * 2 + x.ofLp 1 * 2) • EuclideanSpace.proj 1
      - ((z.ofLp 0 * 2 + z.ofLp 1) • EuclideanSpace.proj 0 + (z.ofLp 0 + z.ofLp 1 * 2)
      • EuclideanSpace.proj 1) - (2 • x.ofLp 0 • EuclideanSpace.proj 0 + x.ofLp 0
      • EuclideanSpace.proj 1 + x.ofLp 1 • EuclideanSpace.proj 0 + 2 • x.ofLp 1
      • EuclideanSpace.proj 1) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) = 0 from by
        ext; norm_num; ring]; norm_num [hε.le];
    positivity;
  rw [iteratedFDeriv_succ_apply_right]; simp +decide [h_second_deriv]; ring!;

/-!

## C. The local minimum at the origin

-/

/-
The second derivative quadratic map of the coupling potential is positive definite
at the origin.
-/
lemma couplingPotential_posDef :
    (iteratedFDerivQuadraticMap couplingPotential
    (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))).PosDef := by
  intros y hy;
  convert! (show 0 < 2 * y 0 ^ 2 + 2 * y 0 * y 1 + 2 * y 1 ^ 2 by
              exact not_le.mp fun h => hy <| by
                ext i
                fin_cases i <;> norm_num <;> nlinarith! [sq_nonneg (y.ofLp 0 + y.ofLp 1)]) using 1
  generalize_proofs at *;
  convert! couplingPotential_iteratedFDeriv_two !₂[0, 0] y y using 1; ring!

lemma coupled_spring_potential :
    let U := fun x : EuclideanSpace ℝ (Fin 2) => (x 0)^2 + x 0 * x 1 + (x 1)^2
    IsLocalMin U {
        ofLp := ![0,0]
    } := by
  show IsLocalMin couplingPotential (!₂[0, 0] : EuclideanSpace ℝ (Fin 2))
  exact second_derivative_test_analyticAt couplingPotential_gradient_zero
    (couplingPotential_analyticAt _) couplingPotential_posDef
