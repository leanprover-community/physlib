/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Calculus.PartialDerivatives
public import Physlib.Mathematics.VariationalCalculus.HasVarGradient
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# A. Euler–Lagrange equations

The Euler–Lagrange equations characterize stationary trajectories of an action functional. For a
Lagrangian `L t q v`, they compare the gradient with respect to position to the time derivative of
the gradient with respect to velocity.

## A.1. Mathematical setting

Trajectories take values in a complete real inner-product space `X`. The Lagrangian has type
`Time → X → X → ℝ`, and the corresponding action is the time integral of
`L t (q t) (∂ₜ q t)`.

## A.2. Main definitions and results

- `eulerLagrangeOp` defines the Euler–Lagrange operator
  `∂L/∂q - ∂ₜ (∂L/∂v)` along a trajectory.
- `eulerLagrangeOp_eq` exposes its pointwise formula.
- `eulerLagrangeOp_zero` evaluates the operator for the zero Lagrangian.
- `euler_lagrange_varGradient` proves that the variational gradient of the action equals the
  Euler–Lagrange operator for smooth trajectories and Lagrangians.
- `canonicalMomentum` and `eulerLagrange` give the covector form `∂L/∂q - dₜ(∂L/∂q̇)` for a
  Lagrangian `L : ℝ × E × E → ℝ` on a normed space `E`, with `contDiff_eulerLagrange`,
  `eulerLagrange_congr` and `eulerLagrange_congr_lagrangian`.

## A.3. Current scope

The result is formulated for smooth data and Hilbert-space-valued trajectories. Applications to
specific mechanical systems are developed in their corresponding modules, where vanishing of the
operator becomes the system's equation of motion.

-/

@[expose] public section

open MeasureTheory ContDiff InnerProductSpace Time

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

namespace ClassicalMechanics

/-- The Euler Lagrange operator, for a trajectory `q : Time → X`,
  and a lagrangian `Time → X → X → ℝ`, the Euler-Lagrange operator is
    `∂L/∂q - dₜ(∂L/∂(dₜ q))`. -/
noncomputable def eulerLagrangeOp (L : Time → X → X → ℝ) (q : Time → X) : Time → X := fun t =>
  gradient (L t · (∂ₜ q t)) (q t) - ∂ₜ (fun t' => gradient (L t' (q t') ·) (∂ₜ q t')) t

lemma eulerLagrangeOp_eq (L : Time → X → X → ℝ) (q : Time → X) :
    eulerLagrangeOp L q = fun t => gradient (L t · (∂ₜ q t)) (q t)
    - ∂ₜ (fun t' => gradient (L t' (q t') ·) (∂ₜ q t')) t := by rfl

lemma eulerLagrangeOp_zero (q : Time → X) :
    eulerLagrangeOp (fun _ _ _ => 0) q = fun _ => 0 := by
  simp [eulerLagrangeOp_eq, Time.deriv_eq]

/-- The variational derivative of the action `∫ t, L t (q' t) (deriv q' t)` for a Lagrangian `L`
  is equal to the `eulerLagrangeOp`. -/
theorem euler_lagrange_varGradient
    (L : Time → X → X → ℝ) (q : Time → X)
    (hq : ContDiff ℝ ∞ q) (hL : ContDiff ℝ ∞ ↿L) :
    (δ (q':=q), ∫ t, L t (q' t) (fderiv ℝ q' t 1)) = eulerLagrangeOp L q := by
  simp only [eulerLagrangeOp_eq, Time.deriv_eq]
  apply HasVarGradientAt.varGradient
  apply HasVarGradientAt.intro _
  · apply HasVarAdjDerivAt.comp
      (F := fun (φ : Time → X × X) t => L t (φ t).fst (φ t).snd)
      (G := fun (φ : Time → X) t => (φ t, fderiv ℝ φ t 1))
    · apply HasVarAdjDerivAt.fmap (f := fun t => ↿(L t))
      · fun_prop
      · fun_prop
      intro x u
      apply DifferentiableAt.hasAdjFDerivAt
      apply ContDiff.differentiable (n := ∞) (by fun_prop) (by simp)
    · apply HasVarAdjDerivAt.prod (F:=fun φ => φ)
      · apply HasVarAdjDerivAt.id _ hq
      · apply HasVarAdjDerivAt.fderiv (hu := hq)
  case hgrad =>
    funext t
    simp (disch := fun_prop) [sub_eq_add_neg]
    congr
    all_goals
      try funext t
      rw [gradient_eq_adjFDeriv, adjFDeriv_uncurry] <;>
        apply ContDiff.differentiable (n := ∞) (by fun_prop) (by simp)

section Covector

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical momentum `∂L/∂q̇` of a curve `q`. -/
noncomputable def canonicalMomentum (L : ℝ × E × E → ℝ) (q : ℝ → E) (τ : ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun v ↦ L (τ, q τ, v)) (deriv q τ)

/-- The Euler-Lagrange covector `∂L/∂q - dₜ(∂L/∂q̇)` of a curve `q`, for a Lagrangian on
`ℝ × E × E`; the covector counterpart of `eulerLagrangeOp`. -/
noncomputable def eulerLagrange (L : ℝ × E × E → ℝ) (q : ℝ → E) (τ : ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun x ↦ L (τ, x, deriv q τ)) (q τ) - deriv (canonicalMomentum L q) τ

/-- The Euler-Lagrange covector of a smooth curve is smooth. -/
lemma contDiff_eulerLagrange {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (eulerLagrange L q) :=
  (contDiff_fderiv_partial_snd hL contDiff_id hq (contDiff_infty_iff_deriv.1 hq).2).sub
    (contDiff_infty_iff_deriv.1
      (contDiff_fderiv_partial_thd hL contDiff_id hq (contDiff_infty_iff_deriv.1 hq).2)).2

/-- The Euler-Lagrange covector at `τ` depends only on the germ of the curve at `τ`. -/
lemma eulerLagrange_congr {L : ℝ × E × E → ℝ} {q g : ℝ → E} {τ : ℝ} (h : q =ᶠ[𝓝 τ] g) :
    eulerLagrange L q τ = eulerLagrange L g τ := by
  unfold eulerLagrange canonicalMomentum
  rw [h.deriv_eq, h.eq_of_nhds]
  congr 1
  refine EventuallyEq.deriv_eq ?_
  filter_upwards [h.eventuallyEq_nhds] with σ hσ
  rw [hσ.eq_of_nhds, hσ.deriv_eq]

/-- The Euler-Lagrange covector only depends on the Lagrangian near the curve. -/
lemma eulerLagrange_congr_lagrangian {L L' : ℝ × E × E → ℝ} {q : ℝ → E} {τ : ℝ} {N : Set E}
    (hN : IsOpen N) (hq : ∀ᶠ σ in 𝓝 τ, q σ ∈ N) (h : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = L' p) :
    eulerLagrange L q τ = eulerLagrange L' q τ := by
  unfold eulerLagrange canonicalMomentum
  have hτ : q τ ∈ N := hq.self_of_nhds
  have h1 : (fun y ↦ L (τ, y, deriv q τ)) =ᶠ[𝓝 (q τ)] fun y ↦ L' (τ, y, deriv q τ) := by
    filter_upwards [hN.mem_nhds hτ] with y hy using h _ hy
  have h2 : (fun σ ↦ fderiv ℝ (fun v ↦ L (σ, q σ, v)) (deriv q σ)) =ᶠ[𝓝 τ]
      fun σ ↦ fderiv ℝ (fun v ↦ L' (σ, q σ, v)) (deriv q σ) := by
    filter_upwards [hq] with σ hσ
    exact congrArg (fun f ↦ fderiv ℝ f (deriv q σ)) (funext fun v ↦ h _ hσ)
  rw [h1.fderiv_eq, h2.deriv_eq]

end Covector

end ClassicalMechanics
