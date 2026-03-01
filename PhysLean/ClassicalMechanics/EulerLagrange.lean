/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
/-!

# Euler-Lagrange equations

In this module we define the Euler-Lagrange operator `eulerLagrangeOp`,
and prove the that the variational derivative of the action functional
`∫ L(t, q(t), dₜ q(t)) dt` is equal to the Euler-Lagrange operator applied to the trajectory `q`.

-/

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

/- The variational derivative of `L t (q' t) (deriv q' t))` for a lagrangian `L`
  is equal to the `eulerLagrangeOp`. -/
theorem euler_lagrange_varGradient
    (L : Time → X → X → ℝ) (q : Time → X)
    (hq : ContDiff ℝ ∞ q) (hL : ContDiff ℝ ∞ ↿L) :
    (δ (q':=q), ∫ t, L t (q' t) (fderiv ℝ q' t 1)) = eulerLagrangeOp L q := by
  rw [eulerLagrangeOp_eq]
  simp only [Time.deriv_eq]
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
      apply Differentiable.differentiableAt
      apply ContDiff.differentiable
      fun_prop
      simp
    · apply HasVarAdjDerivAt.prod (F:=fun φ => φ)
      · apply HasVarAdjDerivAt.id _ hq
      · apply HasVarAdjDerivAt.fderiv
        · exact hq
  case hgrad =>
    funext t
    simp (disch:=fun_prop) only
    simp[sub_eq_add_neg]
    congr
    rw [gradient_eq_adjFDeriv, adjFDeriv_uncurry]
    apply ContDiff.differentiable (n := ∞) (by fun_prop) (by simp)
    apply ContDiff.differentiable (n := ∞) (by fun_prop) (by simp)
    funext t
    rw [gradient_eq_adjFDeriv, adjFDeriv_uncurry]
    apply ContDiff.differentiable (n := ∞) (by fun_prop) (by simp)
    apply ContDiff.differentiable (n := ∞) (by fun_prop) (by simp)

end ClassicalMechanics
