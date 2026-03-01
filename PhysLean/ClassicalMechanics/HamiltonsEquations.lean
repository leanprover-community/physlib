/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
import PhysLean.Mathematics.VariationalCalculus.HasVarGradient
/-!

# Hamilton's equations

In this module, given a Hamiltonian function `H : Time → X → X → ℝ`,
we define the operator `hamiltonEqOp`
which when equals zero implies hamilton's equations.

We show that the variational derivative of the action functional
`∫ ⟪p, dq/dt⟫ - H(t, p, q) dt` is equal to the `hamiltonEqOp`
applied to `(p, q)`.

## References

- G. J. Sussman and J. Wisdom, "Structure and Interpretation of Classical Mechanics", Section 3.1.2.
<https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book-Z-H-36.html#%_sec_3.1.2>

-/

open MeasureTheory ContDiff InnerProductSpace Time

namespace ClassicalMechanics

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- Given a hamiltonian `H : Time → X → X → ℝ` the operator which when
  set to zero implies the Hamilton equations. -/
noncomputable def hamiltonEqOp (H : Time → X → X → ℝ) (p : Time → X) (q : Time → X) :
    Time → X × X :=
  fun t => (∂ₜ q t + -gradient (fun x => H t x (q t)) (p t),
    - ∂ₜ p t + -gradient (fun x => H t (p t) x) (q t))

lemma hamiltonEqOp_eq (H : Time → X → X → ℝ) (p : Time → X) (q : Time → X) :
    hamiltonEqOp H p q = fun t => (∂ₜ q t + -gradient (fun x => H t x (q t)) (p t),
      - ∂ₜ p t + -gradient (fun x => H t (p t) x) (q t)) := by
  rfl

lemma hamiltonEqOp_eq_zero_iff_hamiltons_equations (H : Time → X → X → ℝ)
    (p : Time → X) (q : Time → X) :
    hamiltonEqOp H p q = 0 ↔
    (∀ t, ∂ₜ q t = gradient (fun x => H t x (q t)) (p t)) ∧
    (∀ t, ∂ₜ p t = -gradient (fun x => H t (p t) x) (q t)) := by
  simp [hamiltonEqOp_eq]
  simp_all only [Time.deriv_eq]
  rw [funext_iff]
  simp_all only [Pi.zero_apply, Prod.mk_eq_zero]
  apply Iff.intro
  · intro h1
    apply And.intro
    · intro t
      conv_rhs =>
        rw [← add_zero (gradient (fun x => H t x (q t)) (p t)), ← (h1 t).1]
      simp
    · intro t
      conv_lhs =>
        rw [← add_zero (fderiv ℝ p t 1), ← (h1 t).2]
      simp
  · intro a x
    simp_all only [add_neg_cancel, neg_neg, and_self]

theorem hamiltons_equations_varGradient
    (H : Time → X → X → ℝ) (pq : Time → X × X) (hp : ContDiff ℝ ∞ pq)
    (hL : ContDiff ℝ ∞ ↿H) :
    (δ (pq':= pq), ∫ t, ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ - H t (pq' t).1 (pq' t).2) =
    fun t => hamiltonEqOp H (fun t => (pq t).1) (fun t => (pq t).2) t := by
  apply HasVarGradientAt.varGradient
  apply HasVarGradientAt.intro _
  · apply HasVarAdjDerivAt.add
    · let i := fun (t : Time) (x : X × X) => ⟪x.1, x.2⟫_ℝ
      apply HasVarAdjDerivAt.comp
        (F := fun (φ : Time → X × X) t => i t (φ t))
        (G := fun (φ : Time → X × X) t => ((φ t).1, fderiv ℝ (Prod.snd ∘ φ) t 1))
      · apply HasVarAdjDerivAt.fmap
        · fun_prop
        · fun_prop
        intro t x
        apply DifferentiableAt.hasAdjFDerivAt
        fun_prop
      · apply HasVarAdjDerivAt.prod
        · apply HasVarAdjDerivAt.fst
          apply HasVarAdjDerivAt.id
          fun_prop
        · apply HasVarAdjDerivAt.fderiv' (F := fun (φ : Time → X × X) t => (φ t).2)
          apply HasVarAdjDerivAt.fmap
          · fun_prop
          · fun_prop
          intro t x
          apply DifferentiableAt.hasAdjFDerivAt
          fun_prop
    · apply HasVarAdjDerivAt.neg
      let H' := fun t => ↿(H t)
      change HasVarAdjDerivAt (fun φ x => H' x (φ x)) _ pq
      apply HasVarAdjDerivAt.fmap
      · fun_prop
      · fun_prop
      intro x u
      apply DifferentiableAt.hasAdjFDerivAt
      apply Differentiable.differentiableAt
      apply ContDiff.differentiable
      fun_prop
      simp
  · simp only [adjFDeriv_prod_snd, Prod.mk_add_mk, add_zero, zero_add]
    funext x
    rw [adjFDeriv_uncurry]
    swap
    · apply ContDiff.differentiable
      fun_prop
      simp
    simp only [Prod.neg_mk, Prod.mk_add_mk]
    rw [adjFDeriv_inner]
    simp only [one_smul]
    conv_rhs =>
      enter [2, 1, 1, 1, 2, x]
      rw [adjFDeriv_inner]
      simp
    rw [← gradient_eq_adjFDeriv, ← gradient_eq_adjFDeriv]
    rfl
    · apply ContDiff.differentiable
      fun_prop
      simp
    · apply ContDiff.differentiable
      fun_prop
      simp

end ClassicalMechanics
