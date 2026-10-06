/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Physlib.ClassicalMechanics.HamiltonianMechanics.HamiltonsEquations
public import Physlib.Mathematics.Calculus.Gradient
/-!

# The Poisson bracket

## i. Overview

The Poisson bracket packages, into a single antisymmetric bilinear operation on phase-space
functions, the way an observable evolves along a Hamiltonian flow. Following the convention of
`hamiltonEqOp` in `HamiltonsEquations.lean`, a phase-space function is a function `f : X → X → ℝ`
read as `f p q` for `p` a momentum and `q` a position, both valued in a real inner product space
`X`. The bracket of two such functions is

$$\{f, g\} := \left\langle \frac{\partial f}{\partial q}, \frac{\partial g}{\partial p}
  \right\rangle - \left\langle \frac{\partial f}{\partial p}, \frac{\partial g}{\partial q}
  \right\rangle,$$

built from the same currying-and-`gradient` idiom `hamiltonEqOp` already uses to express partial
derivatives on phase space.

## ii. Key results

- `poissonBracket` : the Poisson bracket of two phase-space functions.
- `poissonBracket_antisymm` : the bracket is antisymmetric.
- `poissonBracket_add_left`, `poissonBracket_add_right`, `poissonBracket_const_mul_left`,
  `poissonBracket_const_mul_right` : the bracket is bilinear, that is additive and homogeneous in
  each argument.
- `deriv_comp_eq_inner_gradient_add` : the time derivative of a phase-space function composed with
  a trajectory is the sum of its gradients paired with the trajectory's velocities.
- `deriv_comp_eq_poissonBracket` : along a solution of Hamilton's equations, the time derivative of
  an observable is its Poisson bracket with the Hamiltonian.

## iii. Table of contents

- A. The definition of the Poisson bracket
- B. Antisymmetry
- C. Bilinearity
- D. Time evolution along a Hamiltonian flow
  - D.1. The chain rule for a phase-space function along a trajectory
  - D.2. Time evolution as the Poisson bracket with the Hamiltonian

## iv. References

* G. J. Sussman and J. Wisdom, "Structure and Interpretation of Classical Mechanics", Section 3.2.
  <https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book-Z-H-37.html>.
  [ref: sussman_wisdom_sicm]
-/

@[expose] public section

open InnerProductSpace Time

namespace ClassicalMechanics

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

TODO "Add the canonical commutation relations for coordinate functionals, the Leibniz (product)
    rule `{f, g * h} = {f, g} * h + g * {f, h}`, and the Jacobi identity for `poissonBracket`."

/-!

## A. The definition of the Poisson bracket

-/

/-- The Poisson bracket of two phase-space functions `f g : X → X → ℝ`, each read as `f p q` for
a momentum `p` and a position `q`, at a point `(p, q)` of phase space. -/
noncomputable def poissonBracket (f g : X → X → ℝ) (p q : X) : ℝ :=
  ⟪gradient (fun q' => f p q') q, gradient (fun p' => g p' q) p⟫_ℝ -
  ⟪gradient (fun p' => f p' q) p, gradient (fun q' => g p q') q⟫_ℝ

/-!

## B. Antisymmetry

-/

/-- The Poisson bracket is antisymmetric. -/
lemma poissonBracket_antisymm (f g : X → X → ℝ) (p q : X) :
    poissonBracket f g p q = -poissonBracket g f p q := by
  simp only [poissonBracket, neg_sub]
  rw [real_inner_comm (gradient (fun p' => g p' q) p) (gradient (fun q' => f p q') q),
    real_inner_comm (gradient (fun q' => g p q') q) (gradient (fun p' => f p' q) p)]

/-!

## C. Bilinearity

The bracket is additive and homogeneous under scaling by a constant in each argument. We prove
this for the first argument; the second-argument versions follow from `poissonBracket_antisymm`.

-/

/-- The Poisson bracket is additive in its first argument, for functions differentiable in both
phase-space directions. -/
lemma poissonBracket_add_left (f₁ f₂ g : X → X → ℝ) (p q : X)
    (hf₁p : DifferentiableAt ℝ (fun p' => f₁ p' q) p)
    (hf₂p : DifferentiableAt ℝ (fun p' => f₂ p' q) p)
    (hf₁q : DifferentiableAt ℝ (fun q' => f₁ p q') q)
    (hf₂q : DifferentiableAt ℝ (fun q' => f₂ p q') q) :
    poissonBracket (fun p' q' => f₁ p' q' + f₂ p' q') g p q =
      poissonBracket f₁ g p q + poissonBracket f₂ g p q := by
  simp only [poissonBracket]
  rw [gradient_add hf₁q hf₂q, gradient_add hf₁p hf₂p, inner_add_left, inner_add_left]
  ring

/-- The Poisson bracket is homogeneous of degree one in its first argument, for a function
differentiable in both phase-space directions. -/
lemma poissonBracket_const_mul_left (c : ℝ) (f g : X → X → ℝ) (p q : X)
    (hfp : DifferentiableAt ℝ (fun p' => f p' q) p)
    (hfq : DifferentiableAt ℝ (fun q' => f p q') q) :
    poissonBracket (fun p' q' => c * f p' q') g p q = c * poissonBracket f g p q := by
  simp only [poissonBracket]
  rw [gradient_const_mul c hfq, gradient_const_mul c hfp, inner_smul_left, inner_smul_left]
  simp [mul_sub]

/-- The Poisson bracket is additive in its second argument. -/
lemma poissonBracket_add_right (f g₁ g₂ : X → X → ℝ) (p q : X)
    (hg₁p : DifferentiableAt ℝ (fun p' => g₁ p' q) p)
    (hg₂p : DifferentiableAt ℝ (fun p' => g₂ p' q) p)
    (hg₁q : DifferentiableAt ℝ (fun q' => g₁ p q') q)
    (hg₂q : DifferentiableAt ℝ (fun q' => g₂ p q') q) :
    poissonBracket f (fun p' q' => g₁ p' q' + g₂ p' q') p q =
      poissonBracket f g₁ p q + poissonBracket f g₂ p q := by
  rw [poissonBracket_antisymm f, poissonBracket_add_left g₁ g₂ f p q hg₁p hg₂p hg₁q hg₂q,
    poissonBracket_antisymm g₁ f, poissonBracket_antisymm g₂ f]
  ring

/-- The Poisson bracket is homogeneous of degree one in its second argument. -/
lemma poissonBracket_const_mul_right (c : ℝ) (f g : X → X → ℝ) (p q : X)
    (hgp : DifferentiableAt ℝ (fun p' => g p' q) p)
    (hgq : DifferentiableAt ℝ (fun q' => g p q') q) :
    poissonBracket f (fun p' q' => c * g p' q') p q = c * poissonBracket f g p q := by
  rw [poissonBracket_antisymm f, poissonBracket_const_mul_left c g f p q hgp hgq,
    poissonBracket_antisymm g f]
  ring

/-!

## D. Time evolution along a Hamiltonian flow

-/

/-!

### D.1. The chain rule for a phase-space function along a trajectory

-/

/-- The time derivative of a phase-space function `f` composed with trajectories `p q : Time → X`
is the sum of the gradients of `f` paired with the velocities `∂ₜ p` and `∂ₜ q`. -/
lemma deriv_comp_eq_inner_gradient_add (f : X → X → ℝ) (p q : Time → X) (t : Time)
    (hp : DifferentiableAt ℝ p t) (hq : DifferentiableAt ℝ q t)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (p t, q t)) :
    ∂ₜ (fun t => f (p t) (q t)) t =
      ⟪gradient (fun p' => f p' (q t)) (p t), ∂ₜ p t⟫_ℝ +
      ⟪gradient (fun q' => f (p t) q') (q t), ∂ₜ q t⟫_ℝ := by
  have h1 : HasFDerivAt (fun p' => f p' (q t))
      ((fderiv ℝ (Function.uncurry f) (p t, q t)).comp (ContinuousLinearMap.inl ℝ X X)) (p t) :=
    HasFDerivAt.comp (f := fun e : X => (e, q t)) (p t) hf.hasFDerivAt
      (hasFDerivAt_prodMk_left (p t) (q t))
  have h2 : HasFDerivAt (fun q' => f (p t) q')
      ((fderiv ℝ (Function.uncurry f) (p t, q t)).comp (ContinuousLinearMap.inr ℝ X X)) (q t) :=
    HasFDerivAt.comp (f := fun e : X => (p t, e)) (q t) hf.hasFDerivAt
      (hasFDerivAt_prodMk_right (p t) (q t))
  have hF : HasFDerivAt (fun t => f (p t) (q t))
      ((fderiv ℝ (Function.uncurry f) (p t, q t)).comp ((fderiv ℝ p t).prod (fderiv ℝ q t))) t :=
    HasFDerivAt.comp (f := fun t => (p t, q t)) t hf.hasFDerivAt
      (hp.hasFDerivAt.prodMk hq.hasFDerivAt)
  rw [inner_gradient_left, inner_gradient_left, h1.fderiv, h2.fderiv, Time.deriv_eq, hF.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← Time.deriv_eq, ← map_add]

/-!

### D.2. Time evolution as the Poisson bracket with the Hamiltonian

-/

/-- Along a solution of Hamilton's equations for a Hamiltonian `H`, the time derivative of a
phase-space observable `f` is its Poisson bracket with `H t`. -/
theorem deriv_comp_eq_poissonBracket (H : Time → X → X → ℝ) (p q : Time → X) (f : X → X → ℝ)
    (t : Time) (heq : hamiltonEqOp H p q = 0)
    (hp : DifferentiableAt ℝ p t) (hq : DifferentiableAt ℝ q t)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (p t, q t)) :
    ∂ₜ (fun t => f (p t) (q t)) t = poissonBracket f (H t) (p t) (q t) := by
  obtain ⟨hq', hp'⟩ := (hamiltonEqOp_eq_zero_iff_hamiltons_equations H p q).mp heq
  rw [deriv_comp_eq_inner_gradient_add f p q t hp hq hf, hq' t, hp' t, inner_neg_right]
  unfold poissonBracket
  ring

end ClassicalMechanics
