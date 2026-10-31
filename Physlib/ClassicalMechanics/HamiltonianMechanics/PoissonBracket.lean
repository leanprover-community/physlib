/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Physlib.ClassicalMechanics.HamiltonianMechanics.HamiltonsEquations
public import Physlib.ClassicalMechanics.HamiltonianMechanics.PhaseSpace
/-!

# The Poisson bracket

The Poisson bracket of phase-space observables and their Hamiltonian time evolution.

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
- `poissonBracket_eq_of_hasGradientAt` : computes the bracket from known partial gradients.
- `poissonBracket_antisymm` : the bracket is antisymmetric.
- `poissonBracket_self` : every observable Poisson-commutes with itself.
- `poissonBracket_add_left`, `poissonBracket_add_right`, `poissonBracket_const_mul_left`,
  `poissonBracket_const_mul_right` : the bracket is bilinear, that is additive and homogeneous in
  each argument.
- `poissonBracket_mul_left`, `poissonBracket_mul_right` : the bracket satisfies the Leibniz rule
  in each argument.
- `deriv_comp_eq_inner_gradient_add` : the time derivative of a phase-space function composed with
  a trajectory is the sum of its gradients paired with the trajectory's velocities.
- `deriv_comp_eq_poissonBracket` : along a solution of Hamilton's equations, the time derivative of
  an observable is its Poisson bracket with the Hamiltonian.
- `fderiv_partial_comm` : mixed partial derivatives of a `C²` phase-space function commute.
- `poissonBracket_jacobi` : Poisson brackets satisfy the Jacobi identity.
- `poissonBracket_position_position`, `poissonBracket_momentum_momentum` : two functions of
  position alone, or of momentum alone, have vanishing Poisson bracket.
- `poissonBracket_inner_position_inner_momentum` : the canonical Poisson bracket
  `{⟪a, q⟫, ⟪b, p⟫} = ⟪a, b⟫` of linear coordinate functionals.
- `poissonBracket_coord_position_coord_momentum` : on Euclidean space, the canonical Poisson
  bracket `{qᵢ, pⱼ} = δᵢⱼ`.

## iii. Table of contents

- A. The definition of the Poisson bracket
- B. Antisymmetry
- C. Bilinearity
- D. The Leibniz rule
- E. Time evolution along a Hamiltonian flow
  - E.1. The chain rule for a phase-space function along a trajectory
  - E.2. Time evolution as the Poisson bracket with the Hamiltonian
- F. The Jacobi identity
  - F.1. Poisson bracket with derivatives falling on `g`
  - F.2. The Jacobi identity
- G. The canonical Poisson brackets
  - G.1. Functions of position alone and of momentum alone
  - G.2. Coordinate functionals

## iv. References

* G. J. Sussman and J. Wisdom, "Structure and Interpretation of Classical Mechanics", Section 3.2.
  <https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book-Z-H-37.html>.
  [ref: sussman_wisdom_sicm]
-/

@[expose] public section

open InnerProductSpace Time

namespace ClassicalMechanics

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-!

## A. The definition of the Poisson bracket

-/

/-- The Poisson bracket of two phase-space functions `f g : X → X → ℝ`, each read as `f p q` for
a momentum `p` and a position `q`, at a point `(p, q)` of phase space. -/
noncomputable def poissonBracket (f g : X → X → ℝ) (p q : X) : ℝ :=
  ⟪gradient (fun q' => f p q') q, gradient (fun p' => g p' q) p⟫_ℝ -
  ⟪gradient (fun p' => f p' q) p, gradient (fun q' => g p q') q⟫_ℝ

/-- The Poisson bracket of two phase-space functions whose partial gradients at `(p, q)` are
known. -/
lemma poissonBracket_eq_of_hasGradientAt {f g : X → X → ℝ} {p q fp fq gp gq : X}
    (hfp : HasGradientAt (fun p' => f p' q) fp p) (hfq : HasGradientAt (fun q' => f p q') fq q)
    (hgp : HasGradientAt (fun p' => g p' q) gp p) (hgq : HasGradientAt (fun q' => g p q') gq q) :
    poissonBracket f g p q = ⟪fq, gp⟫_ℝ - ⟪fp, gq⟫_ℝ := by
  rw [poissonBracket, hfq.gradient, hgp.gradient, hfp.gradient, hgq.gradient]

/-!

## B. Antisymmetry

-/

/-- The Poisson bracket is antisymmetric. -/
lemma poissonBracket_antisymm (f g : X → X → ℝ) (p q : X) :
    poissonBracket f g p q = -poissonBracket g f p q := by
  simp only [poissonBracket, neg_sub]
  rw [real_inner_comm (gradient (fun p' => g p' q) p) (gradient (fun q' => f p q') q),
    real_inner_comm (gradient (fun q' => g p q') q) (gradient (fun p' => f p' q) p)]

/-- The Poisson bracket of a phase-space function with itself vanishes. -/
lemma poissonBracket_self (f : X → X → ℝ) (p q : X) : poissonBracket f f p q = 0 := by
  have h := poissonBracket_antisymm f f p q
  linarith

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

## D. The Leibniz rule

-/

/-- The Poisson bracket satisfies the Leibniz rule in its first argument. -/
lemma poissonBracket_mul_left (f₁ f₂ g : X → X → ℝ) (p q : X)
    (hf₁p : DifferentiableAt ℝ (fun p' => f₁ p' q) p)
    (hf₂p : DifferentiableAt ℝ (fun p' => f₂ p' q) p)
    (hf₁q : DifferentiableAt ℝ (fun q' => f₁ p q') q)
    (hf₂q : DifferentiableAt ℝ (fun q' => f₂ p q') q) :
    poissonBracket (fun p' q' => f₁ p' q' * f₂ p' q') g p q =
      poissonBracket f₁ g p q * f₂ p q + f₁ p q * poissonBracket f₂ g p q := by
  simp only [poissonBracket]
  rw [(hf₁q.hasGradientAt.mul hf₂q.hasGradientAt).gradient,
    (hf₁p.hasGradientAt.mul hf₂p.hasGradientAt).gradient]
  simp only [inner_add_left, real_inner_smul_left]
  ring

/-- The Poisson bracket satisfies the Leibniz rule in its second argument. -/
lemma poissonBracket_mul_right (f g₁ g₂ : X → X → ℝ) (p q : X)
    (hg₁p : DifferentiableAt ℝ (fun p' => g₁ p' q) p)
    (hg₂p : DifferentiableAt ℝ (fun p' => g₂ p' q) p)
    (hg₁q : DifferentiableAt ℝ (fun q' => g₁ p q') q)
    (hg₂q : DifferentiableAt ℝ (fun q' => g₂ p q') q) :
    poissonBracket f (fun p' q' => g₁ p' q' * g₂ p' q') p q =
      poissonBracket f g₁ p q * g₂ p q + g₁ p q * poissonBracket f g₂ p q := by
  rw [poissonBracket_antisymm f, poissonBracket_mul_left g₁ g₂ f p q hg₁p hg₂p hg₁q hg₂q,
    poissonBracket_antisymm g₁ f, poissonBracket_antisymm g₂ f]
  ring

/-!

## E. Time evolution along a Hamiltonian flow

-/

/-!

### E.1. The chain rule for a phase-space function along a trajectory

-/

/-- The time derivative of a phase-space function `f` composed with trajectories `p q : Time → X`
is the sum of the gradients of `f` paired with the velocities `∂ₜ p` and `∂ₜ q`. -/
lemma deriv_comp_eq_inner_gradient_add (f : X → X → ℝ) (p q : Time → X) (t : Time)
    (hp : DifferentiableAt ℝ p t) (hq : DifferentiableAt ℝ q t)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (p t, q t)) :
    ∂ₜ (fun t => f (p t) (q t)) t =
      ⟪gradient (fun p' => f p' (q t)) (p t), ∂ₜ p t⟫_ℝ +
      ⟪gradient (fun q' => f (p t) q') (q t), ∂ₜ q t⟫_ℝ := by
  have hF : HasFDerivAt (fun t => f (p t) (q t))
      ((fderiv ℝ ↿f (p t, q t)).comp ((fderiv ℝ p t).prod (fderiv ℝ q t))) t :=
    HasFDerivAt.comp (f := fun t => (p t, q t)) t hf.hasFDerivAt
      (hp.hasFDerivAt.prodMk hq.hasFDerivAt)
  rw [inner_gradient_left, inner_gradient_left, (hasFDerivAt_uncurry_fst hf).fderiv,
    (hasFDerivAt_uncurry_snd hf).fderiv, Time.deriv_eq, hF.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← Time.deriv_eq, ← map_add]
/-!

### E.2. Time evolution as the Poisson bracket with the Hamiltonian

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

/-!

## F. The Jacobi identity

-/

/-!

### F.1. Poisson bracket with derivatives falling on `g`

-/

/-- The Poisson bracket, written with the derivatives falling on `g`. -/
lemma poissonBracket_eq_fderiv (f g : X → X → ℝ) (p q : X) :
    poissonBracket f g p q =
      fderiv ℝ (fun p' => g p' q) p (gradient (fun q' => f p q') q) -
        fderiv ℝ (fun q' => g p q') q (gradient (fun p' => f p' q) p) := by
  simp only [poissonBracket, inner_gradient_right, conj_trivial]

/-- The same, for a gradient in a second variable (mixed second derivatives). -/
lemma inner_fderiv_gradient_param (G : X → X → ℝ) (x y v w : X) :
    ⟪fderiv ℝ (fun x' => gradient (G x') y) x v, w⟫_ℝ =
      fderiv ℝ (fun x' => fderiv ℝ (G x') y) x v w := by
  change ⟪fderiv ℝ (⇑(toDual ℝ X).symm ∘ fun x' => fderiv ℝ (G x') y) x v, w⟫_ℝ = _
  rw [(toDual ℝ X).symm.comp_fderiv, ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

/-!

### F.2. The Jacobi identity

-/

/-- The Jacobi identity for the Poisson bracket. -/
lemma poissonBracket_jacobi (f₁ f₂ f₃ : X → X → ℝ) (p q : X)
    (hf₁ : ContDiff ℝ 2 (Function.uncurry f₁))
    (hf₂ : ContDiff ℝ 2 (Function.uncurry f₂))
    (hf₃ : ContDiff ℝ 2 (Function.uncurry f₃)) :
    poissonBracket f₁ (poissonBracket f₂ f₃) p q +
    poissonBracket f₂ (poissonBracket f₃ f₁) p q +
    poissonBracket f₃ (poissonBracket f₁ f₂) p q = 0 := by
  -- 1. Outer brackets only: derivatives fall on the inner bracket.
  rw [poissonBracket_eq_fderiv f₁ (poissonBracket f₂ f₃),
    poissonBracket_eq_fderiv f₂ (poissonBracket f₃ f₁),
    poissonBracket_eq_fderiv f₃ (poissonBracket f₁ f₂)]
  -- 2. Unfold the inner brackets, then split differences and apply the product rule.
  simp only [poissonBracket]
  simp (disch := ((try apply DifferentiableAt.inner ℝ) <;>
      first
      | (apply differentiableAt_gradient_fst; assumption)
      | (apply differentiableAt_gradient_snd; assumption)
      | (apply differentiableAt_gradient_mixed_fst; assumption)
      | (apply differentiableAt_gradient_mixed_snd; assumption)))
    only [fderiv_fun_sub, sub_apply, fderiv_inner_apply ℝ]
  -- 3. Put every derivative on the left of its inner product,
  --    then turn derivatives of gradients into second derivatives.
  simp only [real_inner_comm (fderiv ℝ _ _ _ : X)]
  simp only [inner_fderiv_gradient, inner_fderiv_gradient_param]
  -- 4. Mixed partial derivatives commute.
  simp only [fderiv_partial_comm hf₁ p q, fderiv_partial_comm hf₂ p q,
    fderiv_partial_comm hf₃ p q]
  -- 5. Pure second derivatives in one variable are symmetric.
  have hsymm : ∀ (g : X → ℝ) (x : X), ContDiffAt ℝ 2 g x →
      ∀ v w, fderiv ℝ (fderiv ℝ g) x v w = fderiv ℝ (fderiv ℝ g) x w v :=
    fun g x hg => hg.isSymmSndFDerivAt (by simp)
  have hcp : ∀ f : X → X → ℝ, ContDiff ℝ 2 (Function.uncurry f) →
      ContDiffAt ℝ 2 (fun p' => f p' q) p :=
    fun f hf => (hf.comp (contDiff_id.prodMk contDiff_const)).contDiffAt
  have hcq : ∀ f : X → X → ℝ, ContDiff ℝ 2 (Function.uncurry f) →
      ContDiffAt ℝ 2 (fun q' => f p q') q :=
    fun f hf => (hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  simp only [hsymm _ _ (hcp f₁ hf₁), hsymm _ _ (hcp f₂ hf₂), hsymm _ _ (hcp f₃ hf₃),
    hsymm _ _ (hcq f₁ hf₁), hsymm _ _ (hcq f₂ hf₂), hsymm _ _ (hcq f₃ hf₃)]
  ring

/-!

## G. The canonical Poisson brackets

The Poisson-bracket analogue of the canonical commutation relations. On a general inner product
space the coordinate functionals are the linear functionals `q ↦ ⟪a, q⟫` and `p ↦ ⟪b, p⟫`; on
`EuclideanSpace ℝ ι` they are the coordinates `q ↦ q i` and `p ↦ p j`. The brackets
`{qᵢ, qⱼ} = 0` and `{pᵢ, pⱼ} = 0` are instances of the results of G.1.

-/

/-!

### G.1. Functions of position alone and of momentum alone

-/

/-- Two functions of position alone have vanishing Poisson bracket. -/
lemma poissonBracket_position_position (f g : X → ℝ) (p q : X) :
    poissonBracket (fun _ q' => f q') (fun _ q' => g q') p q = 0 := by
  simp only [poissonBracket, gradient_fun_const, inner_zero_left, inner_zero_right, sub_zero]

/-- Two functions of momentum alone have vanishing Poisson bracket. -/
lemma poissonBracket_momentum_momentum (f g : X → ℝ) (p q : X) :
    poissonBracket (fun p' _ => f p') (fun p' _ => g p') p q = 0 := by
  simp only [poissonBracket, gradient_fun_const, inner_zero_left, inner_zero_right, sub_zero]

/-- The Poisson bracket of a function of position with a function of momentum is the inner
product of their gradients. -/
lemma poissonBracket_position_momentum (f g : X → ℝ) (p q : X) :
    poissonBracket (fun _ q' => f q') (fun p' _ => g p') p q =
      ⟪gradient f q, gradient g p⟫_ℝ := by
  simp only [poissonBracket, gradient_fun_const, inner_zero_left, sub_zero]

/-!

### G.2. Coordinate functionals

-/

/-- The canonical Poisson bracket of linear coordinate functionals:
`{⟪a, q⟫, ⟪b, p⟫} = ⟪a, b⟫`. -/
lemma poissonBracket_inner_position_inner_momentum (a b p q : X) :
    poissonBracket (fun _ q' => ⟪a, q'⟫_ℝ) (fun p' _ => ⟪b, p'⟫_ℝ) p q = ⟪a, b⟫_ℝ := by
  rw [poissonBracket_position_momentum, (hasGradientAt_inner_left a q).gradient,
    (hasGradientAt_inner_left b p).gradient]

/-- On Euclidean space, the canonical Poisson bracket of the coordinates is the Kronecker delta:
`{qᵢ, pⱼ} = δᵢⱼ`. -/
lemma poissonBracket_coord_position_coord_momentum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (p q : EuclideanSpace ℝ ι) :
    poissonBracket (fun _ q' => q' i) (fun p' _ => p' j) p q = if i = j then 1 else 0 := by
  rw [poissonBracket_position_momentum, gradient_coord, gradient_coord]
  exact orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℝ)) i j

end ClassicalMechanics
