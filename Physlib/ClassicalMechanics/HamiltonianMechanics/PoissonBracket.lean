/-
Copyright (c) 2026 Rithwik Ranganathan, Art Mountain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan, Art Mountain, Qianli Ma
-/
module

public import Physlib.ClassicalMechanics.HamiltonianMechanics.Basic
public import Physlib.ClassicalMechanics.HamiltonianMechanics.HamiltonsEquations
public import Physlib.Mathematics.Calculus.Gradient
public import Physlib.Mathematics.KroneckerDelta.Basic
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
derivatives on phase space. On a Hamiltonian system with an open domain in real Hilbert
coordinates, observables can also be defined directly on that domain. Their bracket is again a
domain observable and agrees with the coordinate bracket on restricting coordinate functions.

## ii. Key results

- `poissonBracket` : the Poisson bracket of two phase-space functions.
- `poissonBracket_eq_of_hasGradientAt` : computes the bracket from known partial gradients.
- `poissonBracket_antisymm` : the bracket is antisymmetric.
- `poissonBracket_self` : every observable Poisson-commutes with itself.
- `poissonBracket_jacobi` gives the Jacobi identity for `C²` observables.
- `HamiltonianSystem.poissonBracket` takes the bracket on the open domain of a system.
- `HamiltonianSystem.poissonBracket_firstIntegrals` gives closure under the bracket for
  observables commuting with a full-domain system's Hamiltonian at fixed time.
- `poissonBracket_position_momentum`, `poissonBracket_position_position`,
  `poissonBracket_momentum_momentum` : the canonical bracket relations for Euclidean coordinates.
- `poissonBracket_add_left`, `poissonBracket_add_right`, `poissonBracket_const_mul_left`,
  `poissonBracket_const_mul_right` : the bracket is bilinear, that is additive and homogeneous in
  each argument.
- `poissonBracket_mul_left`, `poissonBracket_mul_right` : the bracket satisfies the Leibniz rule
  in each argument.
- `deriv_comp_eq_inner_gradient_add` : the time derivative of a phase-space function composed with
  a trajectory is the sum of its gradients paired with the trajectory's velocities.
- `deriv_comp_eq_poissonBracket` : along a solution of Hamilton's equations, the time derivative of
  an observable is its Poisson bracket with the Hamiltonian.
- `hasDerivAt_comp_eq_poissonBracket` gives the same identity at a single real time.
- `observable_eq_of_poissonBracket_eq_zero` gives conservation on a time interval.

## iii. Table of contents

- A. The definition of the Poisson bracket
- B. Antisymmetry
- C. Bilinearity
- D. The Leibniz rule
- E. Time evolution along a Hamiltonian flow
  - E.1. The chain rule for a phase-space function along a trajectory
  - E.2. Time evolution as the Poisson bracket with the Hamiltonian
- F. Canonical coordinate relations
- G. Observables on a Hamiltonian system
- H. The Jacobi identity
  - H.1. Jacobi in momentum-position coordinates
  - H.2. Jacobi and first integrals on a system domain

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
* G. J. Sussman and J. Wisdom, "Structure and Interpretation of Classical Mechanics", Section 3.2.
  <https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book-Z-H-37.html>.
  [ref: sussman_wisdom_sicm]
-/

@[expose] public section

open InnerProductSpace KroneckerDelta Time

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
      ((fderiv ℝ (Function.uncurry f) (p t, q t)).comp ((fderiv ℝ p t).prod (fderiv ℝ q t))) t :=
    HasFDerivAt.comp (f := fun t => (p t, q t)) t hf.hasFDerivAt
      (hp.hasFDerivAt.prodMk hq.hasFDerivAt)
  rw [Time.deriv_eq, hF.fderiv]
  have hchain := fderiv_uncurry f (p t, q t) (∂ₜ p t, ∂ₜ q t) hf
  change (fderiv ℝ (Function.uncurry f) (p t, q t)) _ = _ at hchain
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ← Time.deriv_eq, inner_gradient_left] using hchain

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

/-- The Poisson bracket gives the derivative of an observable at a real time where the
position and momentum derivatives satisfy Hamilton's equations. -/
lemma hasDerivAt_comp_eq_poissonBracket (H f : X → X → ℝ) {p q : ℝ → X} {t : ℝ}
    (hp : HasDerivAt p (-gradient (fun p' => H (p t) p') (q t)) t)
    (hq : HasDerivAt q (gradient (fun q' => H q' (q t)) (p t)) t)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (p t, q t)) :
    HasDerivAt (fun s => f (p s) (q s)) (poissonBracket f H (p t) (q t)) t := by
  have hpq : HasDerivAt (fun s => (p s, q s))
      (-gradient (fun q' => H (p t) q') (q t), gradient (fun p' => H p' (q t)) (p t)) t :=
    by simpa [ContinuousLinearMap.prod_apply] using
      (hp.hasFDerivAt.prodMk hq.hasFDerivAt).hasDerivAt
  have hd := hf.hasFDerivAt.comp_hasDerivAt t hpq
  have hbr := fderiv_uncurry f (p t, q t)
    (-gradient (fun q' => H (p t) q') (q t), gradient (fun p' => H p' (q t)) (p t)) hf
  change (fderiv ℝ (Function.uncurry f) (p t, q t)) _ = _ at hbr
  rw [hbr, ← inner_gradient_left, ← inner_gradient_left, inner_neg_right,
    neg_add_eq_sub, ← poissonBracket] at hd
  exact hd

/-- A time-independent observable takes the same value at any two times in an interval
where the trajectory satisfies Hamilton's equations and the observable Poisson-commutes
with the possibly time-dependent Hamiltonian along the trajectory. -/
lemma observable_eq_of_poissonBracket_eq_zero (H : ℝ → X → X → ℝ) {p q : ℝ → X}
    {s : Set ℝ} (hs : Convex ℝ s)
    (hp : ∀ t ∈ s, HasDerivAt p (-gradient (fun q' => H t (p t) q') (q t)) t)
    (hq : ∀ t ∈ s, HasDerivAt q (gradient (fun p' => H t p' (q t)) (p t)) t)
    (f : X → X → ℝ) (hf : ∀ t ∈ s, DifferentiableAt ℝ (Function.uncurry f) (p t, q t))
    (hbr : ∀ t ∈ s, poissonBracket f (H t) (p t) (q t) = 0)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ s) (h₂ : t₂ ∈ s) : f (p t₁) (q t₁) = f (p t₂) (q t₂) := by
  have hd t (ht : t ∈ s) : HasDerivAt (fun u => f (p u) (q u)) 0 t := by
    simpa only [hbr t ht] using
      hasDerivAt_comp_eq_poissonBracket (H t) f (hp t ht) (hq t ht) (hf t ht)
  have bound := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0)
    (fun t ht => (hd t ht).hasDerivWithinAt) (fun _ _ => (norm_zero (E := ℝ)).le) h₂ h₁
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using bound

/-!

## F. Canonical coordinate relations

For Euclidean phase space, position and momentum coordinates satisfy
`{qᵢ, pⱼ} = δᵢⱼ`, while brackets between two position coordinates or two momentum coordinates
vanish.
The argument order remains momentum first, position second, as in `poissonBracket`.

-/

/-- The Poisson bracket of a position coordinate with a momentum coordinate is the Kronecker
delta. -/
@[simp]
lemma poissonBracket_position_momentum {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι)
    (p q : EuclideanSpace ℝ ι) :
    poissonBracket (fun _ q => q i) (fun p _ => p j) p q = δ[i,j] := by
  simp [poissonBracket, gradient_coord, gradient_fun_const, EuclideanSpace.inner_single_left,
    PiLp.single_apply, kroneckerDelta, eq_comm]

/-- The Poisson bracket of two position coordinates vanishes. -/
@[simp]
lemma poissonBracket_position_position {ι : Type*} [Fintype ι] (i j : ι)
    (p q : EuclideanSpace ℝ ι) :
    poissonBracket (fun _ q => q i) (fun _ q => q j) p q = 0 := by
  simp [poissonBracket, gradient_fun_const]

/-- The Poisson bracket of two momentum coordinates vanishes. -/
@[simp]
lemma poissonBracket_momentum_momentum {ι : Type*} [Fintype ι] (i j : ι)
    (p q : EuclideanSpace ℝ ι) :
    poissonBracket (fun p _ => p i) (fun p _ => p j) p q = 0 := by
  simp [poissonBracket, gradient_fun_const]

/-!
## G. Observables on a Hamiltonian system
-/

namespace HamiltonianSystem

open scoped Manifold ContDiff Topology

variable (S : HamiltonianSystem 𝓘(ℝ, X) ⟨X⟩)

/-- At a state with known momentum and position, restriction evaluates the coordinate observable. -/
@[simp]
lemma restrictObservable_ofInnerProductSpace (f : X → X → ℝ) (p q : X)
    (hz : PhaseSpace.ofInnerProductSpace p q ∈ S.domain) :
    (Function.uncurry f ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val)
      (⟨PhaseSpace.ofInnerProductSpace p q, hz⟩ : S.domain) = f p q := by
  change Function.uncurry f ((PhaseSpace.hilbertCoords X)
    ((PhaseSpace.hilbertCoords X).symm (p, q))) = f p q
  simp only [(PhaseSpace.hilbertCoords X).apply_symm_apply, Function.uncurry]

/-- The canonical Poisson bracket of observables on the open phase-space domain of a system
in real Hilbert space. The coordinate formula uses extensions by zero. Its value at an
interior point depends only on the observables in a neighborhood of that point. -/
noncomputable def poissonBracket (f g : S.domain → ℝ) : S.domain → ℝ :=
  let coord (a : S.domain → ℝ) (p q : X) :=
    Function.extend Subtype.val a (fun _ => 0) (PhaseSpace.ofInnerProductSpace p q)
  Function.uncurry (ClassicalMechanics.poissonBracket (coord f) (coord g)) ∘
    PhaseSpace.hilbertCoords X ∘ Subtype.val

/-- Restricting the coordinate bracket to the system domain gives the bracket of the restricted
observables. -/
@[simp]
lemma poissonBracket_restrictObservable (f g : X → X → ℝ) :
    S.poissonBracket (Function.uncurry f ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val)
        (Function.uncurry g ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val) =
      Function.uncurry (ClassicalMechanics.poissonBracket f g) ∘
        PhaseSpace.hilbertCoords X ∘ Subtype.val := by
  funext x
  let e := PhaseSpace.hilbertCoords X
  let z := e x.val
  let restrict (a : X → X → ℝ) : S.domain → ℝ := Function.uncurry a ∘ e ∘ Subtype.val
  let lift (a : X → X → ℝ) (pq : X × X) :=
    Function.extend Subtype.val (restrict a) (fun _ => 0) (e.symm pq)
  have hx : e.symm z ∈ S.domain := by simp [z]
  have heq (a : X → X → ℝ) : lift a =ᶠ[𝓝 z] Function.uncurry a := by
    filter_upwards [(S.isOpen_domain.preimage e.symm.contMDiff.continuous).mem_nhds hx] with y hy
    change Function.extend Subtype.val (restrict a) _ (e.symm y) = a y.1 y.2
    rw [Subtype.val_injective.extend_apply (restrict a) _ ⟨e.symm y, hy⟩]
    simp [restrict, Function.uncurry]
  have hfst (a : X → X → ℝ) :
      (fun p' => lift a (p', z.2)) =ᶠ[𝓝 z.1] (fun p' => a p' z.2) :=
    (heq a).comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hsnd (a : X → X → ℝ) :
      (fun q' => lift a (z.1, q')) =ᶠ[𝓝 z.2] (fun q' => a z.1 q') :=
    (heq a).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  change ClassicalMechanics.poissonBracket (Function.curry (lift f)) (Function.curry (lift g))
    z.1 z.2 = ClassicalMechanics.poissonBracket f g z.1 z.2
  simp only [ClassicalMechanics.poissonBracket, Function.curry, (hfst f).gradient_eq,
    (hsnd f).gradient_eq, (hfst g).gradient_eq, (hsnd g).gradient_eq]

/-- Interchanging the two domain observables reverses the bracket at each state. -/
lemma poissonBracket_antisymm (f g : S.domain → ℝ) (x : S.domain) :
    S.poissonBracket f g x = -S.poissonBracket g f x := by
  simp only [poissonBracket, Function.comp_apply, Function.uncurry]
  apply ClassicalMechanics.poissonBracket_antisymm

/-- A zero observable has zero bracket with every observable on the system domain. -/
@[simp]
lemma poissonBracket_zero_right (f : S.domain → ℝ) : S.poissonBracket f 0 = 0 := by
  funext x
  simp [poissonBracket, Function.uncurry, Function.extend, ClassicalMechanics.poissonBracket]

end HamiltonianSystem

/-!
## H. The Jacobi identity

### H.1. Jacobi in momentum-position coordinates

The cyclic sum of nested Poisson brackets vanishes for twice continuously differentiable
observables. Art Mountain formalized this identity in Physlib PR #1894. Here the product
rule expresses a nested bracket using two Hessians. Symmetry of each Hessian then cancels its
two contributions to the cyclic sum.
-/

open ContinuousLinearMap

/-- The canonical Poisson tensor sends the differential of an observable `H` to its
Hamiltonian vector `(-∇q H, ∇p H)` in momentum-first coordinates. -/
private noncomputable def poissonSharp :
    ((X × X) →L[ℝ] ℝ) →L[ℝ] X × X :=
  let riesz := (toDual ℝ X).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let restrict := (compL ℝ X (X × X) ℝ).flip
  (-(riesz.comp (restrict (inr ℝ X X)))).prod (riesz.comp (restrict (inl ℝ X X)))

/-- The canonical Poisson tensor is skew under the covector-vector pairing. -/
private lemma poissonSharp_skew (a b : (X × X) →L[ℝ] ℝ) :
    a (poissonSharp b) = -b (poissonSharp a) := by
  have split (c : (X × X) →L[ℝ] ℝ) (p q : X) :
      c (p, q) = c (p, 0) + c (0, q) := by
    simp [← map_add, Prod.mk_add_mk]
  have pair (c d : X →L[ℝ] ℝ) :
      c ((toDual ℝ X).symm d) = d ((toDual ℝ X).symm c) := by
    rw [← toDual_symm_apply (y := c), real_inner_comm, toDual_symm_apply]
  let dp (c : (X × X) →L[ℝ] ℝ) := c.comp (inl ℝ X X)
  let dq (c : (X × X) →L[ℝ] ℝ) := c.comp (inr ℝ X X)
  have expand (c d : (X × X) →L[ℝ] ℝ) : c (poissonSharp d) =
      -dp c ((toDual ℝ X).symm (dq d)) + dq c ((toDual ℝ X).symm (dp d)) := by
    change c (-_, _) = _
    rw [split]
    simp only [show ∀ x : X, (-x, (0 : X)) = -(x, 0) by simp, map_neg]
    rfl
  rw [expand a, expand b, pair (dp a), pair (dq a)]
  ring

/-- The bracket evaluates the differential of the first observable on the Hamiltonian vector
of the second. -/
private lemma poissonBracket_eq_sharp {f g : X → X → ℝ} {z : X × X}
    (hf : DifferentiableAt ℝ (Function.uncurry f) z)
    (hg : DifferentiableAt ℝ (Function.uncurry g) z) :
    poissonBracket f g z.1 z.2 =
      fderiv ℝ (Function.uncurry f) z (poissonSharp (fderiv ℝ (Function.uncurry g) z)) := by
  have restrict (u : X → X → ℝ) (hu : DifferentiableAt ℝ (Function.uncurry u) z) :
      poissonSharp (fderiv ℝ (Function.uncurry u) z) =
        (-gradient (u z.1) z.2, gradient (fun p => u p z.2) z.1) := by
    change (-((toDual ℝ X).symm _), (toDual ℝ X).symm _) = _
    congr 3 <;> ext v
    · exact (fderiv_curry_snd (Function.uncurry u) z.1 z.2 hu v).symm
    · exact (fderiv_curry_fst (Function.uncurry u) z.1 z.2 hu v).symm
  rw [restrict g hg]
  have h := fderiv_uncurry f z (-gradient (g z.1) z.2, gradient (fun p => g p z.2) z.1) hf
  change fderiv ℝ (Function.uncurry f) z _ = _ at h
  rw [h]
  simp only [poissonBracket, map_neg, ← inner_gradient_left]
  ring

/-- The derivative of a bracket along a third Hamiltonian vector involves one Hessian term
from each of the two inner observables. -/
private lemma poissonBracket_nested {f g h : X → X → ℝ} (z : X × X)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (hg : ContDiff ℝ 2 (Function.uncurry g))
    (hh : ContDiff ℝ 2 (Function.uncurry h)) :
    let field := fun k : X → X → ℝ => poissonSharp (fderiv ℝ (Function.uncurry k) z)
    let hessian := fun k : X → X → ℝ => fderiv ℝ (fderiv ℝ (Function.uncurry k)) z
    poissonBracket f (poissonBracket g h) z.1 z.2 =
      hessian h (field f) (field g) - hessian g (field f) (field h) := by
  dsimp only
  have heq : Function.uncurry (poissonBracket g h) =
      fun x => fderiv ℝ (Function.uncurry g) x (poissonSharp (fderiv ℝ (Function.uncurry h) x)) :=
    funext fun x => poissonBracket_eq_sharp (hg.differentiable (by simp) x)
      (hh.differentiable (by simp) x)
  have dg := (hg.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num)
  have dh := (hh.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num)
  have hd := (dg.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (poissonSharp.hasFDerivAt.comp z (dh.differentiableAt one_ne_zero).hasFDerivAt)
  simp only [Function.comp_apply] at hd
  rw [← heq] at hd
  rw [poissonBracket_antisymm f,
    poissonBracket_eq_sharp hd.differentiableAt (hf.differentiable (by simp) z), hd.fderiv]
  simp only [add_apply, comp_apply, flip_apply]
  rw [poissonSharp_skew]
  ring

/-- The cyclic sum of nested canonical Poisson brackets vanishes for `C²` observables. -/
lemma poissonBracket_jacobi (f₁ f₂ f₃ : X → X → ℝ) (p q : X)
    (hf₁ : ContDiff ℝ 2 (Function.uncurry f₁))
    (hf₂ : ContDiff ℝ 2 (Function.uncurry f₂))
    (hf₃ : ContDiff ℝ 2 (Function.uncurry f₃)) :
    poissonBracket f₁ (poissonBracket f₂ f₃) p q +
    poissonBracket f₂ (poissonBracket f₃ f₁) p q +
    poissonBracket f₃ (poissonBracket f₁ f₂) p q = 0 := by
  simp only [poissonBracket_nested (p, q) hf₁ hf₂ hf₃, poissonBracket_nested (p, q) hf₂ hf₃ hf₁,
    poissonBracket_nested (p, q) hf₃ hf₁ hf₂]
  have symm {f : X → X → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f)) :=
    (hf.contDiffAt (x := (p, q))).isSymmSndFDerivAt (by simp)
  simp only [(symm hf₁).eq, (symm hf₂).eq, (symm hf₃).eq]
  ring

/-!
### H.2. Jacobi and first integrals on a system domain
-/

namespace HamiltonianSystem

open scoped Manifold ContDiff

variable (S : HamiltonianSystem 𝓘(ℝ, X) ⟨X⟩)

/-- The Jacobi identity for restrictions of twice continuously differentiable phase-space
observables to the open domain of a Hamiltonian system. -/
lemma poissonBracket_jacobi (f g h : X → X → ℝ)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (hg : ContDiff ℝ 2 (Function.uncurry g))
    (hh : ContDiff ℝ 2 (Function.uncurry h)) (x : S.domain) :
    let F : S.domain → ℝ := Function.uncurry f ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val
    let K : S.domain → ℝ := Function.uncurry g ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val
    let L : S.domain → ℝ := Function.uncurry h ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val
    S.poissonBracket F (S.poissonBracket K L) x +
      S.poissonBracket K (S.poissonBracket L F) x +
      S.poissonBracket L (S.poissonBracket F K) x = 0 := by
  dsimp only
  simp only [poissonBracket_restrictObservable]
  exact ClassicalMechanics.poissonBracket_jacobi f g h _ _ hf hg hh

/-- At a fixed time in a globally defined system, the bracket of two twice continuously
differentiable observables commuting with the Hamiltonian also commutes with it. -/
lemma poissonBracket_firstIntegrals (hdom : S.domain = Set.univ) (t : Time) (f g : X → X → ℝ)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (hg : ContDiff ℝ 2 (Function.uncurry g)) :
    let F : S.domain → ℝ := Function.uncurry f ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val
    let K : S.domain → ℝ := Function.uncurry g ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val
    let H := fun x : S.domain => S.hamiltonian (t, x.1)
    S.poissonBracket F H = 0 → S.poissonBracket K H = 0 →
    S.poissonBracket (S.poissonBracket F K) H = 0 := by
  intro F K H hfH hgH
  let coordinateHamiltonian := fun p q : X => S.hamiltonian (t, PhaseSpace.ofInnerProductSpace p q)
  have hK :
      Function.uncurry coordinateHamiltonian ∘ PhaseSpace.hilbertCoords X ∘ Subtype.val = H := by
    funext x
    exact congrArg (fun z => S.hamiltonian (t, z))
      ((PhaseSpace.hilbertCoords X).symm_apply_apply x.val)
  have hs := S.contMDiffOn_hamiltonian
  rw [hdom, Set.univ_prod_univ, contMDiffOn_univ] at hs
  have hreg : ContDiff ℝ 2 (Function.uncurry coordinateHamiltonian) :=
    (hs.comp (contMDiff_const.prodMk
      (PhaseSpace.hilbertCoords X).symm.contMDiff)).contDiff.of_le (by simp)
  have hHf : S.poissonBracket H F = 0 := by
    funext x
    rw [S.poissonBracket_antisymm H, hfH]
    exact neg_zero
  funext x
  have h := S.poissonBracket_jacobi f g coordinateHamiltonian hf hg hreg x
  dsimp only at h
  change S.poissonBracket F (S.poissonBracket K _) x +
      S.poissonBracket K (S.poissonBracket _ F) x +
      S.poissonBracket _ (S.poissonBracket F K) x = 0 at h
  rw [hK, hgH, hHf, S.poissonBracket_antisymm H] at h
  simpa only [poissonBracket_zero_right, Pi.zero_apply, zero_add, neg_eq_zero] using h

end HamiltonianSystem

end ClassicalMechanics
