/-
Copyright (c) 2026 Art Mountain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Art Mountain, Qianli Ma
-/
module

public import Physlib.ClassicalMechanics.HamiltonianMechanics.PoissonBracket
public import Physlib.ClassicalMechanics.HamiltonianMechanics.Basic
import Physlib.Mathematics.ForMathlib.FDerivCurry

/-!
# The Jacobi identity for the canonical Poisson bracket

## i. Overview

For twice continuously differentiable observables on a real Hilbert phase space, the cyclic sum
of nested canonical Poisson brackets vanishes. The proof uses symmetry of the second derivative
in momentum and position.

## ii. Key results

- `poissonBracket_jacobi` gives the Jacobi identity for the canonical Poisson bracket.
- `HamiltonianSystem.poissonBracket_firstIntegrals` shows that the bracket of two first integrals
  again Poisson-commutes with the Hamiltonian for a system on the whole phase space.

## iii. Table of contents

- A. Derivatives of the partial gradients
- B. The Jacobi identity
- C. First integrals of a Hamiltonian system

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
-/

@[expose] public section

open InnerProductSpace

namespace ClassicalMechanics

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-!
## A. Derivatives of the partial gradients
-/

/-- The gradient of a `C²` function is differentiable. -/
private lemma differentiableAt_gradient {g : X → ℝ} {x : X} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (gradient g) x := by
  change DifferentiableAt ℝ (⇑(toDual ℝ X).symm ∘ fderiv ℝ g) x
  rw [(toDual ℝ X).symm.comp_differentiableAt_iff]
  exact (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

/-- The derivative of a gradient, paired with `w`, is the second derivative. -/
private lemma inner_fderiv_gradient (g : X → ℝ) (x v w : X) :
    ⟪fderiv ℝ (gradient g) x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ g) x v w := by
  change ⟪fderiv ℝ (⇑(toDual ℝ X).symm ∘ fderiv ℝ g) x v, w⟫_ℝ = _
  rw [(toDual ℝ X).symm.comp_fderiv, ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

/-- For `f` that is `C²` on phase space, the momentum gradient of `f` is differentiable in the
momentum. -/
private lemma differentiableAt_gradient_fst {f : X → X → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (p q : X) :
    DifferentiableAt ℝ (gradient fun p' => f p' q) p :=
  differentiableAt_gradient (hf.comp (contDiff_id.prodMk contDiff_const)).contDiffAt

/-- For `f` that is `C²` on phase space, the position gradient of `f` is differentiable in the
position. -/
private lemma differentiableAt_gradient_snd {f : X → X → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (p q : X) :
    DifferentiableAt ℝ (gradient fun q' => f p q') q :=
  differentiableAt_gradient_fst (f := flip f) (hf.comp (contDiff_snd.prodMk contDiff_fst)) q p

/-- For `f` that is `C²` on phase space, the position gradient of `f` is differentiable in the
momentum. -/
private lemma differentiableAt_gradient_mixed_fst {f : X → X → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (p q : X) :
    DifferentiableAt ℝ (fun p' => gradient (fun q' => f p' q') q) p := by
  change DifferentiableAt ℝ
    (⇑(toDual ℝ X).symm ∘ fun p' => fderiv ℝ (fun q' => f p' q') q) p
  rw [(toDual ℝ X).symm.comp_differentiableAt_iff]
  exact fderiv_uncurry_differentiable_snd_comp_fst f q hf p

/-- For `f` that is `C²` on phase space, the momentum gradient of `f` is differentiable in the
position. -/
private lemma differentiableAt_gradient_mixed_snd {f : X → X → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (p q : X) :
    DifferentiableAt ℝ (fun q' => gradient (fun p' => f p' q') p) q :=
  differentiableAt_gradient_mixed_fst (f := flip f) (hf.comp (contDiff_snd.prodMk contDiff_fst)) q p

omit [CompleteSpace X] in
/-- Mixed partial derivatives of a `C²` phase-space function commute: differentiating in the
momentum and then the position agrees with differentiating in the position and then the
momentum. -/
private lemma fderiv_partial_comm {f : X → X → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f))
    (p q v w : X) :
    fderiv ℝ (fun q' => fderiv ℝ (fun p' => f p' q') p) q w v =
      fderiv ℝ (fun p' => fderiv ℝ (fun q' => f p' q') q) p v w := by
  have h₁ : Differentiable ℝ (fun q' => fderiv ℝ (fun p' => f p' q') p) :=
    fderiv_uncurry_differentiable_fst_comp_snd f p hf
  have h₂ : Differentiable ℝ (fun p' => fderiv ℝ (fun q' => f p' q') q) :=
    fderiv_uncurry_differentiable_snd_comp_fst f q hf
  rw [fderiv_curry_clm_apply _ v q w h₁, fderiv_curry_clm_apply _ w p v h₂]
  exact (fderiv_swap f p v q w hf).symm

/-- The Poisson bracket, written with the derivatives falling on `g`. -/
private lemma poissonBracket_eq_fderiv (f g : X → X → ℝ) (p q : X) :
    poissonBracket f g p q =
      fderiv ℝ (fun p' => g p' q) p (gradient (fun q' => f p q') q) -
        fderiv ℝ (fun q' => g p q') q (gradient (fun p' => f p' q) p) := by
  simp only [poissonBracket, inner_gradient_right, conj_trivial]

/-- The same, for a gradient in a second variable (mixed second derivatives). -/
private lemma inner_fderiv_gradient_param (G : X → X → ℝ) (x y v w : X) :
    ⟪fderiv ℝ (fun x' => gradient (G x') y) x v, w⟫_ℝ =
      fderiv ℝ (fun x' => fderiv ℝ (G x') y) x v w := by
  change ⟪fderiv ℝ (⇑(toDual ℝ X).symm ∘ fun x' => fderiv ℝ (G x') y) x v, w⟫_ℝ = _
  rw [(toDual ℝ X).symm.comp_fderiv, ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

/-!

## B. The Jacobi identity

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
## C. First integrals of a Hamiltonian system
-/

open scoped Manifold ContDiff

/-- At a fixed time, two observables commuting everywhere with the Hamiltonian of a globally
defined system have a bracket that also commutes with that Hamiltonian. -/
lemma HamiltonianSystem.poissonBracket_firstIntegrals (S : HamiltonianSystem 𝓘(ℝ, X) ⟨X⟩)
    (hdom : S.domain = Set.univ) (t : Time) (f g : X → X → ℝ)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (hg : ContDiff ℝ 2 (Function.uncurry g)) :
    let H := fun p q : X => S.hamiltonian (t, PhaseSpace.ofInnerProductSpace p q)
    (∀ p q, poissonBracket f H p q = 0) → (∀ p q, poissonBracket g H p q = 0) →
      ∀ p q, poissonBracket (poissonBracket f g) H p q = 0 := by
  intro H hfH hgH p q
  have hs := S.contMDiffOn_hamiltonian
  rw [hdom, Set.univ_prod_univ, contMDiffOn_univ] at hs
  have hH : ContDiff ℝ 2 (Function.uncurry H) :=
    (hs.comp (contMDiff_const.prodMk
      (PhaseSpace.innerProductSpaceDiffeomorph X).symm.contMDiff)).contDiff.of_le (by simp)
  have h₁ : poissonBracket g H = fun _ _ => 0 := funext fun p => funext (hgH p)
  have h₂ : poissonBracket H f = fun _ _ => 0 := by
    funext p q
    rw [poissonBracket_antisymm, hfH, neg_zero]
  have h := poissonBracket_jacobi f g H p q hf hg hH
  rw [h₁, h₂, poissonBracket_antisymm H (poissonBracket f g)] at h
  have hzero (F : X → X → ℝ) : poissonBracket F (fun _ _ => 0) p q = 0 := by
    simp [poissonBracket]
  simpa only [hzero, zero_add, neg_eq_zero] using h

end ClassicalMechanics
