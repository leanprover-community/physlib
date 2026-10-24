/-
Copyright (c) 2026 Art Mountain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Art Mountain
-/
module

public import Physlib.Mathematics.Calculus.Gradient
public import Physlib.Mathematics.ForMathlib.FDerivCurry
/-!

# Properties of phase space

Differentiability properties for phase space

## i. Overview

Hamiltonian mechanics requires various derivatives to exist in phase space. This is mainly
first derivatives only for the Poisson bracket and Hamiltonian evolution and second
derivatives for equations of motion and the Jacobi identity. Though in principle higher
derivatives might be needed for more the evolution of compound quantities.

## ii. Key results

- `differentiableAt_gradient_fst` : second derivative in momentum exists.
- `differentiableAt_gradient_snd` : second derivative in position exists.
- `differentiableAt_gradient_mixed_fst` : position gradient is differentiable in the momentum.
- `differentiableAt_gradient_mixed_snd` : momentum gradient is differentiable in the position.
- `fderiv_partial_comm` : position and momentum derivatives commute

## iii. Table of contents

- A. Differentiability

## iv. References

* Mathlib, `Mathlib.Analysis.Calculus.Gradient.Basic`.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-!

## A. Differentiability

Establish differentiability properties for phase space

-/

/-- For `f` that is `C²` on phase space, the momentum gradient of `f` is differentiable in the
momentum. -/
lemma differentiableAt_gradient_fst {f : F → F → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (p q : F) :
    DifferentiableAt ℝ (gradient fun p' => f p' q) p :=
  differentiableAt_gradient (hf.comp (contDiff_id.prodMk contDiff_const)).contDiffAt

/-- For `f` that is `C²` on phase space, the position gradient of `f` is differentiable in the
position. -/
lemma differentiableAt_gradient_snd {f : F → F → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (p q : F) :
    DifferentiableAt ℝ (gradient fun q' => f p q') q :=
  differentiableAt_gradient_fst (f := flip f) (hf.comp (contDiff_snd.prodMk contDiff_fst)) q p

/-- For `f` that is `C²` on phase space, the position gradient of `f` is differentiable in the
momentum. -/
lemma differentiableAt_gradient_mixed_fst {f : F → F → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (p q : F) :
    DifferentiableAt ℝ (fun p' => gradient (fun q' => f p' q') q) p := by
  change DifferentiableAt ℝ (⇑(toDual ℝ F).symm ∘ fun p' => fderiv ℝ (fun q' => f p' q') q) p
  rw [(toDual ℝ F).symm.comp_differentiableAt_iff]
  exact fderiv_uncurry_differentiable_snd_comp_fst f q hf p

/-- For `f` that is `C²` on phase space, the momentum gradient of `f` is differentiable in the
position. -/
lemma differentiableAt_gradient_mixed_snd {f : F → F → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (p q : F) :
    DifferentiableAt ℝ (fun q' => gradient (fun p' => f p' q') p) q :=
  differentiableAt_gradient_mixed_fst (f := flip f) (hf.comp (contDiff_snd.prodMk contDiff_fst)) q p

omit [CompleteSpace F] in
/-- Mixed partial derivatives of a `C²` phase-space function commute: differentiating in the
momentum and then the position agrees with differentiating in the position and then the
momentum. -/
lemma fderiv_partial_comm {f : F → F → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f))
    (p q v w : F) :
    fderiv ℝ (fun q' => fderiv ℝ (fun p' => f p' q') p) q w v =
      fderiv ℝ (fun p' => fderiv ℝ (fun q' => f p' q') q) p v w := by
  have h₁ : Differentiable ℝ (fun q' => fderiv ℝ (fun p' => f p' q') p) :=
    fderiv_uncurry_differentiable_fst_comp_snd f p hf
  have h₂ : Differentiable ℝ (fun p' => fderiv ℝ (fun q' => f p' q') q) :=
    fderiv_uncurry_differentiable_snd_comp_fst f q hf
  rw [fderiv_curry_clm_apply _ v q w h₁, fderiv_curry_clm_apply _ w p v h₂]
  exact (fderiv_swap f p v q w hf).symm

end
