/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Covariance.Distributions

/-!

# The retarded solution as a convolution with the retarded kernel

The retarded solution at `p` is the retarded kernel tested against the reflected and shifted
source.

## i. Overview

The retarded kernel `K` is the retarded point source at the origin. The point reflection
`x ↦ p - x` reverses time. It is therefore a Poincaré transformation that is not orthochronous.
It maps the retarded point source at the origin to the advanced point source at `p`. The
advanced point source at `p` is the retarded response evaluated at `p`. This gives
`(G_R f)(p) = K (x ↦ f (p - x))`.

## ii. Key results

- `retarded_eq_kernel` : the retarded solution at `p` is the kernel tested against
  `x ↦ f (p - x)`.

## iii. Table of contents

- A. The point reflection
- B. The convolution form

## iv. References

None.

## A. The point reflection


## B. The convolution form

- `retarded_eq_kernel` : the retarded solution at `p` is the kernel tested against
  `x ↦ f (p - x)`.
- `retardedDistribution_apply` : the retarded solution of a compactly supported distribution is
  the distribution tested against the cut off advanced solution.
- `retardedDistribution_delta_apply` : the point source gives the advanced solution at `p`.
-/

@[expose] public section

noncomputable section

open CausalRelation LocalOperator Minkowski KleinGordon.Spacetime PoincareGroup GreenOperator
  Distribution

namespace KleinGordon.Solution

variable {d : ℕ}

variable {m : ℝ}

/-- **The retarded solution as a convolution.** The retarded solution of a real test source at
`p` is the retarded kernel tested against the source reflected through `p`. -/
lemma retarded_eq_kernel (p : SpaceTime d) (f : TestField d ℝ) :
    ((realRetardedGreenOperator m).toLinearMap f).val p =
      retardedPointSource m 0
        (actTestFunction (pointReflection p)⁻¹ (testFieldEquiv ℝ f)) := by
  have h := retardedPointSource_actDist_of_not (m := m)
    (not_isOrthochronous_pointReflection p) 0
  have h0 : pointReflection p • (0 : SpaceTime d) = p := by
    rw [pointReflection_smul, sub_zero]
  rw [h0] at h
  rw [← actDist_apply, h]
  exact (realRetardedEvaluation_apply m p f).symm

/-- The reflected source takes the value `f (p - x)` at `x`. -/
lemma actTestFunction_pointReflection_apply (p x : SpaceTime d) (f : TestField d ℝ) :
    actTestFunction (pointReflection p)⁻¹ (testFieldEquiv ℝ f) x =
      testFieldEquiv ℝ f (p - x) := by
  rw [actTestFunction_apply, inv_inv, pointReflection_smul]

/-- **Convolution with a compactly supported distribution by transposition.** The retarded
solution of `T` tested against `f` is `T` tested against the advanced solution of `f` cut off by
a function that equals one near the support of `T`. -/
lemma retardedDistribution_apply (T : compactDistributions (SpaceTime d) ℝ) (f : TestField d ℝ) :
    retardedDistribution m T (testFieldEquiv ℝ f) =
      T.val (realAdvancedCutoff m (compactCutoff (compactDistributionBound T))
        (testFieldEquiv ℝ f)) := rfl

/-- The cut off advanced solution has the value `χ p * (A f) p`. -/
lemma realAdvancedCutoff_compactCutoff_apply (T : compactDistributions (SpaceTime d) ℝ)
    (f : TestField d ℝ) (p : SpaceTime d) :
    realAdvancedCutoff m (compactCutoff (compactDistributionBound T)) (testFieldEquiv ℝ f) p =
      compactCutoff (compactDistributionBound T) p *
        ((realAdvancedGreenOperator m).toLinearMap f).val p :=
  realAdvancedCutoff_apply m _ f p

/-- For the point source the transposed convolution is the advanced solution at `p`. -/
lemma retardedDistribution_delta_apply (p : SpaceTime d) (f : TestField d ℝ) :
    retardedDistribution m (deltaCompact p) (testFieldEquiv ℝ f) =
      ((realAdvancedGreenOperator m).toLinearMap f).val p := by
  rw [← retardedPointSource_eq]
  exact (realAdvancedEvaluation_apply m p f)

end KleinGordon.Solution
