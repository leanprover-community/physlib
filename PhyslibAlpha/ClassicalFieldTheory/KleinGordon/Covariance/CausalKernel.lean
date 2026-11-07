/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Covariance.Distributions

/-!

# The causal propagator kernel

The causal propagator kernel is invariant under the orthochronous Lorentz group and odd under time
reversal.

## i. Overview

The causal propagator kernel is the retarded kernel minus the advanced kernel, both centred at the
spacetime origin. It solves the homogeneous equation. The covariance of the retarded and advanced
point sources (`retardedPointSource_actDist`) transfers to it. A Lorentz transformation fixes the
origin. An orthochronous one fixes the kernel. A time-reversing one swaps the retarded and the
advanced kernel, so it changes the sign of the causal kernel.

The covariance is proved on the distribution itself. The Fourier transform of the kernel inherits
it with the induced action on the frequencies.

## ii. Key results

- `causalKernel` : the retarded kernel minus the advanced kernel at the origin.
- `causalKernel_actDist` : the kernel is invariant under orthochronous Lorentz transformations.
- `causalKernel_actDist_of_not` : the kernel changes sign under time reversing ones.

## iii. Table of contents

- A. The kernel

## iv. References

None.

## A. The kernel

- `causalKernel` : the retarded kernel minus the advanced kernel at the origin.
- `causalKernel_actDist` : the kernel is invariant under orthochronous Lorentz transformations.
- `causalKernel_actDist_of_not` : the kernel changes sign under time reversing ones.
-/

@[expose] public section

noncomputable section

open Minkowski PoincareGroup KleinGordon.Spacetime

namespace KleinGordon.Solution

variable {d : ℕ}

/-- The causal propagator kernel: the retarded kernel minus the advanced kernel at the origin. -/
def causalKernel (m : ℝ) : DistributionField d ℝ :=
  retardedPointSource m (0 : SpaceTime d) - advancedPointSource m (0 : SpaceTime d)

/-- A Poincaré transformation without translation fixes the origin. -/
lemma smul_zero_of_translation_eq_zero {g : PoincareGroup d} (h : g.translation = 0) :
    g • (0 : SpaceTime d) = 0 := by
  rw [smul_def, h, smul_zero, add_zero]

/-- **Lorentz invariance of the causal kernel.** An orthochronous Lorentz transformation leaves
the causal propagator kernel invariant. -/
lemma causalKernel_actDist (m : ℝ) {g : PoincareGroup d} (hg : g.IsOrthochronous)
    (h : g.translation = 0) : actDist g (causalKernel m) = causalKernel m := by
  unfold causalKernel
  rw [map_sub, retardedPointSource_actDist hg, advancedPointSource_actDist hg,
    smul_zero_of_translation_eq_zero h]

/-- A time-reversing Lorentz transformation changes the sign of the causal propagator kernel. -/
lemma causalKernel_actDist_of_not (m : ℝ) {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (h : g.translation = 0) : actDist g (causalKernel m) = -causalKernel m := by
  unfold causalKernel
  rw [map_sub, retardedPointSource_actDist_of_not hg, advancedPointSource_actDist_of_not hg,
    smul_zero_of_translation_eq_zero h, neg_sub]

end KleinGordon.Solution
