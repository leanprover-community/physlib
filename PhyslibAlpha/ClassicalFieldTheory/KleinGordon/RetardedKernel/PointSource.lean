/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedKernel.FourierForm
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Covariance.Distributions

/-!

# The boundary value formula for point sources

The retarded response of a point source at `p` is the boundary value of the resolvent pairing of
the translated test function.

## i. Overview

By transposition the retarded response of a compactly supported distribution `T` tested against `f`
is `T` applied to the advanced solution of `f` (`retardedDistribution_apply`). For a point source
at `p` the advanced solution of `f` at `p` is the retarded kernel applied to the translate of `f`.
The boundary value formula for the kernel (`tendsto_fourierPairing`) then holds for the translate.
This gives the formula for every finite combination of point sources.

## ii. Key results

- `retardedPointSource_eq_kernel_translate` : the point source at `p` is the kernel at the origin
  applied to the translate.
- `tendsto_fourierPairing_translate` : the retarded response of a point source at `p` is the
  boundary value of the resolvent pairing of the translate.

## iii. Table of contents

- A. Translation
- B. The boundary value

## iv. References

None.

## A. Translation

- `retardedPointSource_eq_kernel_translate` : the point source at `p` as a translate.

## B. The boundary value

- `tendsto_fourierPairing_translate` : the boundary value for a point source at `p`.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap Distributions
open SchwartzMap TopologicalSpace TestFunction PoincareGroup KleinGordon.Solution
  KleinGordon.Spacetime

namespace KleinGordon

variable {d : ℕ}

/-- The retarded point source at `p` is the retarded kernel at the origin applied to the
translate. -/
lemma retardedPointSource_eq_kernel_translate (m : ℝ) (p : SpaceTime d)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    retardedPointSource m p φ =
      retardedPointSource m (0 : SpaceTime d) (precompTranslationCLM p φ) := by
  have h := retardedPointSource_actDist (m := m) (g := (⟨p, 1⟩ : PoincareGroup d))
    LorentzGroup.id_isOrthochronous (0 : SpaceTime d)
  have h0 : (⟨p, 1⟩ : PoincareGroup d) • (0 : SpaceTime d) = p := by
    rw [smul_def]
    change (1 : LorentzGroup d) • (0 : SpaceTime d) + p = p
    rw [smul_zero, zero_add]
  rw [h0] at h
  rw [← h, actDist_apply, actTestFunction_translation_inv]

/-- **The boundary value formula for a point source.** The retarded response of the point source
at `p` tested against `φ` is the limit for `ε → 0+` of the resolvent pairing of the translate of
`φ`. By transposition this is the response of the distribution `δ_p`. -/
lemma tendsto_fourierPairing_translate (m : ℝ) (p : SpaceTime d)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    Filter.Tendsto (fun ε : ℝ =>
      (fourierPairing (m ^ 2) ε (ofTestFunction (precompTranslationCLM p φ))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (retardedDistribution m (deltaCompact p) φ)) := by
  rw [← retardedPointSource_eq, retardedPointSource_eq_kernel_translate,
    ← temperedKernel_apply d m]
  exact tendsto_fourierPairing m _

end KleinGordon
