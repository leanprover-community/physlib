/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Distribution.TestFunction

/-!

# Translation of test functions

Translation is continuous on the space of test functions.

## i. Overview

Composition with a translation `x ↦ x + b` maps a smooth function with support in a compact set
`K` to a smooth function with support in the translated set. It does not change the norms of the
derivatives. So it is continuous between the spaces of test functions with fixed support. It is
then continuous on all test functions.

## ii. Key results

- `TestFunction.precompTranslationSupportedCLM` : the pullback between fixed-support spaces.
- `TestFunction.precompTranslationCLM` : the pullback is continuous on test functions.

## iii. Table of contents

- A. The pullback along a translation

## iv. References

None.

## A. The pullback along a translation

- `TestFunction.precompTranslationSupportedCLM` : the pullback between fixed-support spaces.
- `TestFunction.precompTranslationCLM` : the pullback is continuous on test functions.
-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff
open TopologicalSpace Topology

namespace TestFunction

variable {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup F]
    [NormedSpace ℝ F]

/-- The pullback along a translation between fixed-support smooth test spaces. -/
def precompTranslationSupportedCLM (b : A) (K : Compacts A) :
    ContDiffMapSupportedIn A F ⊤ K →L[ℝ]
      ContDiffMapSupportedIn A F ⊤ (K.map (fun x => x - b) (continuous_id.sub continuous_const)) :=
  let L : ContDiffMapSupportedIn A F ⊤ K →ₗ[ℝ]
      ContDiffMapSupportedIn A F ⊤ (K.map (fun x => x - b)
        (continuous_id.sub continuous_const)) := {
    toFun f := ⟨fun x => f (x + b), f.contDiff.comp (contDiff_id.add contDiff_const),
      fun x hx => by
        apply f.zero_on_compl
        intro hK
        exact hx ⟨x + b, hK, by simp⟩⟩
    map_add' f g := by ext x; rfl
    map_smul' c f := by ext x; rfl }
  { toLinearMap := L
    cont := by
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms ℝ A F ⊤ K)
        (ContDiffMapSupportedIn.withSeminorms ℝ A F ⊤
          (K.map (fun x => x - b) (continuous_id.sub continuous_const))) L
        (.of_real fun n => ?_)
      refine ⟨{n}, 1, fun f => ?_⟩
      simp only [Finset.sup_singleton, one_mul]
      apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (apply_nonneg _ _) n (L f)).mpr
      intro x hx
      change ‖iteratedFDeriv ℝ n (fun z => f (z + b)) x‖ ≤ _
      rw [iteratedFDeriv_comp_add_right]
      exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ }

/-- The pullback along a translation is continuous on test functions. -/
def precompTranslationCLM (b : A) : 𝓓((⊤ : Opens A), F) →L[ℝ] 𝓓((⊤ : Opens A), F) :=
  TestFunction.mkCLM ℝ (fun f => {
    toFun := fun x => f (x + b)
    contDiff' := f.contDiff.comp (contDiff_id.add contDiff_const)
    hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (Homeomorph.addRight b)
    tsupport_subset' := fun _ _ => trivial })
    (fun f g => by ext x; rfl) (fun c f => by ext x; rfl) (by
      intro K hK
      exact (TestFunction.ofSupportedInCLM ℝ (Ω := ⊤) (by simp)).continuous.comp
        (precompTranslationSupportedCLM (F := F) b K).continuous)

/-- The pullback along a translation evaluates the function at the translated point. -/
@[simp]
lemma precompTranslationCLM_apply (b : A) (f : 𝓓((⊤ : Opens A), F)) (x : A) :
    precompTranslationCLM b f x = f (x + b) := rfl

end TestFunction
