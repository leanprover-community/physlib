/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!

# Operations on test functions

## i. Overview

Multiplication by a weight and composition with a linear equivalence are continuous on test
functions.

## ii. Key results

- `precompLinearEquivSupportedCLM` : Pullback between fixed-support smooth test spaces by an
  invertible linear coordinate map.
- `precompLinearEquivCLM` : Pullback by an invertible continuous linear coordinate change is
  continuous on smooth tests.
- `weightedTestBCFLinear` : Weight a compact smooth test field and retain its bounded continuous
  representative.
- `weightedTestBCF` : Arbitrary continuous weights give continuous maps from the native LF
  test-function space into the uniform norm.
- `smoothWeightTest` : Multiplication by a smooth weight is continuous in the native LF test
  topology.

## iii. Table of contents

- A. Continuous linear changes of test-function coordinates
- B. Weighted test functions in the uniform norm

## iv. References

None.

## A. Continuous linear changes of test-function coordinates

- `precompLinearEquivSupportedCLM` : Pullback between fixed-support smooth test spaces by an
  invertible linear coordinate map.
- `precompLinearEquivCLM` : Pullback by an invertible continuous linear coordinate change is
  continuous on smooth tests.

Lemmas: `precompLinearEquivCLM_apply`.

## B. Weighted test functions in the uniform norm

- `weightedTestBCFLinear` : Weight a compact smooth test field and retain its bounded continuous
  representative.
- `weightedTestBCF` : Arbitrary continuous weights give continuous maps from the native LF
  test-function space into the uniform norm.
- `smoothWeightTest` : Multiplication by a smooth weight is continuous in the native LF test
  topology.

Lemmas: `weightedTestBCF_apply`, `smoothWeightTest_apply`.

-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff CompactlySupported BoundedContinuousFunction
open TopologicalSpace Topology MeasureTheory

namespace TestFunction

section
variable {A B F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback between fixed-support smooth test spaces by an invertible linear coordinate map. -/
def precompLinearEquivSupportedCLM (e : A ≃L[ℝ] B) (K : Compacts B) :
    ContDiffMapSupportedIn B F ⊤ K →L[ℝ]
      ContDiffMapSupportedIn A F ⊤ (K.map e.symm e.symm.continuous) :=
  let L : ContDiffMapSupportedIn B F ⊤ K →ₗ[ℝ]
      ContDiffMapSupportedIn A F ⊤ (K.map e.symm e.symm.continuous) := {
    toFun f := ⟨f ∘ e, f.contDiff.comp e.contDiff, fun x hx => by
      apply f.zero_on_compl
      intro he
      exact hx ⟨e x, he, e.symm_apply_apply x⟩⟩
    map_add' f g := by ext x; rfl
    map_smul' c f := by ext x; rfl }
  { toLinearMap := L
    cont := by
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms ℝ B F ⊤ K)
        (ContDiffMapSupportedIn.withSeminorms ℝ A F ⊤ (K.map e.symm e.symm.continuous)) L
        (.of_real fun n => ?_)
      refine ⟨{n}, ‖e.toContinuousLinearMap‖ ^ n, fun f => ?_⟩
      simp only [Finset.sup_singleton]
      apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ
        (mul_nonneg (by positivity) (apply_nonneg _ _)) n (L f)).mpr
      intro x hx
      change ‖iteratedFDeriv ℝ n (f ∘ e.toContinuousLinearMap) x‖ ≤ _
      rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ f.contDiff x (by simp)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc
        _ ≤ ContDiffMapSupportedIn.seminorm ℝ B F ⊤ K n f * ‖e.toContinuousLinearMap‖ ^ n :=
          mul_le_mul_of_nonneg_right
            (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ) (by positivity)
        _ = _ := mul_comm _ _ }

/-- Pullback by an invertible continuous linear coordinate change is continuous on smooth tests. -/
def precompLinearEquivCLM (e : A ≃L[ℝ] B) :
    𝓓((⊤ : Opens B), F) →L[ℝ] 𝓓((⊤ : Opens A), F) :=
  TestFunction.mkCLM ℝ (fun f => {
    toFun := f ∘ e
    contDiff' := f.contDiff.comp e.contDiff
    hasCompactSupport' := f.hasCompactSupport.comp_homeomorph e.toHomeomorph
    tsupport_subset' := fun _ _ => trivial })
    (fun f g => by ext x; rfl) (fun c f => by ext x; rfl) (by
      intro K hK
      exact (TestFunction.ofSupportedInCLM ℝ (Ω := ⊤) (by simp)).continuous.comp
        (precompLinearEquivSupportedCLM (F := F) e K).continuous)

@[simp]
lemma precompLinearEquivCLM_apply (e : A ≃L[ℝ] B) (f : 𝓓((⊤ : Opens B), F)) (x : A) :
    precompLinearEquivCLM e f x = f (e x) := rfl
end

section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace
    ℝ V]

/-- Weight a compact smooth test field and retain its bounded continuous representative. -/
def weightedTestBCFLinear (w : E → ℝ) (hw : Continuous w) :
    _root_.TestFunction (⊤ : TopologicalSpace.Opens E) V ⊤ →ₗ[ℝ] (E →ᵇ V) where
  toFun φ := (⟨⟨fun x => w x • φ x, hw.smul φ.continuous⟩,
    φ.hasCompactSupport.smul_left⟩ : C_c(E, V)).toBoundedContinuousFunction
  map_add' _ _ := by ext x; exact smul_add _ _ _
  map_smul' _ _ := by ext x; exact smul_comm _ _ _

/-- Arbitrary continuous weights give continuous maps from the native LF test-function space
into the uniform norm. No global bound on the weight is required. -/
def weightedTestBCF (w : E → ℝ) (hw : Continuous w) :
    _root_.TestFunction (⊤ : TopologicalSpace.Opens E) V ⊤ →L[ℝ] (E →ᵇ V) :=
  TestFunction.mkCLM ℝ (weightedTestBCFLinear w hw)
    (weightedTestBCFLinear w hw).map_add (weightedTestBCFLinear w hw).map_smul
    fun K hK => by
      let A := (weightedTestBCFLinear (V := V) w hw).comp
        (TestFunction.ofSupportedInCLM ℝ hK).toLinearMap
      obtain ⟨C, hC⟩ := K.isCompact.exists_bound_of_continuousOn hw.continuousOn
      have hb : ∃ s : Finset ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ φ,
          ‖A φ‖ ≤ B * (s.sup fun i => ContDiffMapSupportedIn.seminorm ℝ E V ⊤ K i) φ := by
        refine ⟨{0}, max C 0, le_max_right _ _, ?_⟩
        intro φ
        simp only [Finset.sup_singleton]
        apply BoundedContinuousFunction.norm_le
          (mul_nonneg (le_max_right _ _) (apply_nonneg _ _)) |>.mpr
        intro x
        change ‖w x • φ x‖ ≤ _
        by_cases hx : x ∈ K
        · rw [norm_smul]
          exact mul_le_mul
            ((hC x hx).trans (le_max_left _ _))
            (ContDiffMapSupportedIn.norm_apply_le_seminorm ℝ) (norm_nonneg _) (le_max_right _ _)
        · rw [φ.zero_on_compl hx, Pi.zero_apply, smul_zero, norm_zero]
          exact mul_nonneg (le_max_right _ _) (apply_nonneg _ _)
      exact (ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ A A.map_add A.map_smul hb).continuous

/-- The weighted embedding retains the pointwise weighted field. -/
lemma weightedTestBCF_apply (w : E → ℝ) (hw : Continuous w)
    (φ : _root_.TestFunction (⊤ : TopologicalSpace.Opens E) V ⊤) (x : E) :
    weightedTestBCF w hw φ x = w x • φ x := rfl

/-- Multiplication by a smooth weight is continuous in the native LF test topology. -/
def smoothWeightTest (w : E → ℝ) (hw : ContDiff ℝ ∞ w) :
    _root_.TestFunction (⊤ : TopologicalSpace.Opens E) V ⊤ →L[ℝ]
      _root_.TestFunction (⊤ : TopologicalSpace.Opens E) V ⊤ :=
  TestFunction.mkCLM ℝ
    (fun φ => ⟨fun p => w p • φ p, hw.smul φ.contDiff,
      φ.hasCompactSupport.smul_left, Set.subset_univ _⟩)
    (fun φ ψ => by ext p; exact smul_add _ _ _)
    (fun a φ => by ext p; exact smul_comm _ _ _)
    (fun K hK => by
      let B : V →L[ℝ] ℝ →L[ℝ] V :=
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V).flip
      let S : ContDiffMapSupportedIn E V ⊤ K →L[ℝ]
          _root_.TestFunction (⊤ : TopologicalSpace.Opens E) V ⊤ :=
        (TestFunction.ofSupportedInCLM ℝ hK).comp
          (ContDiffMapSupportedIn.bilinLeftCLM B hw)
      apply S.continuous.congr
      intro φ
      ext p
      rfl)

/-- The LF-continuous weight map is pointwise scalar multiplication. -/
lemma smoothWeightTest_apply (w : E → ℝ) (hw : ContDiff ℝ ∞ w)
    (φ : _root_.TestFunction (⊤ : TopologicalSpace.Opens E) V ⊤) (p : E) :
    smoothWeightTest w hw φ p = w p • φ p := rfl
end

end TestFunction
