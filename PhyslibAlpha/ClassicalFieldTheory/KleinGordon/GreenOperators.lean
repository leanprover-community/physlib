/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GreenOperator.SmoothFields
public import PhyslibAlpha.ClassicalFieldTheory.GreenOperator.Uniqueness
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Coordinates
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.CutoffResponse
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.FinitePropagation

/-!

# Green operators on spacetime

Retarded and advanced Green operators of the Klein–Gordon equation on `SpaceTime d` for every mass.

## i. Overview

Retarded and advanced Green operators of the Klein–Gordon equation on `SpaceTime d` for every mass.
Uniqueness and the exact sequence follow.

## ii. Key results

- `retardedResponse` : The retarded spatial Fourier response of a compact source on Minkowski
  spacetime.
- `advancedResponse` : The advanced spatial Fourier response of a compact source on Minkowski
  spacetime.
- `testFieldEquiv` : The neighbour's compact smooth fields and Mathlib's bundled test functions have
  the same data.
- `retardedMap` : The retarded Fourier response as a real linear map into the existing smooth-field
  space.
- `advancedMap` : The advanced Fourier response as a real linear map into the existing smooth-field
  space.
- `retardedGreenOperator` : The retarded Fourier Green inverse for the existing Minkowski equation
  in every dimension.
- `advancedGreenOperator` : The advanced Fourier Green inverse for the existing Minkowski equation
  in every dimension.
- `greenOperators` : The spatial Fourier Green pair for Klein–Gordon fields in arbitrary spatial
  dimension.

## iii. Table of contents

- A. The spatial Fourier Green construction on Minkowski spacetime
- B. Fourier Klein–Gordon Green operators in every dimension
- C. Real scalar Fourier Green operators
- D. Continuous evaluation of the spacetime Fourier response
- E. Uniqueness for the Fourier Klein–Gordon Green operators

## iv. References

None.

## A. The spatial Fourier Green construction on Minkowski spacetime

- `retardedResponse` : The retarded spatial Fourier response of a compact source on Minkowski
  spacetime.
- `advancedResponse` : The advanced spatial Fourier response of a compact source on Minkowski
  spacetime.

Lemmas: `contDiff_retardedResponse`, `contDiff_advancedResponse`,
`tsupport_retardedResponse_subset`, `tsupport_advancedResponse_subset`,
`retardedResponse_sourceOperator`, `advancedResponse_sourceOperator`.

## B. Fourier Klein–Gordon Green operators in every dimension

- `testFieldEquiv` : The neighbour's compact smooth fields and Mathlib's bundled test functions have
  the same data.
- `retardedMap` : The retarded Fourier response as a real linear map into the existing smooth-field
  space.
- `advancedMap` : The advanced Fourier response as a real linear map into the existing smooth-field
  space.
- `retardedGreenOperator` : The retarded Fourier Green inverse for the existing Minkowski equation
  in every dimension.
- `advancedGreenOperator` : The advanced Fourier Green inverse for the existing Minkowski equation
  in every dimension.
- `greenOperators` : The spatial Fourier Green pair for Klein–Gordon fields in arbitrary spatial
  dimension.

Lemmas: `testFieldEquiv_compactOperator`, `retardedMap_solves`, `advancedMap_solves`.

## C. Real scalar Fourier Green operators

- `fiberIntertwiner` : A constant fibre transformation intertwines the equal-mass Klein–Gordon
  equations.
- `realRetardedGreenOperator` : The real part of the complex retarded response is a real scalar
  Green inverse.
- `realAdvancedGreenOperator` : The real part of the complex advanced response is a real scalar
  Green inverse.
- `realGreenOperators` : The real scalar Klein–Gordon Green pair for transposition in arbitrary
  spatial dimension.

Lemmas: `fiberIntertwiner_compactOperator`.

## D. Continuous evaluation of the spacetime Fourier response

- `retardedEvaluation` : Continuous evaluation of the complex Banach-valued retarded Fourier
  response.
- `advancedEvaluation` : Continuous evaluation of the complex Banach-valued advanced Fourier
  response.
- `realRetardedEvaluation` : Continuous evaluation of the real scalar retarded Green response.
- `realAdvancedEvaluation` : Continuous evaluation of the real scalar advanced Green response.

Lemmas: `retardedEvaluation_apply`, `advancedEvaluation_apply`, `realRetardedEvaluation_apply`,
`realAdvancedEvaluation_apply`.

## E. Uniqueness for the Fourier Klein–Gordon Green operators

- `solutionSpaceEquivQuotient` : Spacelike-compact homogeneous solutions of the Klein–Gordon
  equation are the compact source classes modulo the equation of motion, in every spatial dimension.

Lemmas: `existsUnique_retardedSolution`, `causalGreen_exactSequence`.

-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff
open CausalRelation FieldIntertwiner LocalOperator Minkowski TestFunction TimeSlice TimeSpace
    WaveEquation TopologicalSpace Topology GreenOperator

namespace KleinGordon.Spacetime

section
variable {d : ℕ} (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The retarded spatial Fourier response of a compact source on Minkowski spacetime. -/
def retardedResponse (μ : ℝ) (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) (p : SpaceTime d) : F :=
  solution F (sourceEquiv F f) μ ((coordinates d) p).1 ((coordinates d) p).2

/-- The advanced spatial Fourier response of a compact source on Minkowski spacetime. -/
def advancedResponse (μ : ℝ) (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) (p : SpaceTime d) : F :=
  advancedSolution F (sourceEquiv F f) μ ((coordinates d) p).1 ((coordinates d) p).2

lemma contDiff_retardedResponse {μ : ℝ} (hμ : 0 ≤ μ)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) : ContDiff ℝ ∞ (retardedResponse F μ f) :=
  (contDiff_solution F (sourceEquiv F f) hμ).comp (coordinates d).contDiff

lemma contDiff_advancedResponse {μ : ℝ} (hμ : 0 ≤ μ)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) : ContDiff ℝ ∞ (advancedResponse F μ f) :=
  (contDiff_advancedSolution F (sourceEquiv F f) hμ).comp (coordinates d).contDiff

/-- The retarded spacetime field has support inside the coordinate light cones of its source. -/
lemma tsupport_retardedResponse_subset {μ : ℝ} (hμ : 0 ≤ μ)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    tsupport (retardedResponse F μ f) ⊆ (coordinates d) ⁻¹'
      causalFuture (coordinates d '' tsupport f) := by
  change tsupport ((fun p => solution F (sourceEquiv F f) μ p.1 p.2) ∘ (coordinates d).toHomeomorph)
    ⊆ _
  rw [tsupport_comp_eq_preimage _ (coordinates d).toHomeomorph]
  intro p hp
  rw [← tsupport_sourceEquiv F f]
  exact tsupport_solution_subset F (sourceEquiv F f) hμ hp

/-- The advanced spacetime field has support inside the past coordinate light cones. -/
lemma tsupport_advancedResponse_subset {μ : ℝ} (hμ : 0 ≤ μ)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    tsupport (advancedResponse F μ f) ⊆ (coordinates d) ⁻¹'
      causalPast (coordinates d '' tsupport f) := by
  change tsupport ((fun p => advancedSolution F (sourceEquiv F f) μ p.1 p.2) ∘ (coordinates
    d).toHomeomorph) ⊆ _
  rw [tsupport_comp_eq_preimage _ (coordinates d).toHomeomorph]
  intro p hp
  rw [← tsupport_sourceEquiv F f]
  exact tsupport_advancedSolution_subset F (sourceEquiv F f) hμ hp

/-- The retarded response recovers a spacetime test field from its compact Klein–Gordon source. -/
lemma retardedResponse_sourceOperator {μ : ℝ} (hμ : 0 ≤ μ)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) (p : SpaceTime d) :
    retardedResponse F μ (sourceOperator F μ f) p = f p := by
  simp only [retardedResponse, sourceOperator, LinearEquiv.apply_symm_apply]
  rw [solution_testOperator F (sourceEquiv F f) hμ]
  change f ((coordinates d).symm ((coordinates d) p)) = f p
  simp

/-- The advanced response recovers a spacetime test field from its compact Klein–Gordon source. -/
lemma advancedResponse_sourceOperator {μ : ℝ} (hμ : 0 ≤ μ)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) (p : SpaceTime d) :
    advancedResponse F μ (sourceOperator F μ f) p = f p := by
  simp only [advancedResponse, sourceOperator, LinearEquiv.apply_symm_apply]
  rw [advancedSolution_testOperator F (sourceEquiv F f) hμ]
  change f ((coordinates d).symm ((coordinates d) p)) = f p
  simp
end

section
variable {d : ℕ} (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The neighbour's compact smooth fields and Mathlib's bundled test functions have the same data.
-/
def testFieldEquiv : TestField d F ≃ₗ[ℝ] 𝓓((⊤ : Opens (SpaceTime d)), F) where
  toFun f := {
    toFun := f.val.val
    contDiff' := f.val.property
    hasCompactSupport' := f.property
    tsupport_subset' := fun _ _ => trivial }
  invFun f := ⟨⟨f, f.contDiff⟩, f.hasCompactSupport⟩
  left_inv f := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv f := by ext p; rfl
  map_add' f g := by ext p; rfl
  map_smul' c f := by ext p; rfl
end

section
variable {d : ℕ} (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma testFieldEquiv_compactOperator (m : ℝ) (f : TestField d F) :
    testFieldEquiv F ((equation m).compactOperator f) =
      sourceOperator F (m ^ 2) (testFieldEquiv F f) := by
  ext p
  exact (sourceOperator_eq_operator m (testFieldEquiv F f) p).symm

/-- The retarded Fourier response as a real linear map into the existing smooth-field space. -/
def retardedMap (m : ℝ) : TestField d F →ₗ[ℝ] smoothFields d F where
  toFun f := ⟨retardedResponse F (m ^ 2) (testFieldEquiv F f),
    contDiff_retardedResponse F (sq_nonneg m) _⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    simp only [retardedResponse, map_add]
    exact solution_add F _ (sq_nonneg m) _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext p
    simp only [retardedResponse, map_smul]
    exact solution_smul F _ (sq_nonneg m) c _ _

/-- The advanced Fourier response as a real linear map into the existing smooth-field space. -/
def advancedMap (m : ℝ) : TestField d F →ₗ[ℝ] smoothFields d F where
  toFun f := ⟨advancedResponse F (m ^ 2) (testFieldEquiv F f),
    contDiff_advancedResponse F (sq_nonneg m) _⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    simp only [advancedResponse, advancedSolution, map_add]
    have he : reflect F (sourceEquiv F (testFieldEquiv F f) + sourceEquiv F (testFieldEquiv F g)) =
        reflect F (sourceEquiv F (testFieldEquiv F f)) + reflect F (sourceEquiv F (testFieldEquiv F
          g)) := by
      ext q; rfl
    rw [he]
    exact solution_add F _ (sq_nonneg m) _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext p
    simp only [advancedResponse, advancedSolution, map_smul]
    have he : reflect F (c • sourceEquiv F (testFieldEquiv F f)) =
        c • reflect F (sourceEquiv F (testFieldEquiv F f)) := by ext q; rfl
    rw [he]
    exact solution_smul F _ (sq_nonneg m) c _ _

lemma retardedMap_solves (m : ℝ) (f : TestField d F) :
    KleinGordon.Spacetime.operator m (retardedMap F m f) = f.val := by
  apply Subtype.ext
  funext p
  change (KleinGordon.Spacetime.operator m
    ⟨(fun q => solution F (sourceEquiv F (testFieldEquiv F f)) (m ^ 2) q.1 q.2) ∘ coordinates d,
      _⟩ : SpaceTime d → F) p = _
  rw [operator_of_coordinates m _ (contDiff_solution F _ (sq_nonneg m))]
  rw [solution_equation_at F _ (sq_nonneg m)]
  change (testFieldEquiv F f) ((coordinates d).symm (coordinates d p)) = f.val.val p
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rfl

lemma advancedMap_solves (m : ℝ) (f : TestField d F) :
    KleinGordon.Spacetime.operator m (advancedMap F m f) = f.val := by
  apply Subtype.ext
  funext p
  change (KleinGordon.Spacetime.operator m
    ⟨(fun q => advancedSolution F (sourceEquiv F (testFieldEquiv F f)) (m ^ 2) q.1 q.2) ∘
      coordinates d,
      _⟩ : SpaceTime d → F) p = _
  rw [operator_of_coordinates m _ (contDiff_advancedSolution F _ (sq_nonneg m))]
  rw [advancedSolution_equation F _ (sq_nonneg m)]
  change (testFieldEquiv F f) ((coordinates d).symm (coordinates d p)) = f.val.val p
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- The retarded Fourier Green inverse for the existing Minkowski equation in every dimension. -/
def retardedGreenOperator (m : ℝ) :
    RetardedGreenOperator (causalRelation d) (equation (V := F) m) where
  toLinearMap := retardedMap F m
  solves := retardedMap_solves F m
  comp_operator f := by
    apply Subtype.ext
    funext p
    change retardedResponse F (m ^ 2)
      (testFieldEquiv F ((equation m).compactOperator f)) p = _
    rw [testFieldEquiv_compactOperator, retardedResponse_sourceOperator F (sq_nonneg m)]
    rfl
  support f := by
    change tsupport (retardedResponse F (m ^ 2) (testFieldEquiv F f)) ⊆ _
    have h := tsupport_retardedResponse_subset F (sq_nonneg m) (testFieldEquiv F f)
    rw [causalFuture_coordinates] at h
    exact h

/-- The advanced Fourier Green inverse for the existing Minkowski equation in every dimension. -/
def advancedGreenOperator (m : ℝ) :
    AdvancedGreenOperator (causalRelation d) (equation (V := F) m) where
  toLinearMap := advancedMap F m
  solves := advancedMap_solves F m
  comp_operator f := by
    apply Subtype.ext
    funext p
    change advancedResponse F (m ^ 2)
      (testFieldEquiv F ((equation m).compactOperator f)) p = _
    rw [testFieldEquiv_compactOperator, advancedResponse_sourceOperator F (sq_nonneg m)]
    rfl
  support f := by
    change tsupport (advancedResponse F (m ^ 2) (testFieldEquiv F f)) ⊆ _
    have h := tsupport_advancedResponse_subset F (sq_nonneg m) (testFieldEquiv F f)
    rw [causalPast_coordinates] at h
    exact h

/-- The spatial Fourier Green pair for Klein–Gordon fields in arbitrary spatial dimension. -/
def greenOperators (m : ℝ) :
    GreenOperators (causalRelation d) (equation (V := F) m) :=
  ⟨retardedGreenOperator F m, advancedGreenOperator F m⟩
end

section
variable {d : ℕ} {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W]

/-- A constant fibre transformation intertwines the equal-mass Klein–Gordon equations. -/
def fiberIntertwiner (m : ℝ) (L : V →L[ℝ] W) :
    FieldIntertwiner (equation (d := d) (V := V) m)
      (equation (d := d) (V := W) m) where
  toLinearMap := smoothFiberMap L
  support u := tsupport_comp_subset (map_zero L) u.val
  commutes u := by
    change KleinGordon.Spacetime.operator m (smoothFiberMap L u) =
      smoothFiberMap L (KleinGordon.Spacetime.operator m u)
    simp only [KleinGordon.Spacetime.operator, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, map_smul, smoothFiberMap_waveOperator]

lemma fiberIntertwiner_compactOperator (m : ℝ) (L : V →L[ℝ] W) (f : TestField d V) :
    (fiberIntertwiner m L).compactMap ((equation m).compactOperator f) =
      (equation m).compactOperator ((fiberIntertwiner m L).compactMap f) := by
  apply Subtype.ext
  exact ((fiberIntertwiner m L).commutes f.val).symm

/-- The real part of the complex retarded response is a real scalar Green inverse. -/
def realRetardedGreenOperator (m : ℝ) :
    RetardedGreenOperator (causalRelation d)
      (equation (V := ℝ) m) where
  toLinearMap := (fiberIntertwiner m Complex.reCLM).toLinearMap.comp
    ((retardedGreenOperator ℂ m).toLinearMap.comp (fiberIntertwiner m Complex.ofRealCLM).compactMap)
  solves f := by
    change (equation m).operator
      ((fiberIntertwiner m Complex.reCLM).toLinearMap _) = _
    rw [(fiberIntertwiner m Complex.reCLM).commutes, LinearMap.comp_apply, (retardedGreenOperator ℂ
      m).solves]
    apply Subtype.ext
    funext p
    exact Complex.ofReal_re _
  comp_operator f := by
    change (fiberIntertwiner m Complex.reCLM).toLinearMap
      ((retardedGreenOperator ℂ m).toLinearMap
        ((fiberIntertwiner m Complex.ofRealCLM).compactMap
          ((equation m).compactOperator f))) = _
    rw [fiberIntertwiner_compactOperator, (retardedGreenOperator ℂ m).comp_operator]
    apply Subtype.ext
    funext p
    exact Complex.ofReal_re _
  support f := by
    refine ((fiberIntertwiner m Complex.reCLM).support _).trans ?_
    exact ((retardedGreenOperator ℂ m).support _).trans
      ((causalRelation d).causalFuture_mono
        ((fiberIntertwiner m Complex.ofRealCLM).support f.val))

/-- The real part of the complex advanced response is a real scalar Green inverse. -/
def realAdvancedGreenOperator (m : ℝ) :
    AdvancedGreenOperator (causalRelation d)
      (equation (V := ℝ) m) where
  toLinearMap := (fiberIntertwiner m Complex.reCLM).toLinearMap.comp
    ((advancedGreenOperator ℂ m).toLinearMap.comp (fiberIntertwiner m Complex.ofRealCLM).compactMap)
  solves f := by
    change (equation m).operator
      ((fiberIntertwiner m Complex.reCLM).toLinearMap _) = _
    rw [(fiberIntertwiner m Complex.reCLM).commutes, LinearMap.comp_apply, (advancedGreenOperator ℂ
      m).solves]
    apply Subtype.ext
    funext p
    exact Complex.ofReal_re _
  comp_operator f := by
    change (fiberIntertwiner m Complex.reCLM).toLinearMap
      ((advancedGreenOperator ℂ m).toLinearMap
        ((fiberIntertwiner m Complex.ofRealCLM).compactMap
          ((equation m).compactOperator f))) = _
    rw [fiberIntertwiner_compactOperator, (advancedGreenOperator ℂ m).comp_operator]
    apply Subtype.ext
    funext p
    exact Complex.ofReal_re _
  support f := by
    refine ((fiberIntertwiner m Complex.reCLM).support _).trans ?_
    exact ((advancedGreenOperator ℂ m).support _).trans
      ((causalRelation d).causalPast_mono
        ((fiberIntertwiner m Complex.ofRealCLM).support f.val))

/-- The real scalar Klein–Gordon Green pair for transposition in arbitrary spatial dimension. -/
def realGreenOperators (m : ℝ) :
    GreenOperators (causalRelation d) (equation (V := ℝ) m) :=
  ⟨realRetardedGreenOperator m, realAdvancedGreenOperator m⟩
end

section
variable {d : ℕ} (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuous evaluation of the complex Banach-valued retarded Fourier response. -/
def retardedEvaluation {μ : ℝ} (hμ : 0 ≤ μ) (p : SpaceTime d) :
    𝓓((⊤ : Opens (SpaceTime d)), F) →L[ℝ] F :=
  (solutionEvaluation F hμ (coordinates d p)).comp
    (precompLinearEquivCLM (coordinates d).symm)

/-- Continuous evaluation of the complex Banach-valued advanced Fourier response. -/
def advancedEvaluation {μ : ℝ} (hμ : 0 ≤ μ) (p : SpaceTime d) :
    𝓓((⊤ : Opens (SpaceTime d)), F) →L[ℝ] F :=
  (advancedSolutionEvaluation F hμ (coordinates d p)).comp
    (precompLinearEquivCLM (coordinates d).symm)

lemma retardedEvaluation_apply {μ : ℝ} (hμ : 0 ≤ μ) (p : SpaceTime d)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    retardedEvaluation F hμ p f = retardedResponse F μ f p := rfl

lemma advancedEvaluation_apply {μ : ℝ} (hμ : 0 ≤ μ) (p : SpaceTime d)
    (f : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    advancedEvaluation F hμ p f = advancedResponse F μ f p := by
  rw [advancedEvaluation, ContinuousLinearMap.comp_apply, advancedSolutionEvaluation_apply]
  rfl

/-- Continuous evaluation of the real scalar retarded Green response. -/
def realRetardedEvaluation (m : ℝ) (p : SpaceTime d) :
    𝓓((⊤ : Opens (SpaceTime d)), ℝ) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((retardedEvaluation ℂ (sq_nonneg m) p).comp
    (TestFunction.postcompCLM Complex.ofRealCLM))

/-- Continuous evaluation of the real scalar advanced Green response. -/
def realAdvancedEvaluation (m : ℝ) (p : SpaceTime d) :
    𝓓((⊤ : Opens (SpaceTime d)), ℝ) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((advancedEvaluation ℂ (sq_nonneg m) p).comp
    (TestFunction.postcompCLM Complex.ofRealCLM))

lemma realRetardedEvaluation_apply (m : ℝ) (p : SpaceTime d) (f : TestField d ℝ) :
    realRetardedEvaluation m p (testFieldEquiv ℝ f) =
      ((realRetardedGreenOperator m).toLinearMap f).val p := rfl

lemma realAdvancedEvaluation_apply (m : ℝ) (p : SpaceTime d) (f : TestField d ℝ) :
    realAdvancedEvaluation m p (testFieldEquiv ℝ f) =
      ((realAdvancedGreenOperator m).toLinearMap f).val p := by
  change Complex.re (advancedEvaluation ℂ (sq_nonneg m) p _) = _
  rw [advancedEvaluation_apply]
  rfl

/-- A compact smooth source has exactly one sharply retarded solution of the Klein–Gordon
equation, in every spatial dimension. -/
lemma existsUnique_retardedSolution (m : ℝ)
    (f : (equation (d := d) (V := F) m).compactSources) :
    ∃! u : smoothFields d F,
      (equation (V := F) m).operator u = f.val ∧
      tsupport (u : SpaceTime d → F) ⊆
        (causalRelation d).causalFuture (tsupport (f.val : SpaceTime d → F)) :=
  (retardedGreenOperator F m).existsUnique_retardedSolution_of_localization
    (Minkowski.smoothPastLocalization _) (hasCompactCausalDiamonds d) f

/-- The causal Green sequence for the Klein–Gordon equation in every spatial dimension:
the equation of motion is injective on compact fields, the causal propagator is exact in the
middle and the equation of motion is surjective on spacelike-compact fields. -/
lemma causalGreen_exactSequence (m : ℝ) :
    let P := equation (d := d) (V := F) m
    Function.Injective P.compactOperator ∧
      Function.Exact P.compactOperator (greenOperators F m).toSpacelikeCompact ∧
      Function.Exact (greenOperators F m).toSpacelikeCompact
        (P.spacelikeCompactOperator (causalRelation d)) ∧
      Function.Surjective (P.spacelikeCompactOperator (causalRelation d)) :=
  (greenOperators F m).causalGreen_exactSequence (Minkowski.smoothPastLocalization _)
    (Minkowski.smoothFutureLocalization _) (hasCompactCausalDiamonds d)
    (Minkowski.smoothHasCausalCutoffs _)

/-- Fix the inherited field addition for quotient inference. -/
local instance smoothFieldsAddGroup : AddCommGroup (smoothFields d F) :=
  (smoothFields d F).addCommGroup

/-- Spacelike-compact homogeneous solutions of the Klein–Gordon equation are the compact source
classes modulo the equation of motion, in every spatial dimension. -/
noncomputable def solutionSpaceEquivQuotient (m : ℝ) :
    let P := equation (d := d) (V := F) m
    P.spacelikeCompactSolution (causalRelation d) ≃ₗ[ℝ]
      (P.compactSources ⧸ LinearMap.range P.compactOperator) :=
  (greenOperators F m).solutionSpaceEquivQuotientOfLocalization (Minkowski.smoothPastLocalization _)
    (Minkowski.smoothFutureLocalization _) (hasCompactCausalDiamonds d)
    (Minkowski.smoothHasCausalCutoffs _)
end

end KleinGordon.Spacetime
