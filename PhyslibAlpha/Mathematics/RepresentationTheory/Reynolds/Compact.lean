/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Reynolds.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Basic
/-!

# Reynolds elements for compact groups

Continuous finite-dimensional representations of compact groups have Reynolds elements.

## i. Overview

Let `ρ` be a complex representation of a compact topological group `H` and `W` a
finite-dimensional subrepresentation on which `ρ` is continuous. Averaging the operators `ρ h`
on `W` over the normalized Haar measure gives an operator `P` on `W`. Left invariance of the Haar
measure gives `ρ g ∘ P = P`, so `P` maps into the invariants of `W`.

The operator `P` is also a finite combination `Σ cᵢ ρ hᵢ` with `Σ cᵢ = 1`. The set
`1 + span {ρ h - 1}`, the affine span of the operators `ρ h`, is closed and convex because it is a
translate of a finite-dimensional subspace. It contains every `ρ h`, so it contains their average
by `Convex.integral_mem`. By `Representation.exists_isReynolds_of_sub_one_mem_span` this makes
`P` the action of a Reynolds element.

The integral is carried out in coordinates. A basis identifies `W` with `Fin n → ℂ`, and the
operators `ρ h` become continuous linear maps on this normed space.

Continuity of `ρ` on `W` is phrased without a topology on `W` or `V`, as continuity of every
matrix coefficient `h ↦ φ (ρ h w)` with `φ` a linear functional on `W`. Since `W` is
finite-dimensional this is continuity for its unique vector space topology. A finite spanning
family with continuous coefficients is enough to prove it.

## ii. Key results

- `Representation.ContinuousMatrixCoeff` is continuity of a representation on a subspace.
- `Representation.continuousMatrixCoeff_of_span` proves it from a finite spanning family.
- `Representation.exists_isReynolds_of_compactSpace` gives Reynolds elements for compact groups.

## iii. Table of contents

- A. Continuity on a finite-dimensional subrepresentation
  - A.1. The definition
  - A.2. Continuity from a spanning family
- B. Averaging continuous linear maps over a compact group
  - B.1. The average lies in one plus the span of the group image
  - B.2. The average is invariant
- C. The subrepresentation in coordinates
- D. Existence of Reynolds elements

## iv. References

- The Haar average as a Reynolds operator, see for example
  T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*.

-/

@[expose] public section

open MeasureTheory TopologicalSpace

namespace Representation

/-!

## A. Continuity on a finite-dimensional subrepresentation

### A.1. The definition

-/

section Continuity

variable {k H V : Type*} [CommRing k] [TopologicalSpace k] [Group H] [TopologicalSpace H]
  [AddCommGroup V] [Module k V] {ρ : Representation k H V}

/-- The representation is continuous on the subrepresentation `W` if every matrix coefficient
`h ↦ φ (ρ h w)`, for `w` in `W` and `φ` a linear functional on `W`, is continuous. For a
finite-dimensional `W` this is continuity for the unique vector space topology on `W`. -/
def ContinuousMatrixCoeff (W : Subrepresentation ρ) : Prop :=
  ∀ (w : W.toSubmodule) (φ : Module.Dual k W.toSubmodule),
    Continuous fun h => φ (W.toRepresentation h w)

/-!

### A.2. Continuity from a spanning family

-/

/-- A subrepresentation spanned by a finite family `v`, on which the group acts by continuous
coefficients `ρ h (v i) = Σ j, a i j h • v j`, has continuous matrix coefficients. -/
lemma continuousMatrixCoeff_of_span [IsTopologicalRing k] {ι : Type*} [Fintype ι]
    (W : Subrepresentation ρ) (v : ι → V) (hvW : ∀ i, v i ∈ W.toSubmodule)
    (hspan : W.toSubmodule ≤ Submodule.span k (Set.range v)) (a : ι → ι → H → k)
    (ha : ∀ i j, Continuous (a i j)) (hρ : ∀ h i, ρ h (v i) = ∑ j, a i j h • v j) :
    ContinuousMatrixCoeff W := by
  intro w φ
  let v' : ι → W.toSubmodule := fun i => ⟨v i, hvW i⟩
  have hρ' (h : H) (i : ι) : W.toRepresentation h (v' i) = ∑ j, a i j h • v' j := by
    ext
    simp only [v', Submodule.coe_sum, Submodule.coe_smul]
    exact hρ h i
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 (hspan w.2)
  have hw : w = ∑ i, c i • v' i := by
    ext
    simp only [v', Submodule.coe_sum, Submodule.coe_smul]
    exact hc.symm
  have hφ : (fun h => φ (W.toRepresentation h w)) =
      fun h => ∑ i, c i * ∑ j, a i j h * φ (v' j) := by
    funext h
    simp [hw, map_sum, hρ', smul_eq_mul]
  rw [hφ]
  fun_prop

end Continuity

/-!

## B. Averaging continuous linear maps over a compact group

### B.1. The average lies in one plus the span of the group image

-/

section Average

variable {H E : Type*} [MeasurableSpace H] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The average of a family of operators on a finite-dimensional space, with respect to a
probability measure, lies in the affine span `1 + span {F h - 1}` of the family. -/
lemma integral_sub_one_mem_span (μ : Measure H) [IsProbabilityMeasure μ]
    {F : H → E →L[ℂ] E} (hF : Integrable F μ) :
    (∫ h, F h ∂μ) - 1 ∈ Submodule.span ℂ (Set.range fun h => F h - 1) := by
  have := FiniteDimensional.completeSpace ℂ E
  set N := Submodule.span ℂ (Set.range fun h => F h - 1)
  have hconv : Convex ℝ {M : E →L[ℂ] E | M - 1 ∈ N} := by
    intro x hx y hy a b _ _ hab
    obtain rfl : b = 1 - a := eq_sub_of_add_eq' hab
    have heq : a • x + (1 - a) • y - 1 = a • (x - 1) + (1 - a) • (y - 1) := by module
    rw [Set.mem_ofPred_eq, heq]
    exact N.add_mem (N.smul_of_tower_mem a hx) (N.smul_of_tower_mem (1 - a) hy)
  have hclosed : IsClosed {M : E →L[ℂ] E | M - 1 ∈ N} :=
    N.isClosed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)
  exact hconv.integral_mem hclosed
    (Filter.Eventually.of_forall fun h => Submodule.subset_span ⟨h, rfl⟩) hF

/-!

### B.2. The average is invariant

-/

/-- The average of a multiplicative family of operators over a left-invariant measure is
absorbed by each operator of the family. -/
lemma comp_integral_eq_integral [Group H] [MeasurableMul H] (μ : Measure H) [μ.IsMulLeftInvariant]
    {F : H → E →L[ℂ] E} (hF : Integrable F μ) (hmul : ∀ g h, F (g * h) = (F g).comp (F h))
    (g : H) : (F g).comp (∫ h, F h ∂μ) = ∫ h, F h ∂μ := by
  have := FiniteDimensional.completeSpace ℂ E
  rw [← ContinuousLinearMap.compL_apply ℂ E E E (F g),
    ← ContinuousLinearMap.integral_comp_comm _ hF]
  simp only [ContinuousLinearMap.compL_apply, ← hmul]
  exact integral_mul_left_eq_self F g

end Average

/-!

## C. The subrepresentation in coordinates

-/

variable {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}

/-- The action of a group element on a finite-dimensional subrepresentation, written in the
coordinates of a chosen basis as a continuous linear map on `Fin n → ℂ`. -/
noncomputable def coordRep (W : Subrepresentation ρ) [FiniteDimensional ℂ W.toSubmodule]
    (h : H) : (Fin (Module.finrank ℂ W.toSubmodule) → ℂ) →L[ℂ]
      (Fin (Module.finrank ℂ W.toSubmodule) → ℂ) :=
  LinearMap.toContinuousLinearMap
    ((Module.finBasis ℂ W.toSubmodule).equivFun.conj (W.toRepresentation h))

variable (W : Subrepresentation ρ) [FiniteDimensional ℂ W.toSubmodule]

/-- The coordinate form of the action is the action conjugated by the coordinate map. -/
lemma coordRep_apply (h : H) (x : Fin (Module.finrank ℂ W.toSubmodule) → ℂ) :
    coordRep W h x = (Module.finBasis ℂ W.toSubmodule).equivFun
      (W.toRepresentation h ((Module.finBasis ℂ W.toSubmodule).equivFun.symm x)) := by
  simp [coordRep, LinearEquiv.conj_apply]

/-- The coordinate form of the action is multiplicative. -/
lemma coordRep_mul (g h : H) : coordRep W (g * h) = (coordRep W g).comp (coordRep W h) := by
  ext x : 1
  simp [coordRep_apply, map_mul]

/-- The action on a vector given by its coordinates, in terms of the coordinate form. -/
lemma toRepresentation_apply_equivFun_symm (h : H)
    (x : Fin (Module.finrank ℂ W.toSubmodule) → ℂ) :
    W.toRepresentation h ((Module.finBasis ℂ W.toSubmodule).equivFun.symm x) =
      (Module.finBasis ℂ W.toSubmodule).equivFun.symm (coordRep W h x) := by
  simp [coordRep_apply]

/-- The coordinate form of the representation is continuous when the matrix coefficients are. -/
lemma continuous_coordRep [TopologicalSpace H] (hW : ContinuousMatrixCoeff W) :
    Continuous (coordRep W) := by
  refine continuous_clm_apply.2 fun x => continuous_pi fun i => ?_
  simp only [coordRep_apply, Module.Basis.equivFun_apply, ← Module.Basis.coord_apply]
  exact hW _ _

/-- Conjugating back to the subrepresentation, an operator in `1 + span {coordRep h - 1}`
becomes an operator in `1 + span {ρ h - 1}`. -/
lemma conj_sub_one_mem_span
    {P : (Fin (Module.finrank ℂ W.toSubmodule) → ℂ) →L[ℂ] Fin (Module.finrank ℂ W.toSubmodule) → ℂ}
    (hP : P - 1 ∈ Submodule.span ℂ (Set.range fun h => coordRep W h - 1)) :
    (Module.finBasis ℂ W.toSubmodule).equivFun.symm.conj (P : Module.End ℂ _) - 1 ∈
      Submodule.span ℂ (Set.range fun h => W.toRepresentation h - 1) := by
  let L := (Module.finBasis ℂ W.toSubmodule).equivFun.symm.conj.toLinearMap ∘ₗ
    ContinuousLinearMap.coeLM ℂ
  have hL1 : L 1 = 1 := LinearMap.ext fun w => by
    simp only [L, LinearMap.comp_apply, LinearEquiv.conj_apply, ContinuousLinearMap.coeLM_apply,
      ContinuousLinearMap.toLinearMap_one, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply, one_apply_eq_self]
  have hLρ (h : H) : L (coordRep W h) = W.toRepresentation h := LinearMap.ext fun w => by
    simp only [L, LinearMap.comp_apply, LinearEquiv.conj_apply, ContinuousLinearMap.coeLM_apply,
      ContinuousLinearMap.coe_coe, coordRep_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
      LinearEquiv.symm_apply_apply]
  have hcomp : L ∘ (fun h => coordRep W h - 1) = fun h => W.toRepresentation h - 1 := by
    funext h
    simp only [Function.comp_apply, map_sub, hLρ, hL1]
  have hmem := Submodule.mem_map_of_mem (f := L) hP
  rwa [Submodule.map_span, ← Set.range_comp, hcomp, map_sub, hL1] at hmem

/-!

## D. Existence of Reynolds elements

-/

/-- A representation of a compact group which is continuous on a finite-dimensional
subrepresentation has a Reynolds element on it. The Reynolds element realizes the average of the
group action over the normalized Haar measure. -/
lemma exists_isReynolds_of_compactSpace [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (hW : ContinuousMatrixCoeff W) : ∃ r, ρ.IsReynolds W.toSubmodule r := by
  borelize H
  let μ : Measure H := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨by
    simpa [PositiveCompacts.coe_top] using
      Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts H))⟩
  have hint : Integrable (coordRep W) μ :=
    (continuous_coordRep W hW).integrable_of_hasCompactSupport (.of_compactSpace _)
  set P' := ∫ h, coordRep W h ∂μ
  have hP' (g : H) : (coordRep W g).comp P' = P' :=
    comp_integral_eq_integral μ hint (coordRep_mul W) g
  have hinv (w : W.toSubmodule) : (Module.finBasis ℂ W.toSubmodule).equivFun.symm.conj
      (P' : Module.End ℂ _) w ∈ W.toRepresentation.invariants := by
    rw [mem_invariants]
    intro g
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
    rw [toRepresentation_apply_equivFun_symm, ← ContinuousLinearMap.comp_apply, hP']
  obtain ⟨r, hr, -⟩ := exists_isReynolds_of_sub_one_mem_span W
    (conj_sub_one_mem_span W (integral_sub_one_mem_span μ hint)) hinv
  exact ⟨r, hr⟩

end Representation
