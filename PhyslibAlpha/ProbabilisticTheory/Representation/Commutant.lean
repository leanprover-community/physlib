/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.VectorMeasure
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.BoundedIntegralCommute
public import PhyslibAlpha.ProbabilisticTheory.Representation.MomentumSectors

/-!

# The commutant of a unitary representation of an abelian group

Every bounded operator commuting with a unitary representation of an abelian group is decomposable
over the characters of the group.

## i. Overview

The spectral measure `P` of a unitary representation `π` commutes with every bounded operator `T`
that commutes with all `π(g)`: such an operator maps each spectral subspace into itself, it is
reduced by the spectral decomposition of `π`. Consequently the closed subspaces invariant under
the representation are exactly the closed subspaces invariant under the spectral measure, and
the spectral projection onto a single character `χ` of a countable group is the projection onto
the subspace of vectors of crystal momentum `χ`.

## ii. Key results

- `UnitaryRep.projection` : the spectral projection of a set of characters.
- `UnitaryRep.projection_commute` : the spectral projections commute with the commutant.
- `UnitaryRep.mapsTo_projection_of_invariant` : spectral projections preserve every closed
  invariant subspace.
- `UnitaryRep.range_projection_singleton` : the projection onto the character `χ` is the
  projection onto the subspace of momentum `χ`.

## iii. Table of contents

- A. Spectral projections
- B. Commutation with the commutant
- C. Invariant subspaces
- D. Sectors of definite momentum

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology WeakDual
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

namespace UnitaryRep

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : Multiplicative G →* unitary (H →L[ℂ] H))
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-! ## A. Spectral projections -/

/-- The spectral projection of a set of characters, as a bounded operator. -/
def projection (S : Set (PontryaginDual (Multiplicative G))) : H →L[ℂ] H :=
  ContinuousLinearMapWOT.toCLM (spectralMeasure π S)

lemma projection_isStarProjection (S : Set (PontryaginDual (Multiplicative G))) :
    IsStarProjection (projection π S) := by
  have h := (spectralMeasure π).isStarProjection S
  refine ⟨?_, ?_⟩
  · exact congrArg ContinuousLinearMapWOT.toCLM h.isIdempotentElem
  · exact congrArg ContinuousLinearMapWOT.toCLM h.isSelfAdjoint

lemma projection_eq_zero_of_not_measurable {S : Set (PontryaginDual (Multiplicative G))}
    (hS : ¬ MeasurableSet S) : projection π S = 0 := by
  have h : spectralMeasure π S = 0 :=
    (spectralMeasure π).toVectorMeasure.not_measurable hS
  simp [projection, h]

/-! ## B. Commutation with the commutant -/

/-- **The commutant is decomposable**: every bounded operator commuting with the representation
commutes with every spectral projection. -/
lemma projection_commute {T : H →L[ℂ] H}
    (hT : ∀ g, Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) T)
    (S : Set (PontryaginDual (Multiplicative G))) : Commute (projection π S) T := by
  by_cases hS : MeasurableSet S
  · have hT' : ∀ a ∈ (family π).carrier, Commute a T := by
      rintro _ ⟨g, rfl⟩
      exact hT g
    have h := (family π).spectralMeasure_commute hT' (dual π ⁻¹' S)
    have hmap : spectralMeasure π S = (family π).spectralMeasure (dual π ⁻¹' S) :=
      WOTSpectralMeasure.map_apply _ _ (continuous_dual π).measurable hS
    change projection π S * T = T * projection π S
    simp only [projection, hmap]
    exact congrArg ContinuousLinearMapWOT.toCLM h
  · rw [projection_eq_zero_of_not_measurable π hS]
    exact Commute.zero_left T

/-! ## C. Invariant subspaces -/

omit [CompleteSpace H] in
/-- An operator mapping a closed subspace and its orthogonal complement into themselves commutes
with the orthogonal projection onto the subspace. -/
lemma commute_starProjection_of_mapsTo (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    {T : H →L[ℂ] H} (hW : ∀ v ∈ W, T v ∈ W) (hWo : ∀ v ∈ Wᗮ, T v ∈ Wᗮ) :
    Commute (W.starProjection : H →L[ℂ] H) T := by
  ext v
  have hv := Submodule.starProjection_apply_mem W v
  have hvo := Submodule.sub_starProjection_mem_orthogonal (K := W) v
  have h := Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := W) (u := T v)
    (v := T (W.starProjection v)) (hW _ hv) (fun w hw => by
      have := hWo _ hvo
      rw [Submodule.mem_orthogonal'] at this
      simpa [map_sub] using this w hw)
  change W.starProjection (T v) = T (W.starProjection v)
  exact h

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [TopologicalSpace G] in
lemma inner_unitary_left (g : Multiplicative G) (x w : H) :
    ⟪((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x, w⟫_ℂ =
      ⟪x, ((π g⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) w⟫_ℂ := by
  have hadj : ContinuousLinearMap.adjoint ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      ((π g⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  rw [← hadj]
  exact (ContinuousLinearMap.adjoint_inner_right _ x w).symm

/-- A closed subspace invariant under the representation is invariant under every spectral
projection. -/
lemma mapsTo_projection_of_invariant (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (hW : ∀ g, ∀ v ∈ W, ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v ∈ W)
    (S : Set (PontryaginDual (Multiplicative G))) {v : H} (hv : v ∈ W) :
    projection π S v ∈ W := by
  have hcomm : ∀ g, Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
      (W.starProjection : H →L[ℂ] H) := fun g =>
    (commute_starProjection_of_mapsTo W (hW g) (fun u hu => by
      rw [Submodule.mem_orthogonal'] at hu ⊢
      intro w hw
      rw [inner_unitary_left, hu _ (hW g⁻¹ w hw)])).symm
  have h := (projection_commute π hcomm S).symm.eq
  have hv' : W.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have := congrArg (fun A : H →L[ℂ] H => A v) h
  simp only [mul_apply_eq_comp] at this
  rw [hv'] at this
  rw [← this]
  exact Submodule.starProjection_apply_mem W _

/-- A closed subspace invariant under every spectral projection is invariant under the
representation. -/
lemma mapsTo_of_projection_invariant (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (hW : ∀ (S : Set (PontryaginDual (Multiplicative G))), ∀ v ∈ W, projection π S v ∈ W)
    (g : Multiplicative G) {v : H} (hv : v ∈ W) :
    ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v ∈ W := by
  have : Nonempty (PontryaginDual (Multiplicative G)) := ⟨1⟩
  have hpc : ∀ S : Set (PontryaginDual (Multiplicative G)),
      Commute (W.starProjection : H →L[ℂ] H) (projection π S) := fun S =>
    commute_starProjection_of_mapsTo W (hW S) (fun u hu => by
      rw [Submodule.mem_orthogonal'] at hu ⊢
      intro w hw
      have hself : IsSelfAdjoint (projection π S) :=
        (projection_isStarProjection π S).isSelfAdjoint
      exact (hself.isSymmetric u w).trans (hu _ (hW S w hw)))
  have hT : ∀ S : Set (PontryaginDual (Multiplicative G)),
      spectralMeasure π S * ContinuousLinearMapWOT.ofCLM (W.starProjection : H →L[ℂ] H) =
        ContinuousLinearMapWOT.ofCLM (W.starProjection : H →L[ℂ] H) * spectralMeasure π S := by
    intro S
    apply ContinuousLinearMapWOT.toCLM_injective
    rw [ContinuousLinearMapWOT.toCLM_mul, ContinuousLinearMapWOT.toCLM_mul,
      ContinuousLinearMapWOT.toCLM_ofCLM]
    exact (hpc S).symm.eq
  have hbi := WOTSpectralMeasure.boundedIntegral_commute (spectralMeasure π) hT
    (TauCeti.PontryaginDual.continuous_coe_eval_const (G := Multiplicative G) g).measurable
    ⟨1, fun χ => by simp⟩
  rw [boundedIntegral_character π g] at hbi
  have hv' : W.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have := congrArg (fun A : H →L[ℂ] H => A v) hbi
  simp only [mul_apply_eq_comp] at this
  rw [hv'] at this
  rw [this]
  exact Submodule.starProjection_apply_mem W _

/-! ## D. Sectors of definite momentum -/

/-- The linear action of a unitary representation on its Hilbert space. -/
def toEnd : Multiplicative G →* Module.End ℂ H where
  toFun g := ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H).toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [DiscreteTopology G] in
omit [BorelSpace (PontryaginDual (Multiplicative G))] in
omit [MeasurableSpace (PontryaginDual (Multiplicative G))] in
omit [TopologicalSpace G] in
lemma toEnd_apply (g : Multiplicative G) (v : H) :
    toEnd π g v = ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v := rfl

/-- The operator `π(g)` acts on the spectral projection of the single character `χ` as the scalar
`χ(g)`. -/
lemma character_mul_projection_singleton (χ : PontryaginDual (Multiplicative G))
    (g : Multiplicative G) :
    ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * projection π {χ} =
      ((χ g : Circle) : ℂ) • projection π {χ} := by
  have : Nonempty (PontryaginDual (Multiplicative G)) := ⟨1⟩
  have hsing : MeasurableSet ({χ} : Set (PontryaginDual (Multiplicative G))) :=
    measurableSet_singleton χ
  have hmeas : Measurable fun χ' : PontryaginDual (Multiplicative G) => ((χ' g : Circle) : ℂ) :=
    (TauCeti.PontryaginDual.continuous_coe_eval_const (G := Multiplicative G) g).measurable
  have hf1 : ∃ C, ∀ χ' : PontryaginDual (Multiplicative G), ‖((χ' g : Circle) : ℂ)‖ ≤ C :=
    ⟨1, fun χ' => by simp⟩
  have hf2 : ∃ C, ∀ χ' : PontryaginDual (Multiplicative G),
      ‖({χ} : Set _).indicator (fun _ => (1 : ℂ)) χ'‖ ≤ C :=
    ⟨1, fun χ' => by by_cases h : χ' ∈ ({χ} : Set _) <;> simp [h]⟩
  have hmul := WOTSpectralMeasure.boundedIntegral_mul (spectralMeasure π) hmeas
    (measurable_const.indicator hsing) hf1 hf2
  have hsmul := WOTSpectralMeasure.boundedIntegral_smul (spectralMeasure π)
    ((χ g : Circle) : ℂ) (measurable_const.indicator hsing) hf2
  have hind := WOTSpectralMeasure.boundedIntegral_indicator (spectralMeasure π) hsing
  have hchar := boundedIntegral_character π g
  have hcongr := WOTSpectralMeasure.boundedIntegral_congr (spectralMeasure π)
    (f := (fun χ' : PontryaginDual (Multiplicative G) => ((χ' g : Circle) : ℂ)) *
      ({χ} : Set _).indicator (fun _ => (1 : ℂ)))
    (g := fun χ' => ((χ g : Circle) : ℂ) * ({χ} : Set _).indicator (fun _ => (1 : ℂ)) χ')
    (hmeas.mul (measurable_const.indicator hsing))
    (measurable_const.mul (measurable_const.indicator hsing))
    (by obtain ⟨C₁, h₁⟩ := hf1; obtain ⟨C₂, h₂⟩ := hf2
        exact ⟨C₁ * C₂, fun z => by
          rw [Pi.mul_apply, norm_mul]
          exact mul_le_mul (h₁ z) (h₂ z) (norm_nonneg _) ((norm_nonneg _).trans (h₁ z))⟩)
    (by obtain ⟨C, hC⟩ := hf2
        exact ⟨‖((χ g : Circle) : ℂ)‖ * C, fun z => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)⟩)
    (fun χ' => by
      by_cases h : χ' ∈ ({χ} : Set _)
      · rw [Set.mem_singleton_iff] at h
        subst h
        simp
      · simp [h])
  have key := hmul.symm.trans (hcongr.trans hsmul)
  have h2 := congrArg ContinuousLinearMapWOT.toCLM key
  rw [ContinuousLinearMapWOT.toCLM_mul, hchar, hind] at h2
  exact h2

section Countable

variable [Countable G]

/-- A vector of momentum `χ` is carried by the single character `χ`: its spectral measure is
concentrated at `χ`. -/
lemma ae_eq_of_mem_sector (χ : PontryaginDual (Multiplicative G)) {v : H}
    (hv : v ∈ ProbabilisticTheory.Representation.sector (toEnd π) (fun g => ((χ g : Circle) : ℂ))) :
    ∀ᵐ χ' ∂vectorMeasure π v, χ' = χ := by
  have : Countable (Multiplicative G) := inferInstanceAs (Countable G)
  set ν := vectorMeasure π v
  have hall : ∀ g : Multiplicative G, ∀ᵐ χ' ∂ν, χ' g = χ g := by
    intro g
    have hI : Integrable (fun χ' : PontryaginDual (Multiplicative G) =>
        ((χ' g : Circle) : ℂ) * starRingEnd ℂ ((χ g : Circle) : ℂ)) ν :=
      (TauCeti.PontryaginDual.integrable_coe_eval (μ := ν) g).mul_const _
    have hmean : ∫ χ', ((χ' g : Circle) : ℂ) ∂ν = ((χ g : Circle) : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_eq_integral_vectorMeasure π v g]
      have h := hv g
      rw [toEnd_apply] at h
      change ⟪v, ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) v⟫_ℂ = _
      rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp
    have hmass : ν.real univ = ‖v‖ ^ 2 := by
      rw [measureReal_def, vectorMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
    have hint : ∫ χ', ‖((χ' g : Circle) : ℂ) - ((χ g : Circle) : ℂ)‖ ^ 2 ∂ν = 0 := by
      have hz : ∀ χ' : PontryaginDual (Multiplicative G), ‖((χ' g : Circle) : ℂ) -
          ((χ g : Circle) : ℂ)‖ ^ 2 = 2 - 2 * (((χ' g : Circle) : ℂ) *
            starRingEnd ℂ ((χ g : Circle) : ℂ)).re := by
        intro χ'
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
        simp [Complex.normSq_eq_norm_sq]
        ring
      have hIre : Integrable (fun χ' : PontryaginDual (Multiplicative G) =>
          (((χ' g : Circle) : ℂ) * starRingEnd ℂ ((χ g : Circle) : ℂ)).re) ν := hI.re
      have hre : ∫ χ' : PontryaginDual (Multiplicative G),
          (((χ' g : Circle) : ℂ) * starRingEnd ℂ ((χ g : Circle) : ℂ)).re ∂ν =
          (∫ χ' : PontryaginDual (Multiplicative G),
            ((χ' g : Circle) : ℂ) * starRingEnd ℂ ((χ g : Circle) : ℂ) ∂ν).re := integral_re hI
      simp_rw [hz]
      rw [integral_sub (integrable_const _) (hIre.const_mul 2), integral_const,
        integral_const_mul, hre, integral_mul_const, hmean, hmass]
      have hu : ((χ g : Circle) : ℂ) * starRingEnd ℂ ((χ g : Circle) : ℂ) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        simp
      have : ((χ g : Circle) : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ ((χ g : Circle) : ℂ) =
          ((‖v‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_right_comm, hu, one_mul]
      rw [this, Complex.ofReal_re]
      ring
    have hmeasf : Continuous fun χ' : PontryaginDual (Multiplicative G) =>
        ‖((χ' g : Circle) : ℂ) - ((χ g : Circle) : ℂ)‖ ^ 2 :=
      (((TauCeti.PontryaginDual.continuous_coe_eval_const (G := Multiplicative G) g).sub
        continuous_const).norm).pow 2
    have hint_int : Integrable (fun χ' : PontryaginDual (Multiplicative G) =>
        ‖((χ' g : Circle) : ℂ) - ((χ g : Circle) : ℂ)‖ ^ 2) ν := by
      refine Integrable.of_bound hmeasf.aestronglyMeasurable 4 (Filter.Eventually.of_forall
        fun χ' => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 := norm_sub_le ((χ' g : Circle) : ℂ) ((χ g : Circle) : ℂ)
      simp only [Circle.norm_coe] at h1
      nlinarith [norm_nonneg (((χ' g : Circle) : ℂ) - ((χ g : Circle) : ℂ))]
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint_int).mp hint
    filter_upwards [hae] with χ' hχ'
    have hz0 : ((χ' g : Circle) : ℂ) - ((χ g : Circle) : ℂ) = 0 := by
      have : ‖((χ' g : Circle) : ℂ) - ((χ g : Circle) : ℂ)‖ ^ 2 = 0 := hχ'
      exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
    exact Circle.ext (sub_eq_zero.mp hz0)
  have h := ae_all_iff.mpr hall
  filter_upwards [h] with χ' hχ'
  exact PontryaginDual.ext fun g => Circle.ext (congrArg Subtype.val (hχ' g))

/-- **A vector of momentum `χ` lies in the range of the spectral projection of `χ`.** -/
lemma projection_singleton_eq_self_of_mem_sector (χ : PontryaginDual (Multiplicative G)) {v : H}
    (hv : v ∈ ProbabilisticTheory.Representation.sector (toEnd π) (fun g => ((χ g : Circle) : ℂ))) :
    projection π {χ} v = v := by
  have hsing : MeasurableSet ({χ} : Set (PontryaginDual (Multiplicative G))) :=
    measurableSet_singleton χ
  have hae := ae_eq_of_mem_sector π χ hv
  have hc : vectorMeasure π v ({χ}ᶜ) = 0 := by
    have h0 := ae_iff.mp hae
    have hset : {a : PontryaginDual (Multiplicative G) | ¬ a = χ} = ({χ}ᶜ : Set _) := by
      ext a; simp
    rwa [hset] at h0
  have hν : vectorMeasure π v {χ} = vectorMeasure π v Set.univ := by
    have := measure_add_measure_compl (μ := vectorMeasure π v) hsing
    rw [hc, add_zero] at this
    exact this
  rw [vectorMeasure_apply π v hsing, vectorMeasure_univ] at hν
  have hnorm : ‖projection π {χ} v‖ ^ 2 = ‖v‖ ^ 2 :=
    (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp hν
  have hp := projection_isStarProjection π {χ}
  have hpp : projection π {χ} (projection π {χ} v) = projection π {χ} v := by
    have := congrArg (fun A : H →L[ℂ] H => A v) hp.isIdempotentElem.eq
    simpa using this
  have hadj : IsSelfAdjoint (projection π {χ}) := hp.isSelfAdjoint
  have hre : (⟪v, projection π {χ} v⟫_ℂ).re = ‖projection π {χ} v‖ ^ 2 := by
    have h1 : ⟪projection π {χ} v, projection π {χ} v⟫_ℂ = ⟪v, projection π {χ} v⟫_ℂ := by
      have := hadj.isSymmetric v (projection π {χ} v)
      simpa [hpp] using this
    rw [← h1, inner_self_eq_norm_sq_to_K]
    have h2 : ((((‖projection π {χ} v‖ : ℝ) : ℂ)) ^ 2).re = ‖projection π {χ} v‖ ^ 2 := by
      rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
    exact h2
  have hsub : ‖v - projection π {χ} v‖ ^ 2 = 0 := by
    have e : RCLike.re ⟪v, projection π {χ} v⟫_ℂ = ‖projection π {χ} v‖ ^ 2 := hre
    rw [@norm_sub_sq ℂ, e, hnorm]
    ring
  have := norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hsub)
  exact (sub_eq_zero.mp this).symm

/-- **The spectral projection of a single character is the projection onto the sector of
definite momentum**: its range is the subspace of vectors on which the group acts through the
character. -/
lemma range_projection_singleton (χ : PontryaginDual (Multiplicative G)) :
    LinearMap.range (projection π {χ} : H →L[ℂ] H).toLinearMap =
      ProbabilisticTheory.Representation.sector (toEnd π) (fun g => ((χ g : Circle) : ℂ)) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩ g
    have h := congrArg (fun A : H →L[ℂ] H => A w) (character_mul_projection_singleton π χ g)
    simpa [toEnd_apply] using h
  · intro hv
    exact ⟨v, projection_singleton_eq_self_of_mem_sector π χ hv⟩

end Countable

end UnitaryRep

end QuantumMechanics

end ProbabilisticTheory

end
