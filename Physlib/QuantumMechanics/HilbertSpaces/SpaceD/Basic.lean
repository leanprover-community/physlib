/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Gregory J. Loges
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Physlib.SpaceAndTime.Space.Module
/-!

# Hilbert spaces for quantum mechanics on `Space d`

## i. Overview

The Hilbert spaces appropriate for doing quantum mechanics on `Space d` are the $L^2$-spaces
`SpaceDHilbertSpace d μ := Lp ℂ 2 μ`, where `μ` is some measure on `Space d`.
Elements of `SpaceDHilbertSpace d μ` are _equivalence classes_ of functions `Space d → ℂ` which are
square-integrable with respect to `μ`, i.e. `∫ x, ‖f x‖ ^ 2 ∂μ` is finite, and where `f` and `g` are
in the same equivalence class if they are `μ`-a.e. equal.

The ability of a function to be interpreted as an element of `SpaceDHilbertSpace d μ` is captured
by the property `MemHS`. If one has `hf : MemHS f μ` for a function `f : Space d → ℂ` this means
that `f` is `μ`-a.e. strongly measurable and square-integrable; `mk hf` constructs the corresponding
equivalence class of `f` in `SpaceDHilbertSpace d μ`.

Given `SpaceDHilbertSpace d μ` and `Ω : Set (Space d)`, the Hilbert space
`SpaceDHilbertSpaceOn Ω μ ≔ SpaceDHilbertSpace d (μ.restrict Ω)` may be interpreted as the
sub-Hilbert space consisting of those vectors with domain contained in `Ω`.
The reason is that for each `ψ` in `SpaceDHilbertSpaceOn Ω μ` we have
`ψ =ᵐ[μ.restrict Ω] Ω.indicator ψ`, namely the equivalence class of `ψ` always
contains a representative which vanishes on the complement of `Ω`.
The linear isometry `restrictIncl Ω μ` describes this sub-Hilbert space relationship
by mapping each `ψ` to this special representative in its equivalence class.
Similarly, we may project `SpaceDHilbertSpace d μ` onto `SpaceDHilbertSpaceOn Ω μ` by enlarging the
equivalence classes, essentially dropping information about the functions on the complement of `Ω`.

## ii. Key results

- `SpaceDHilbertSpace d μ` : The $L^2$-space on `Space d` with respect to the measure `μ`.
- `toBra` : The linear equivalence between the Hilbert space and its dual. This is the map which
    sends each ket to its corresponding bra and _vice versa_.
- `MemHS f μ` : The proposition capturing exactly when a function `f : Space d → ℂ` can be lifted
    to an element of the Hilbert space.
- `SpaceDHilbertSpaceOn Ω μ` : An abbreviation for the Hilbert space
    `SpaceDHilbertSpace d (μ.restrict Ω)` appropriate for describing the $L^2$-space of complex
    functions on a subset of `Space d`.
- `subspaceProjection` : The projection of `SpaceDHilbertSpace d μ` onto `SpaceDHilbertSpaceOn Ω μ`.
- `subspaceIncl` : The linear isometry including `SpaceDHilbertSpaceOn Ω μ`
    as a sub-Hilbert space of `SpaceDHilbertspace d μ`.

## iii. Table of contents

- A. SpaceDHilbertSpace
  - A.1. Dual space
  - A.2. Membership
  - A.3. Construction of elements
  - A.4. Coersions
  - A.5. Misc.
- B. SpaceDHilbertSpaceOn

## iv. References

* None.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics

open Function InnerProductSpace MeasureTheory Measure Set
open scoped SchwartzMap

/-!
## A. SpaceDHilbertSpace
-/

/-- The L²-space of `μ`-a.e. equal equivalence classes of functions `f : Space d → ℂ`
  for which `∫ x, ‖f x‖² ∂μ` is finite. -/
abbrev SpaceDHilbertSpace (d : ℕ) (μ : Measure (Space d) := volume) := Lp ℂ 2 μ

namespace SpaceDHilbertSpace

variable {d : ℕ} {μ μ' : Measure (Space d)} {f g : Space d → ℂ} (ψ φ : SpaceDHilbertSpace d μ)

variable {ψ φ} in
/-- Elements of `SpaceDHilbertSpace d μ` are equivalence classes
  of `μ`-a.e. equal functions `Space d → ℂ`. -/
lemma ext_iff : ψ = φ ↔ ψ =ᵐ[μ] φ := Lp.ext_iff

/-!
### A.1. Dual space
-/

/-- The anti-linear equivalence between `SpaceDHilbertSpace d μ` and its dual.

  This is the map that takes a ket to its corresponding bra and _vice versa_. -/
def toBra : SpaceDHilbertSpace d μ ≃ₛₗ[starRingEnd ℂ] StrongDual ℂ (SpaceDHilbertSpace d μ) :=
  toDual ℂ (SpaceDHilbertSpace d μ)

@[simp]
lemma toBra_apply_apply : toBra ψ φ = ⟪ψ, φ⟫_ℂ := rfl

@[simp]
lemma toBra_symm_apply (f : StrongDual ℂ (SpaceDHilbertSpace d μ)) : ⟪toBra.symm f, ψ⟫_ℂ = f ψ :=
  toDual_symm_apply

/-!
### A.2. Membership
-/

/-- For a function `f : Space d → ℂ`, the proposition `MemHS f μ` means that the function `f`
  can be lifted to an element of the Hilbert space. -/
def MemHS (f : Space d → ℂ) (μ : Measure (Space d) := volume) : Prop := MemLp f 2 μ

/-- Elements of the Hilbert space satisfy the property `MemHS`. -/
lemma memHS_coe : MemHS ψ μ := Lp.memLp ψ

/-- A function `f : Space d → ℂ` satisfies `MemHS f μ` if and only if
  it is `μ`-a.e. strongly measurable and `∫ x, ‖f x‖ ^ 2 ∂μ` is finite. -/
lemma memHS_iff : MemHS f μ ↔ AEStronglyMeasurable f μ ∧ Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
  ⟨fun h ↦ ⟨h.aestronglyMeasurable,
      (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h⟩,
    fun h ↦ (memLp_two_iff_integrable_sq_norm h.1).mpr h.2⟩

lemma mem_iff {f : Space d →ₘ[μ] ℂ} : f ∈ SpaceDHilbertSpace d μ ↔ MemHS f μ := Lp.mem_Lp_iff_memLp

@[simp]
lemma MemHS.zero : MemHS (0 : Space d → ℂ) μ := MemLp.zero

lemma MemHS.neg (hf : MemHS f μ) : MemHS (-f) μ := MemLp.neg hf

lemma memHS_neg_iff : MemHS (-f) μ ↔ MemHS f μ := memLp_neg_iff

lemma MemHS.add (hf : MemHS f μ) (hg : MemHS g μ) : MemHS (f + g) μ := MemLp.add hf hg

lemma MemHS.sub (hf : MemHS f μ) (hg : MemHS g μ) : MemHS (f - g) μ := MemLp.sub hf hg

lemma MemHS.const_smul (c : ℂ) (hf : MemHS f μ) : MemHS (c • f) μ := MemLp.const_smul hf c

lemma memHS_const_smul_iff {c : ℂ} (hc : c ≠ 0) : MemHS (c • f) μ ↔ MemHS f μ :=
  ⟨fun h ↦ inv_smul_smul₀ hc f ▸ h.const_smul c⁻¹, MemHS.const_smul c⟩

lemma MemHS.ae_eq (hfg : f =ᵐ[μ] g) (hf : MemHS f μ) : MemHS g μ := MemLp.ae_eq hfg hf

lemma memHS_congr_ae (hfg : f =ᵐ[μ] g) : MemHS f μ ↔ MemHS g μ := memLp_congr_ae hfg

lemma MemHS.congr_norm
    (hf : MemHS f μ) (hg : AEStronglyMeasurable g μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) : MemHS g μ :=
  MemLp.congr_norm hf hg hfg

lemma memHS_congr_norm (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) : MemHS f μ ↔ MemHS g μ :=
  memLp_congr_norm hf hg hfg

lemma MemHS.mono (hf : MemHS f μ) (hg : AEStronglyMeasurable g μ) (hfg : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    MemHS g μ :=
  MemLp.mono hf hg hfg

lemma MemHS.mono_measure (h : μ' ≤ μ) (hf : MemHS f μ) : MemHS f μ' := MemLp.mono_measure h hf

lemma MemHS.restrict (Ω : Set (Space d)) (hf : MemHS f μ) : MemHS f (μ.restrict Ω) :=
  hf.mono_measure restrict_le_self

lemma MemHS.mono_restrict {Ω Ω' : Set (Space d)} (h : Ω' ≤ Ω) (hf : MemHS f (μ.restrict Ω)) :
    MemHS f (μ.restrict Ω') :=
  hf.mono_measure (μ.restrict_mono_set h)

lemma MemHS.indicator {Ω : Set (Space d)} (hΩ : MeasurableSet Ω) (hf : MemHS f μ) :
    MemHS (Ω.indicator f) μ :=
  MemLp.indicator hΩ hf

/-- If `f` is a member of the Hilbert space with measure restricted to `Ω` then the representative
  `Ω.indicator f` which vanishes outside `Ω` is a member of `SpaceDHilbertSpace d μ`. -/
lemma MemHS.indicator_of_restrict
    {Ω : Set (Space d)} (hΩ : MeasurableSet Ω) (hf : MemHS f (μ.restrict Ω)) :
    MemHS (Ω.indicator f) μ := by
  refine memHS_iff.mpr ⟨(aestronglyMeasurable_indicator_iff hΩ).mpr hf.aestronglyMeasurable, ?_⟩
  refine (IntegrableOn.integrable_indicator (memHS_iff.mp hf).2 hΩ).congr ?_
  filter_upwards with x
  by_cases x ∈ Ω <;> simp_all

/-!
### A.3. Construction of elements
-/

section

variable (hf : MemHS f μ) (hg : MemHS g μ)

/-- Given a function `f : Space d → ℂ` such that `MemHS f μ` is true via `hf`,
  `mk hf` is the element of the Hilbert space defined by `f`. -/
def mk : SpaceDHilbertSpace d μ :=
  ⟨AEEqFun.mk f hf.aestronglyMeasurable,
    mem_iff.mpr <| hf.ae_eq (AEEqFun.coeFn_mk f hf.aestronglyMeasurable).symm⟩

@[simp]
lemma mk_neg : mk hf.neg = -mk hf := rfl

@[simp]
lemma mk_add : mk (hf.add hg) = mk hf + mk hg := rfl

@[simp]
lemma mk_sub : mk (hf.sub hg) = mk hf - mk hg := rfl

@[simp]
lemma mk_const_smul (c : ℂ) : mk (hf.const_smul c) = c • mk hf := rfl

lemma mk_eq_iff : mk hf = mk hg ↔ f =ᵐ[μ] g := by simp [mk]

lemma mk_surjective : ∃ (f : Space d → ℂ) (hf : MemHS f μ), mk hf = ψ :=
  ⟨ψ, memHS_coe ψ, by simp [mk]⟩

lemma coeFn_mk : mk hf =ᵐ[μ] f := AEEqFun.coeFn_mk f hf.aestronglyMeasurable

lemma inner_mk_mk : ⟪mk hf, mk hg⟫_ℂ = ∫ x, starRingEnd ℂ (f x) * g x ∂μ := by
  apply integral_congr_ae
  filter_upwards [coeFn_mk hf, coeFn_mk hg]
  simp_all [mul_comm]

end

/-!
### A.4. Coersions
-/

section

variable (c : ℂ) (ψ φ : SpaceDHilbertSpace d μ)

lemma coeFn_zero : ⇑(0 : SpaceDHilbertSpace d μ) =ᵐ[μ] 0 := Lp.coeFn_zero _ _ _

lemma coeFn_neg : ⇑(-ψ) =ᵐ[μ] -ψ := Lp.coeFn_neg _

lemma coeFn_add : ⇑(ψ.val + φ.val) =ᵐ[μ] ψ + φ := Lp.coeFn_add _ _

lemma coeFn_sub : ⇑(ψ.val - φ.val) =ᵐ[μ] ψ - φ := Lp.coeFn_sub _ _

lemma coeFn_smul : ⇑(c • ψ) =ᵐ[μ] c • ψ := Lp.coeFn_smul _ _

end

/-!
### A.5. Misc.
-/

/-- The tempered distribution associated to a state. -/
abbrev toTemperedDistribution [μ.HasTemperateGrowth]
    (ψ : SpaceDHilbertSpace d μ) : 𝓢'(Space d, ℂ) := Lp.toTemperedDistribution ψ

/-- The embedding of states into tempered distributions as a continuous linear map. -/
abbrev toTemperedDistributionCLM (d : ℕ) (μ : Measure (Space d) := volume)
    [μ.HasTemperateGrowth] : SpaceDHilbertSpace d μ →L[ℂ] 𝓢'(Space d, ℂ) :=
  Lp.toTemperedDistributionCLM ℂ μ 2

open Filter in
lemma tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq
    {α : Type*} {l : Filter α} {ψ : α → SpaceDHilbertSpace d μ} :
    Tendsto ψ l (nhds 0) ↔ Tendsto (fun a ↦ ∫⁻ x, ‖ψ a x‖ₑ ^ 2 ∂μ) l (nhds 0) := by
  trans Tendsto (fun a ↦ (∫⁻ x, ‖ψ a x‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)) l (nhds 0)
  · simp [tendsto_iff_edist_tendsto_0, edist_zero_right, Lp.enorm_def, eLpNorm, eLpNorm',
      Lp.aestronglyMeasurable]
  constructor <;> intro h
  · apply Tendsto.ennrpow_const 2 at h
    simp_all [← ENNReal.rpow_mul_natCast]
  · apply Tendsto.ennrpow_const 2⁻¹ at h
    simp_all

end SpaceDHilbertSpace

/-!
## B. SpaceDHilbertSpaceOn
-/

TODO "Upgrade subspaceProjection to a ContinuousLinearMap when Lp.LpToLpOfMeasureLeSMul
  becomes available."

/-- The L²-space `SpaceDHilbertSpace d (μ.restrict Ω)`.

  Elements are equivalence classes of functions which agree `μ`-a.e. on `Ω` and which have
  `∫ x in Ω, ‖f x‖ ^ 2 ∂μ` finite. -/
abbrev SpaceDHilbertSpaceOn {d : ℕ} (Ω : Set (Space d)) (μ : Measure (Space d) := volume) :=
  SpaceDHilbertSpace d (μ.restrict Ω)

namespace SpaceDHilbertSpaceOn

open SpaceDHilbertSpace

variable {d : ℕ} (Ω : Set (Space d)) (hΩ : MeasurableSet Ω) (μ : Measure (Space d))
variable (ψ : SpaceDHilbertSpace d μ) (φ : SpaceDHilbertSpaceOn Ω μ)

/-- The linear map projecting `SpaceDHilbertSpace d μ` onto `SpaceDHilbertSpaceOn Ω μ`. -/
def subspaceProjection : SpaceDHilbertSpace d μ →ₗ[ℂ] SpaceDHilbertSpaceOn Ω μ where
  toFun ψ := mk ((memHS_coe ψ).restrict Ω)
  map_add' ψ φ := by
    rw [← mk_add, mk_eq_iff]
    exact (coeFn_add ψ φ).filter_mono ae_restrict_le
  map_smul' c ψ := by
    rw [← mk_const_smul, mk_eq_iff]
    exact (coeFn_smul c ψ).filter_mono ae_restrict_le

variable {μ} in
lemma subspaceProjection_apply : subspaceProjection Ω μ ψ =ᵐ[μ.restrict Ω] ψ :=
  coeFn_mk ((memHS_coe ψ).restrict Ω)

lemma subspaceProjection_norm_le : ‖subspaceProjection Ω μ ψ‖ ≤ ‖ψ‖ := by
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top ψ) ?_
  refine (eLpNorm_congr_ae (subspaceProjection_apply Ω ψ)).trans_le ?_
  exact eLpNorm_mono_measure ψ restrict_le_self

variable {Ω}

/-- The linear isometry including `SpaceDHilbertSpaceOn Ω μ` as a sub-Hilbert space of
  `SpaceDHilbertSpace d μ`, defined by mapping `ψ` to `Ω.indicator ψ`. -/
def subspaceIncl : SpaceDHilbertSpaceOn Ω μ →ₗᵢ[ℂ] SpaceDHilbertSpace d μ where
  toFun ψ := mk ((memHS_coe ψ).indicator_of_restrict hΩ)
  map_add' ψ φ := by
    rw [← mk_add, mk_eq_iff, ← indicator_add']
    exact (ae_eq_restrict_iff_indicator_ae_eq hΩ).mp (coeFn_add ψ φ)
  map_smul' c ψ := by
    rw [← mk_const_smul, mk_eq_iff, Pi.smul_def, ← indicator_const_smul]
    exact (ae_eq_restrict_iff_indicator_ae_eq hΩ).mp (coeFn_smul c ψ)
  norm_map' ψ := by
    calc
      _ = (eLpNorm (mk ((memHS_coe ψ).indicator_of_restrict hΩ)) 2 μ).toReal := rfl
      _ = (eLpNorm (Ω.indicator ψ) 2 μ).toReal := congrArg _ (eLpNorm_congr_ae (coeFn_mk _))
      _ = ‖ψ‖ := congrArg _ (eLpNorm_indicator_eq_eLpNorm_restrict hΩ)

variable {μ} in
lemma subspaceIncl_apply : subspaceIncl hΩ μ φ =ᵐ[μ] Ω.indicator φ :=
  coeFn_mk ((memHS_coe φ).indicator_of_restrict hΩ)

lemma leftInverse_subspaceProjection :
    LeftInverse (subspaceProjection Ω μ) (subspaceIncl hΩ μ) := by
  intro ψ
  apply ext_iff.mpr
  have h := subspaceProjection_apply Ω (subspaceIncl hΩ μ ψ)
  rw [ae_eq_restrict_iff_indicator_ae_eq hΩ] at *
  filter_upwards [subspaceIncl_apply hΩ ψ, h] with x
  by_cases x ∈ Ω <;> simp_all

@[simp]
lemma subspaceProjection_subspaceIncl_apply : subspaceProjection Ω μ (subspaceIncl hΩ μ φ) = φ :=
  leftInverse_subspaceProjection hΩ μ φ

include hΩ in
lemma subspaceProjection_surjective : Surjective (subspaceProjection Ω μ) :=
  (leftInverse_subspaceProjection hΩ μ).surjective

end SpaceDHilbertSpaceOn

end QuantumMechanics
end
