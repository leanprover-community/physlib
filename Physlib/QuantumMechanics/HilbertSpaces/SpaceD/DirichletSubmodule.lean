/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# Dirichlet submodule

## i. Overview

In this module we define the Dirichlet submodule of `SpaceDHilbertSpaceOn Ω μ` consisting of
equivalence classes of Schwartz maps which vanish on `frontier Ω`. The frontier (or boundary)
of a set `Ω` contains all points whose neighborhoods always intersect with both `Ω` and `Ωᶜ`.

These serve as a convenient dense domain for operators acting on wavefunctions satisfying
homogeneous Dirichlet boundary conditions on `Ω`. For a measure `μ` finite on compact sets, the
Dirichlet submodule is dense exactly when the frontier of `Ω` is null for `μ.restrict Ω`, for
instance when `Ω` is open.

## ii. Key results

- `DirichletSubmoduleOn Ω μ`: The subspace of `SchwartzSubmodule d μ` consisting of Schwartz maps
  which vanish on the frontier of `Ω`.
- `DirichletSubmoduleOn.dense`: For a measure finite on compact sets, the Dirichlet submodule is
  dense in `SpaceDHilbertSpaceOn Ω μ` when the frontier of `Ω` is null for `μ.restrict Ω`.
- `DirichletSubmoduleOn.dense_iff`: For such a measure this condition is also necessary.

## iii. Table of contents

- A. Definitions
- B. Contained in SchwartzSubmoduleOn
- C. Density
  - C.1. Density when the frontier is null
  - C.2. Necessity of a null frontier

## iv. References

* None.
-/

@[expose] public section

noncomputable section
namespace QuantumMechanics
namespace SpaceDHilbertSpaceOn

open MeasureTheory SchwartzMap SpaceDHilbertSpace

variable {d : ℕ} (Ω : Set (Space d)) (μ : Measure (Space d)) [μ.HasTemperateGrowth]

/-!
## A. Definitions
-/

/-- The Schwartz maps which vanish on `frontier Ω`. -/
def DirichletSchwartzMap : Submodule ℂ 𝓢(Space d, ℂ) where
  carrier := {f : 𝓢(Space d, ℂ) | ∀ x : frontier Ω, f x = 0}
  add_mem' := by simp_all
  zero_mem' := by simp
  smul_mem' := by simp_all

/-- The submodule of the Hilbert space on `Ω` consisting of the equivalence classes
  of Schwartz maps which vanish on `frontier Ω`. -/
abbrev DirichletSubmoduleOn : Submodule ℂ (SpaceDHilbertSpaceOn Ω μ) :=
  (DirichletSchwartzMap Ω).map (subspaceProjection Ω μ ∘L schwartzIncl μ).toLinearMap

namespace DirichletSubmoduleOn

variable {Ω μ} in
lemma mem_iff {ψ : SpaceDHilbertSpaceOn Ω μ} :
    ψ ∈ DirichletSubmoduleOn Ω μ ↔
      ∃ f : DirichletSchwartzMap Ω, subspaceProjection Ω μ (schwartzIncl μ f) = ψ := by
  simp

/-!
## B. Contained in SchwartzSubmoduleOn
-/

lemma le_schwartzSubmoduleOn : DirichletSubmoduleOn Ω μ ≤ SchwartzSubmoduleOn Ω μ := by
  intro ψ hψ
  obtain ⟨f, hf⟩ := mem_iff.mp hψ
  apply SchwartzSubmoduleOn.mem_iff.mpr ⟨⟨schwartzIncl μ f, by simp⟩, hf⟩

/-!
## C. Density
-/

/-!
### C.1. Density when the frontier is null
-/

/-- The class in `SpaceDHilbertSpaceOn Ω μ` of a Schwartz map `f` agrees with `f`
  `μ.restrict Ω`-almost everywhere. -/
private lemma subspaceProjection_schwartzIncl_coe_ae (f : 𝓢(Space d, ℂ)) :
    subspaceProjection Ω μ (schwartzIncl μ f) =ᵐ[μ.restrict Ω] f :=
  (subspaceProjection_apply Ω _).trans ((coeFn_toLp f 2 μ).filter_mono ae_restrict_le)

omit [μ.HasTemperateGrowth] in
/-- If the frontier of `Ω` is null for `μ.restrict Ω`, then `μ.restrict Ω`-almost every point
  is an interior point of `Ω`. -/
private lemma ae_mem_interior (h : μ.restrict Ω (frontier Ω) = 0) :
    ∀ᵐ x ∂μ.restrict Ω, x ∈ interior Ω := by
  rw [Measure.restrict_apply isClosed_frontier.measurableSet] at h
  have h0 : μ.restrict Ω (interior Ω)ᶜ = 0 := by
    rw [Measure.restrict_apply isOpen_interior.measurableSet.compl]
    refine measure_mono_null (fun x hx ↦ ?_) h
    exact ⟨(mem_frontier_iff_notMem_interior hx.2).mpr hx.1, hx.2⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
  simpa using hx

/-- For a measure `μ` finite on compact sets, the Dirichlet submodule is dense in
  `SpaceDHilbertSpaceOn Ω μ` when the frontier of `Ω` is null for `μ.restrict Ω`, for instance
  when `μ (frontier Ω) = 0`.

  An element orthogonal to the Dirichlet submodule integrates to zero against every smooth
  compactly supported function with support in `interior Ω`, so it vanishes almost everywhere
  on `interior Ω`, which has full measure. -/
lemma dense [IsFiniteMeasureOnCompacts μ] (h : μ.restrict Ω (frontier Ω) = 0) :
    Dense (DirichletSubmoduleOn Ω μ : Set (SpaceDHilbertSpaceOn Ω μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro φ hφ
  have hint : ∀ᵐ x ∂μ.restrict Ω, x ∈ interior Ω → φ x = 0 := by
    refine isOpen_interior.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((Lp.memLp φ).locallyIntegrable one_le_two).locallyIntegrableOn _) ?_
    intro g g_smooth g_cpt g_supp
    -- `g` as a complex Schwartz map which vanishes on `frontier Ω`
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ := Complex.ofRealCLM.contDiff.comp g_smooth
    have hG : hg₁.toSchwartzMap hg₂ ∈ DirichletSchwartzMap Ω := by
      show ∀ x : frontier Ω, hg₁.toSchwartzMap hg₂ x = 0
      intro x
      have hx : (x : Space d) ∉ tsupport g := fun hx ↦ x.2.2 (g_supp hx)
      simp [image_eq_zero_of_notMem_tsupport hx]
    have h0 := (Submodule.mem_orthogonal _ _).mp hφ _ (mem_iff.mpr ⟨⟨_, hG⟩, rfl⟩)
    rw [L2.inner_def] at h0
    refine (integral_congr_ae ?_).trans h0
    filter_upwards [subspaceProjection_schwartzIncl_coe_ae Ω μ (hg₁.toSchwartzMap hg₂)]
      with x hx
    rw [hx]
    simp [Complex.real_smul, mul_comm]
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hint, ae_mem_interior Ω μ h] with x h1 h2
  exact h1 h2

/-- For an open set `Ω` and a measure `μ` finite on compact sets, the Dirichlet submodule is
  dense in `SpaceDHilbertSpaceOn Ω μ`, whatever the measure does on the frontier. -/
lemma dense_of_isOpen [IsFiniteMeasureOnCompacts μ] (hΩ : IsOpen Ω) :
    Dense (DirichletSubmoduleOn Ω μ : Set (SpaceDHilbertSpaceOn Ω μ)) := by
  refine dense Ω μ ?_
  rw [Measure.restrict_apply isClosed_frontier.measurableSet, Set.inter_comm,
    hΩ.inter_frontier_eq, measure_empty]

/-!
### C.2. Necessity of a null frontier
-/

/-- The indicator function of a measurable subset `S` of `frontier Ω` of finite measure is
  orthogonal to the Dirichlet submodule. -/
private lemma indicatorConstLp_mem_orthogonal {S : Set (Space d)} (hS : MeasurableSet S)
    (hSfin : μ.restrict Ω S ≠ ⊤) (hSF : S ⊆ frontier Ω) (c : ℂ) :
    indicatorConstLp 2 hS hSfin c ∈ (DirichletSubmoduleOn Ω μ)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨f, rfl⟩ := mem_iff.mp hu
  have hf : ∀ y : frontier Ω, (f : 𝓢(Space d, ℂ)) y = 0 := f.2
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [subspaceProjection_schwartzIncl_coe_ae Ω μ f,
    indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hSfin) (c := c)] with x hx1 hx2
  by_cases hxS : x ∈ S
  · rw [hx1, hf ⟨x, hSF hxS⟩]
    simp
  · rw [hx2, Set.indicator_of_notMem hxS]
    simp

/-- For a measure `μ` finite on compact sets, the Dirichlet submodule is dense in
  `SpaceDHilbertSpaceOn Ω μ` if and only if the frontier of `Ω` is null for `μ.restrict Ω`.

  If a compact piece of the frontier had positive measure, its indicator function would be a
  nonzero element orthogonal to the Dirichlet submodule. -/
lemma dense_iff [IsFiniteMeasureOnCompacts μ] :
    Dense (DirichletSubmoduleOn Ω μ : Set (SpaceDHilbertSpaceOn Ω μ)) ↔
      μ.restrict Ω (frontier Ω) = 0 := by
  refine ⟨fun hD ↦ ?_, dense Ω μ⟩
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff] at hD
  -- Cover the frontier by the compact pieces `frontier Ω ∩ closedBall 0 n`
  rw [← Set.inter_univ (frontier Ω), ← Metric.iUnion_closedBall_nat (0 : Space d),
    Set.inter_iUnion, measure_iUnion_null_iff]
  intro n
  by_contra hn
  have hS : MeasurableSet (frontier Ω ∩ Metric.closedBall (0 : Space d) n) :=
    isClosed_frontier.measurableSet.inter Metric.isClosed_closedBall.measurableSet
  have hSfin : μ.restrict Ω (frontier Ω ∩ Metric.closedBall (0 : Space d) n) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_right).trans_lt
      (isCompact_closedBall (0 : Space d) (n : ℝ)).measure_lt_top).ne
  -- A piece of positive measure has a nonzero indicator function, orthogonal to the submodule
  have hpos : 0 < ‖indicatorConstLp 2 hS hSfin (1 : ℂ)‖ := by
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul,
      measureReal_def]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hn hSfin) _
  rw [hD _ (indicatorConstLp_mem_orthogonal Ω μ hS hSfin Set.inter_subset_left 1),
    norm_zero] at hpos
  exact lt_irrefl _ hpos

end DirichletSubmoduleOn
end SpaceDHilbertSpaceOn
end QuantumMechanics
end
