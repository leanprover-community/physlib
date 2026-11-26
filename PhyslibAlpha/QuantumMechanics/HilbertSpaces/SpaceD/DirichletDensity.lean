/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.DirichletSubmodule
/-!

# Density of the Dirichlet submodule

## i. Overview

Homogeneous Dirichlet boundary conditions say that the wavefunction vanishes on the boundary of
a region `Ω`, as for a particle confined to `Ω` by infinitely high walls (the particle in a box).
The Dirichlet submodule `DirichletSubmoduleOn Ω μ` of `SpaceDHilbertSpaceOn Ω μ`, defined in
`Physlib/QuantumMechanics/HilbertSpaces/SpaceD/DirichletSubmodule.lean`, consists of the classes
of Schwartz maps which vanish on `frontier Ω`. It serves as a domain for operators acting on such
wavefunctions, and a domain must be dense for the adjoint of an operator to be well defined.

In this module we show that, for a measure `μ` finite on compact sets, the Dirichlet submodule is
dense exactly when the frontier of `Ω` is null for `μ.restrict Ω`, for instance when `Ω` is open.
This answers the TODO on density in `DirichletSubmodule.lean`.

## ii. Key results

- `SpaceDHilbertSpaceOn.subspaceProjection_schwartzIncl_coe_ae`: The class in
  `SpaceDHilbertSpaceOn Ω μ` of a Schwartz map agrees with it `μ.restrict Ω`-almost everywhere.
- `DirichletSubmoduleOn.dense`: For a measure finite on compact sets, the Dirichlet submodule is
  dense in `SpaceDHilbertSpaceOn Ω μ` when the frontier of `Ω` is null for `μ.restrict Ω`.
- `DirichletSubmoduleOn.dense_of_isOpen`: In particular it is dense when `Ω` is open.
- `DirichletSubmoduleOn.indicatorConstLp_mem_orthogonal`: The indicator function of a part of the
  frontier is orthogonal to the Dirichlet submodule.
- `DirichletSubmoduleOn.dense_iff`: For such a measure the condition on the frontier is also
  necessary.

## iii. Table of contents

- A. Classes of Schwartz maps
- B. Density when the frontier is null
- C. Necessity of a null frontier

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
## A. Classes of Schwartz maps
-/

/-- The class in `SpaceDHilbertSpaceOn Ω μ` of a Schwartz map `f`, obtained by including `f` in
  `SpaceDHilbertSpace d μ` and projecting onto `Ω`, agrees with `f` `μ.restrict Ω`-almost
  everywhere. The projection only forgets the values of `f` outside `Ω`. -/
lemma subspaceProjection_schwartzIncl_coe_ae (f : 𝓢(Space d, ℂ)) :
    subspaceProjection Ω μ (schwartzIncl μ f) =ᵐ[μ.restrict Ω] f :=
  (subspaceProjection_apply Ω _).trans ((coeFn_toLp f 2 μ).filter_mono ae_restrict_le)

namespace DirichletSubmoduleOn

/-!
## B. Density when the frontier is null
-/

/-- For a measure `μ` finite on compact sets, the Dirichlet submodule is dense in
  `SpaceDHilbertSpaceOn Ω μ` when the frontier of `Ω` is null for `μ.restrict Ω`, that is when
  `μ (frontier Ω ∩ Ω) = 0`, for instance when `μ (frontier Ω) = 0`. No measurability of `Ω` is
  assumed.

  An element orthogonal to the Dirichlet submodule integrates to zero against every smooth
  function with compact support in `interior Ω`, since such a function vanishes on the frontier.
  So it vanishes almost everywhere on `interior Ω`, which has full measure because the frontier
  is null. The measure being finite on compact sets makes square-integrable functions locally
  integrable, which this argument needs. -/
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
  -- The frontier is null, so almost every point of `Ω` is an interior point
  have hΩ : ∀ᵐ x ∂μ.restrict Ω, x ∈ interior Ω := by
    rw [Measure.restrict_apply isClosed_frontier.measurableSet] at h
    refine ae_iff.mpr ((Measure.restrict_apply isOpen_interior.measurableSet.compl).trans ?_)
    refine measure_mono_null (fun x hx ↦ ?_) h
    exact ⟨(mem_frontier_iff_notMem_interior hx.2).mpr hx.1, hx.2⟩
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hint, hΩ] with x h1 h2
  exact h1 h2

/-- For an open set `Ω` and a measure `μ` finite on compact sets, the Dirichlet submodule is
  dense in `SpaceDHilbertSpaceOn Ω μ`, whatever the measure does on the frontier, since an
  open set does not meet its frontier. -/
lemma dense_of_isOpen [IsFiniteMeasureOnCompacts μ] (hΩ : IsOpen Ω) :
    Dense (DirichletSubmoduleOn Ω μ : Set (SpaceDHilbertSpaceOn Ω μ)) := by
  refine dense Ω μ ?_
  rw [Measure.restrict_apply isClosed_frontier.measurableSet, Set.inter_comm,
    hΩ.inter_frontier_eq, measure_empty]

/-!
## C. Necessity of a null frontier
-/

/-- The indicator function of a measurable subset `S` of `frontier Ω`, of finite measure for
  `μ.restrict Ω`, is orthogonal to the Dirichlet submodule, since Dirichlet Schwartz maps vanish
  on the frontier. So a state concentrated on the boundary of `Ω` is orthogonal to every state
  satisfying Dirichlet boundary conditions. For `c ≠ 0` this state is nonzero exactly when
  `S ∩ Ω` has positive measure, and then it cannot be approximated by Dirichlet states. -/
lemma indicatorConstLp_mem_orthogonal {S : Set (Space d)} (hS : MeasurableSet S)
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
  nonzero element orthogonal to the Dirichlet submodule. For instance, for `Ω = {0}` in `Space 1`
  and the Dirac measure at `0`, the frontier of `Ω` is `Ω` itself. Every Dirichlet Schwartz map
  vanishes on `Ω`, so the Dirichlet submodule is zero while the Hilbert space is not. -/
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
