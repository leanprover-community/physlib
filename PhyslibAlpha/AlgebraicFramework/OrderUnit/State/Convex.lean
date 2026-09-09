/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.UnitInterval

/-!

# Convex state spaces

## i. Overview

Mixtures of complex-valued states on ordered complex vector spaces with a distinguished unit.
No multiplication, star operation, norm, topology, completeness, or C⋆ structure is required.

## ii. Key definitions and results

- `UnitalPositiveLinearMap.finiteMix`: a finite convex mixture of states.
- `UnitalPositiveLinearMap.mix`: a binary mixture.
- `UnitalPositiveLinearMap.stateSpace`: states embedded in the algebraic dual.
- `UnitalPositiveLinearMap.stateSpace_convex`: convexity of the state space.

## iii. Table of contents

- A. Finite mixtures
- B. Binary mixtures
- C. The state space in the algebraic dual

-/

@[expose] public section

open scoped ComplexOrder

namespace UnitalPositiveLinearMap

variable {A : Type*} [AddCommGroup A] [PartialOrder A] [IsOrderedAddMonoid A]
  [Module ℂ A] [One A]

/-! ## A. Finite mixtures -/

/-- The state obtained from a finite family using probability weights `p`. -/
noncomputable def finiteMix {ι : Type*} [Fintype ι] (ω : ι → 𝓢[A])
    (p : stdSimplex ℝ ι) : 𝓢[A] :=
  ofLinearMap (R := ℂ) (E₁ := A) (E₂ := ℂ)
    (∑ i, (p i : ℂ) • (ω i).toLinearMap)
    (fun a ha => by
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (RCLike.ofReal_nonneg.mpr (stdSimplex.zero_le p i)) ((ω i).map_nonneg ha))
    (by
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      have hone (i : ι) : (ω i).toLinearMap (1 : A) = 1 := (ω i).map_one
      simp_rw [hone, mul_one]
      exact_mod_cast stdSimplex.sum_eq_one p)

/-- Evaluation of a finite mixture is its pointwise weighted sum. -/
@[simp]
lemma finiteMix_apply {ι : Type*} [Fintype ι] (ω : ι → 𝓢[A])
    (p : stdSimplex ℝ ι) (a : A) :
    finiteMix ω p a = ∑ i, (p i : ℂ) * ω i a := by
  change (∑ i, (p i : ℂ) • (ω i).toLinearMap) a = _
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The two probability weights `t` and `1 - t`. -/
def binaryWeights (t : unitInterval) : stdSimplex ℝ (Fin 2) :=
  ⟨![(t : ℝ), 1 - (t : ℝ)],
    Fin.forall_fin_two.2 ⟨unitInterval.nonneg t, sub_nonneg.mpr (unitInterval.le_one t)⟩,
    by simp⟩

@[simp] lemma binaryWeights_zero (t : unitInterval) : binaryWeights t 0 = (t : ℝ) := rfl

@[simp] lemma binaryWeights_one (t : unitInterval) :
    binaryWeights t 1 = 1 - (t : ℝ) := rfl

/-! ## B. Binary mixtures -/

/-- Randomize between two states with probability `t` of choosing the first. -/
noncomputable def mix (ω φ : 𝓢[A]) (t : unitInterval) : 𝓢[A] :=
  finiteMix ![ω, φ] (binaryWeights t)

/-- Evaluation of a binary mixture is its pointwise convex combination. -/
@[simp]
lemma mix_apply (ω φ : 𝓢[A]) (t : unitInterval) (a : A) :
    mix ω φ t a = (t : ℝ) • ω a + (1 - (t : ℝ)) • φ a := by
    unfold mix
    rw [finiteMix_apply, Fin.sum_univ_two]
    simp [RCLike.real_smul_eq_coe_mul]

/-- The underlying linear functional of a mixture is the pointwise convex combination. -/
lemma mix_toLinearMap (ω φ : 𝓢[A]) (t : unitInterval) :
    (mix ω φ t).toLinearMap =
      (t : ℝ) • ω.toLinearMap + (1 - (t : ℝ)) • φ.toLinearMap := by
  ext a
  change mix ω φ t a = (t : ℝ) • ω a + (1 - (t : ℝ)) • φ a
  exact mix_apply ω φ t a

/-- A state lies in the open segment between two states exactly when it is a genuine mixture of
them. -/
lemma mem_openSegment_iff_exists_mix (ω φ ψ : 𝓢[A]) :
    ω.toLinearMap ∈ openSegment ℝ φ.toLinearMap ψ.toLinearMap ↔
      ∃ t : unitInterval, t ≠ 0 ∧ t ≠ 1 ∧ mix φ ψ t = ω := by
  constructor
  · rintro ⟨t, s, ht, hs, hts, heq⟩
    have ht₁ : t < 1 := by linarith
    let u : unitInterval := ⟨t, by exact ⟨ht.le, ht₁.le⟩⟩
    refine ⟨u, ?_, ?_, ?_⟩
    · exact ne_of_gt (by exact_mod_cast ht)
    · exact ne_of_lt (by exact_mod_cast ht₁)
    · apply toLinearMap_injective
      change (mix φ ψ u).toLinearMap = ω.toLinearMap
      rw [mix_toLinearMap]
      change t • φ.toLinearMap + (1 - t) • ψ.toLinearMap = ω.toLinearMap
      rwa [show 1 - t = s by linarith]
  · rintro ⟨t, ht₀, ht₁, rfl⟩
    refine ⟨(t : ℝ), 1 - (t : ℝ), ?_, ?_, by ring, ?_⟩
    · exact_mod_cast unitInterval.pos_iff_ne_zero.mpr ht₀
    · exact sub_pos.mpr (by exact_mod_cast unitInterval.lt_one_iff_ne_one.mpr ht₁)
    · rw [mix_toLinearMap]

/-! ## C. The state space in the algebraic dual -/

/-- General states embedded into the complex algebraic dual. -/
def stateSpace : Set (A →ₗ[ℂ] ℂ) :=
  Set.range fun ω : 𝓢[A] => ω.toLinearMap

/-- The general state space is convex in the algebraic dual. -/
lemma stateSpace_convex : Convex ℝ (stateSpace (A := A)) := by
  rintro x ⟨ω, rfl⟩ y ⟨φ, rfl⟩ t s ht hs hts
  have ht₁ : t ≤ 1 := by linarith
  let u : unitInterval := ⟨t, by exact ⟨ht, ht₁⟩⟩
  refine ⟨mix ω φ u, ?_⟩
  change (mix ω φ u).toLinearMap = t • ω.toLinearMap + s • φ.toLinearMap
  rw [mix_toLinearMap]
  change t • ω.toLinearMap + (1 - t) • φ.toLinearMap =
    t • ω.toLinearMap + s • φ.toLinearMap
  rw [show s = 1 - t by linarith]

end UnitalPositiveLinearMap
