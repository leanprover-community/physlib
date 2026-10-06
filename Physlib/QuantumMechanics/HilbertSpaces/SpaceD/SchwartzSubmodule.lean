/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Basic
/-!

# Schwartz submodule

## i. Overview

In this module we define the Schwartz submodule of `SpaceDHilbertSpace d μ`.
`SchwartzSubmodule d μ` consists of the `μ`-a.e. equal equivalence classes of Schwartz maps
on `Space d`.

This is an import subspace of the Hilbert space. For one, the Fourier transform maps the Schwartz
submodule into itself. It also is a convenient dense domain on which to define derivative operators.

## ii. Key results

- `SchwartzSubmodule d μ`: Submodule of `SpaceDHilbertSpace d μ` consisting of the L² equivalence
  classes of Schwartz maps `𝓢(Space d, ℂ)`.
- `SchwartzSubmoduleOn Ω μ`: The projection of `SchwartzSubmodule d μ`
  onto `SpaceDHilbertSpaceOn Ω μ`.

## iii. Table of contents

- A. SchwartzSubmodule
  - A.1. Coercions
  - A.2. Misc.
- B. SchwartzSubmoduleOn

## iv. References

* None.
-/

@[expose] public section

noncomputable section
namespace QuantumMechanics

open MeasureTheory
open InnerProductSpace
open SchwartzMap

namespace SpaceDHilbertSpace

/-!
## A. SchwartzSubmodule
-/

/-- The continuous linear map including Schwartz maps into `SpaceDHilbertSpace d μ`. -/
def schwartzIncl {d : ℕ} (μ : Measure (Space d)) [μ.HasTemperateGrowth] :
    𝓢(Space d, ℂ) →L[ℂ] SpaceDHilbertSpace d μ :=
  toLpCLM ℂ ℂ 2 μ

/-- The submodule of `SpaceDHilbertSpace d` corresponding to Schwartz maps. -/
abbrev SchwartzSubmodule (d : ℕ) (μ : Measure (Space d) := volume) [μ.HasTemperateGrowth] :
    Submodule ℂ (SpaceDHilbertSpace d μ) :=
  (schwartzIncl μ).range

/-- The linear equivalence between the Schwartz maps `𝓢(Space d, ℂ)` and the Schwartz submodule
  of `SpaceDHilbertSpace d μ`. -/
def schwartzEquiv
    {d : ℕ} (μ : Measure (Space d)) [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] :
    𝓢(Space d, ℂ) ≃ₗ[ℂ] SchwartzSubmodule d μ :=
  LinearEquiv.ofInjective (schwartzIncl μ).toLinearMap (injective_toLp 2 μ)

namespace SchwartzSubmodule

variable {d : ℕ}
variable {μ : Measure (Space d)} [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure]
variable (f g : 𝓢(Space d, ℂ)) (ψ : SchwartzSubmodule d μ)

/-!
### A.1. Coercions
-/

instance : CoeFun (SchwartzSubmodule d μ) fun _ ↦ Space d → ℂ := ⟨fun ψ ↦ ψ.val⟩

set_option backward.isDefEq.respectTransparency false in
lemma schwartzEquiv_apply_coe : ↑(schwartzEquiv μ f) = schwartzIncl μ f := by simp [schwartzEquiv]

lemma schwartzEquiv_coe_ae : schwartzEquiv μ f =ᵐ[μ] f := coeFn_toLp f 2 μ

lemma schwartzEquiv_symm_coe_ae : (schwartzEquiv μ).symm ψ =ᵐ[μ] ψ := by
  nth_rw 2 [← (schwartzEquiv μ).apply_symm_apply ψ]
  exact (schwartzEquiv_coe_ae _).symm

lemma schwartzEquiv_ae_eq (h : schwartzEquiv μ f =ᵐ[μ] schwartzEquiv μ g) : f = g :=
  (EmbeddingLike.apply_eq_iff_eq _).mp (SetLike.coe_eq_coe.mp (ext_iff.mpr h))

/-!
### A.2. Misc.
-/

@[simp]
lemma zero_eq_top (μ : Measure (Space 0)) [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] :
    SchwartzSubmodule 0 μ = ⊤ := by
  ext ψ
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_top, iff_true]
  let g : 𝓢(Space 0, ℂ) := {
    toFun x := ψ 0
    smooth' := contDiff_const
    decay' k n := by
      refine ⟨‖ψ 0‖, fun x ↦ ?_⟩
      rcases eq_zero_or_pos n with rfl | hn
      · rw [← one_mul ‖ψ 0‖]
        refine mul_le_mul ?_ (by simp) (norm_nonneg _) zero_le_one
        simp [Space.point_dim_zero_eq, zero_pow_le_one]
      · simp [iteratedFDeriv_const_of_ne hn.ne']
  }
  use g
  ext
  filter_upwards [schwartzEquiv_coe_ae g] with x hg
  rw [← schwartzEquiv_apply_coe, hg, Space.point_dim_zero_eq x]
  rfl

variable (d μ) in
omit [μ.IsOpenPosMeasure] in
lemma dense [IsFiniteMeasureOnCompacts μ] :
    Dense (SchwartzSubmodule d μ : Set (SpaceDHilbertSpace d μ)) :=
  denseRange_toLpCLM ENNReal.top_ne_ofNat.symm

lemma schwartzEquiv_inner :
    ⟪schwartzEquiv μ f, schwartzEquiv μ g⟫_ℂ = ∫ x, starRingEnd ℂ (f x) * g x ∂μ := by
  apply integral_congr_ae
  filter_upwards [schwartzEquiv_coe_ae f, schwartzEquiv_coe_ae g] with _ hf hg
  simp [hf, hg, mul_comm]

variable (μ) in
lemma schwartzIncl_ker : (schwartzIncl μ).ker = (⊥ : Submodule ℂ 𝓢(Space d, ℂ)) := by
  ext; simp [← schwartzEquiv_apply_coe]

omit [μ.IsOpenPosMeasure] in
lemma toTemperedDistribution_schwartzIncl_eq :
    toTemperedDistribution (schwartzIncl μ g) = g.toTemperedDistributionCLM (Space d) ℂ μ :=
  Lp.toTemperedDistribution_toLp_eq g

end SchwartzSubmodule
end SpaceDHilbertSpace

/-!
## B. SchwartzSubmoduleOn
-/

namespace SpaceDHilbertSpaceOn

open SpaceDHilbertSpace

/-- The projection of `SchwartzSubmodule d μ` onto `SpaceDHilbertSpaceOn Ω μ`. -/
abbrev SchwartzSubmoduleOn
    {d : ℕ} (Ω : Set (Space d)) (μ : Measure (Space d) := volume) [μ.HasTemperateGrowth] :
    Submodule ℂ (SpaceDHilbertSpaceOn Ω μ) :=
  (SchwartzSubmodule d μ).map (subspaceProjection Ω μ)

namespace SchwartzSubmoduleOn

variable {d : ℕ} (Ω : Set (Space d)) (μ : Measure (Space d)) [μ.HasTemperateGrowth]

variable {Ω μ} in
lemma mem_iff {ψ : SpaceDHilbertSpaceOn Ω μ} :
    ψ ∈ SchwartzSubmoduleOn Ω μ ↔ ∃ φ : SchwartzSubmodule d μ, subspaceProjection Ω μ φ = ψ := by
  simp

end SchwartzSubmoduleOn
end SpaceDHilbertSpaceOn

end QuantumMechanics
end
