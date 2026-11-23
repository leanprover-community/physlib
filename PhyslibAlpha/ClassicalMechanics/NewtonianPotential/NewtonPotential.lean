/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Basic
public import PhyslibAlpha.QuantumMechanics.Hydrogen.PolyBounded

/-!
# The Newtonian potential of a Schwartz mass density

## i. Overview

For a mass density `ρ` on `Space 3` given by a Schwartz map, the Newtonian potential is
`Φ(x) = -G ∫ ρ(y) / ‖x - y‖ dy`. This module defines `Φ`, shows that it is bounded and hence
defines a tempered distribution, and proves Poisson's equation `ΔΦ = 4πGρ` in the weak form:
`(Δᵈ Φ) η = 4πG ∫ η ρ` for every Schwartz map `η`.

The proof exchanges the two integrals (Fubini) and applies the Laplacian of the point-source
potential `‖x - y‖⁻¹`, which is `-4π` times the Dirac delta at `y`.

## ii. Key results

- `newtonPotential` : the Newtonian potential of a Schwartz mass density.
- `exists_integral_abs_mul_inv_norm_sub_le` : `∫ |ρ(y)| / ‖x - y‖ dy` is bounded uniformly in `x`.
- `isDistBounded_newtonPotential` : the Newtonian potential is bounded.
- `newtonPotential_translateSchwartz` : the potential of a translated density.
- `distLaplacian_newtonPotential_apply` : Poisson's equation in weak form.

## iii. Table of contents

- A. A uniform bound for the potential integral
- B. The Newtonian potential
- C. Poisson's equation

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution
open scoped SchwartzMap LineDeriv Laplacian

/-!

## A. A uniform bound for the potential integral

-/

open PhyslibAlpha.Hydrogen in
/-- For a Schwartz map `ρ` on `Space 3`, the integral `∫ |ρ(y)| / ‖x - y‖ dy` is bounded
uniformly in `x`. Near `x` the integrand is at most `sup |ρ| / ‖x - y‖`, away from `x` it is at
most `|ρ(y)|`. -/
lemma exists_integral_abs_mul_inv_norm_sub_le (ρ : 𝓢(Space 3, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space 3, ∫ y, |ρ y| * ‖x - y‖⁻¹ ≤ C := by
  obtain ⟨S, -, hS⟩ := ρ.decay 0 0
  have hS' : ∀ y, |ρ y| ≤ S := fun y => by
    have := hS y
    simpa [norm_iteratedFDeriv_zero] using this
  have hk : Integrable (fun z : Space 3 => ‖z‖⁻¹ * ((1 + ‖z‖) ^ 3)⁻¹) :=
    integrable_inv_norm_mul_one_add_norm_pow (d := 3) (by norm_num) (M := 3) le_rfl
  have hρ : Integrable (fun y : Space 3 => |ρ y|) := ρ.integrable.norm
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS' 0)
  refine ⟨S * 8 * (∫ z : Space 3, ‖z‖⁻¹ * ((1 + ‖z‖) ^ 3)⁻¹) + ∫ y : Space 3, |ρ y|, ?_,
    fun x => ?_⟩
  · have h1 : 0 ≤ ∫ z : Space 3, ‖z‖⁻¹ * ((1 + ‖z‖) ^ 3)⁻¹ :=
      integral_nonneg fun z => by positivity
    have h2 : 0 ≤ ∫ y : Space 3, |ρ y| := integral_nonneg fun y => abs_nonneg _
    positivity
  have hkx : Integrable (fun y : Space 3 => ‖y - x‖⁻¹ * ((1 + ‖y - x‖) ^ 3)⁻¹) :=
    hk.comp_sub_right x
  have hint : Integrable (fun y : Space 3 => |ρ y| * ‖x - y‖⁻¹) := by
    have := ((IsDistBounded.inv_shift (d := 3) x).integrable_space_mul ρ).norm
    simpa [norm_sub_rev] using this
  calc ∫ y, |ρ y| * ‖x - y‖⁻¹
      ≤ ∫ y, (S * 8 * (‖y - x‖⁻¹ * ((1 + ‖y - x‖) ^ 3)⁻¹) + |ρ y|) := by
        refine integral_mono hint ((hkx.const_mul _).add hρ) fun y => ?_
        simp only
        rw [norm_sub_rev x y]
        set r := ‖y - x‖
        have hr : 0 ≤ r := norm_nonneg _
        rcases le_or_gt r 1 with h | h
        · have h8 : 1 ≤ 8 * ((1 + r) ^ 3)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
            nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + r)
              (by linarith : 1 + r ≤ 2) 3]
          have : |ρ y| * r⁻¹ ≤ S * r⁻¹ * (8 * ((1 + r) ^ 3)⁻¹) := by
            calc |ρ y| * r⁻¹ ≤ S * r⁻¹ := by gcongr; exact hS' y
              _ ≤ S * r⁻¹ * (8 * ((1 + r) ^ 3)⁻¹) := le_mul_of_one_le_right (by positivity) h8
          nlinarith [abs_nonneg (ρ y)]
        · have : |ρ y| * r⁻¹ ≤ |ρ y| :=
            mul_le_of_le_one_right (abs_nonneg _) (inv_le_one_of_one_le₀ h.le)
          have : 0 ≤ S * 8 * (r⁻¹ * ((1 + r) ^ 3)⁻¹) := by positivity
          linarith
    _ = S * 8 * (∫ z : Space 3, ‖z‖⁻¹ * ((1 + ‖z‖) ^ 3)⁻¹) + ∫ y : Space 3, |ρ y| := by
        rw [integral_add (hkx.const_mul _) hρ, integral_const_mul]
        congr 2
        exact integral_sub_right_eq_self (fun z : Space 3 => ‖z‖⁻¹ * ((1 + ‖z‖) ^ 3)⁻¹) x

/-!

## B. The Newtonian potential

-/

/-- The Newtonian gravitational potential `Φ(x) = -G ∫ ρ(y) / ‖x - y‖ dy` of a mass density
`ρ` on `Space 3`, with `G` the gravitational constant. -/
def newtonPotential (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) (x : Space 3) : ℝ :=
  -G * ∫ y, ρ y * ‖x - y‖⁻¹

/-- The integrand of the Newtonian potential is integrable for every `x`. -/
lemma integrable_mul_inv_norm_sub (ρ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    Integrable (fun y : Space 3 => ρ y * ‖x - y‖⁻¹) := by
  have := (IsDistBounded.inv_shift (d := 3) x).integrable_space_mul ρ
  simpa [norm_sub_rev] using this

/-- The kernel `(x, y) ↦ ρ(y) / ‖x - y‖` is jointly measurable. -/
lemma measurable_mul_inv_norm_sub (ρ : 𝓢(Space 3, ℝ)) :
    Measurable (fun p : Space 3 × Space 3 => ρ p.2 * ‖p.1 - p.2‖⁻¹) :=
  (ρ.continuous.measurable.comp measurable_snd).mul
    ((measurable_fst.sub measurable_snd).norm.inv)

/-- The product kernel `(x, y) ↦ ψ(x) ρ(y) / ‖x - y‖` is integrable for Schwartz maps `ψ` and
`ρ`. This is what allows the two integrals to be exchanged. -/
lemma integrable_prod_mul_mul_inv_norm_sub (ψ ρ : 𝓢(Space 3, ℝ)) :
    Integrable (fun p : Space 3 × Space 3 => ψ p.1 * (ρ p.2 * ‖p.1 - p.2‖⁻¹))
      (volume.prod volume) := by
  obtain ⟨C, hC, hb⟩ := exists_integral_abs_mul_inv_norm_sub_le ρ
  have hmeas : Measurable (fun p : Space 3 × Space 3 => ψ p.1 * (ρ p.2 * ‖p.1 - p.2‖⁻¹)) :=
    (ψ.continuous.measurable.comp measurable_fst).mul (measurable_mul_inv_norm_sub ρ)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x =>
    (integrable_mul_inv_norm_sub ρ x).const_mul (ψ x), ?_⟩
  refine (ψ.integrable.norm.const_mul C).mono'
    (hmeas.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_inv, abs_norm]
  rw [integral_const_mul, abs_mul, abs_abs,
    abs_of_nonneg (integral_nonneg fun y => by positivity), mul_comm]
  gcongr
  exact hb x

/-- The Newtonian potential of a translated density is the translated potential. -/
lemma newtonPotential_translateSchwartz (G : ℝ) (ρ : 𝓢(Space 3, ℝ))
    (a : EuclideanSpace ℝ (Fin 3)) (x : Space 3) :
    newtonPotential G (translateSchwartz a ρ) x =
      newtonPotential G ρ (x - basis.repr.symm a) := by
  simp only [newtonPotential, translateSchwartz_apply]
  congr 1
  rw [← integral_sub_right_eq_self
    (fun y : Space 3 => ρ y * ‖x - basis.repr.symm a - y‖⁻¹) (basis.repr.symm a)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  congr 3
  abel

/-- The Newtonian potential of a Schwartz density is bounded, hence defines a distribution. -/
lemma isDistBounded_newtonPotential (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) :
    IsDistBounded (newtonPotential G ρ) := by
  obtain ⟨C, hC, hb⟩ := exists_integral_abs_mul_inv_norm_sub_le ρ
  have hm : AEStronglyMeasurable (newtonPotential G ρ) volume :=
    (((measurable_mul_inv_norm_sub ρ).stronglyMeasurable.integral_prod_right').const_mul
      (-G)).aestronglyMeasurable
  refine ⟨hm, 1, fun _ => |G| * C, fun _ => 0, fun _ => 0, fun _ => by positivity,
    fun _ => by simp, fun x => ?_⟩
  simp only [newtonPotential, norm_mul, norm_neg, Real.norm_eq_abs, add_zero, zpow_zero, mul_one,
    Finset.univ_unique, Finset.sum_singleton]
  gcongr
  calc |∫ y, ρ y * ‖x - y‖⁻¹| ≤ ∫ y, |ρ y * ‖x - y‖⁻¹| := by
        simpa using norm_integral_le_integral_norm (fun y : Space 3 => ρ y * ‖x - y‖⁻¹)
    _ = ∫ y, |ρ y| * ‖x - y‖⁻¹ := by simp [abs_mul]
    _ ≤ C := hb x

/-- The Newtonian potential of a Schwartz density is bounded. -/
lemma exists_abs_newtonPotential_le (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Space 3, |newtonPotential G ρ x| ≤ B := by
  obtain ⟨C, hC, h⟩ := exists_integral_abs_mul_inv_norm_sub_le ρ
  refine ⟨|G| * C, by positivity, fun x => ?_⟩
  rw [newtonPotential, abs_mul, abs_neg]
  gcongr
  calc |∫ y, ρ y * ‖x - y‖⁻¹| ≤ ∫ y, |ρ y * ‖x - y‖⁻¹| := abs_integral_le_integral_abs
    _ = ∫ y, |ρ y| * ‖x - y‖⁻¹ := by simp [abs_mul]
    _ ≤ C := h x

/-!

## C. Poisson's equation

-/

/-- **Poisson's equation** for the Newtonian potential, in weak form: for a Schwartz mass
density `ρ` and every Schwartz test function `η`, `(Δᵈ Φ) η = 4πG ∫ η ρ`, i.e. `ΔΦ = 4πGρ`. -/
theorem distLaplacian_newtonPotential_apply (G : ℝ) (ρ η : 𝓢(Space 3, ℝ)) :
    (Δᵈ (distOfFunction (newtonPotential G ρ) (isDistBounded_newtonPotential G ρ))) η =
      4 * Real.pi * G * ∫ x, η x * ρ x := by
  rw [distLaplacian_apply, distOfFunction_apply]
  set ψ : 𝓢(Space 3, ℝ) := Δ η with hψ
  have hint := integrable_prod_mul_mul_inv_norm_sub ψ ρ
  have key : ∫ x, ψ x * ∫ y, ρ y * ‖x - y‖⁻¹ = ∫ y, ρ y * (-(4 * Real.pi) * η y) := by
    calc ∫ x, ψ x * ∫ y, ρ y * ‖x - y‖⁻¹
        = ∫ x, ∫ y, ψ x * (ρ y * ‖x - y‖⁻¹) := by
          simp_rw [integral_const_mul]
      _ = ∫ y, ∫ x, ψ x * (ρ y * ‖x - y‖⁻¹) := integral_integral_swap hint
      _ = ∫ y, ρ y * ∫ x, ψ x * ‖x - y‖⁻¹ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only
          ring
      _ = ∫ y, ρ y * (-(4 * Real.pi) * η y) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          have h := congrArg (fun T => T η) (distLaplacian_inv_norm_sub y)
          simp only [distLaplacian_apply, distOfFunction_apply, smul_eq_mul] at h
          simp only
          rw [← hψ] at h
          rw [h]
          simp
  calc ∫ x, ψ x • newtonPotential G ρ x
      = -G * ∫ x, ψ x * ∫ y, ρ y * ‖x - y‖⁻¹ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [newtonPotential, smul_eq_mul]
        ring
    _ = 4 * Real.pi * G * ∫ x, η x * ρ x := by
        rw [key, ← integral_const_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        ring

end PhyslibAlpha.NewtonianPotential
