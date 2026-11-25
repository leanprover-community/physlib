/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.WaveEquation.Basic
public import PhyslibAlpha.Relativity.Poincare.Fields

/-!

# The wave operator is Poincaré invariant

The wave operator commutes with the action of the Poincaré group on fields.

## i. Overview

The wave operator is the Minkowski metric trace of the second derivative. A Lorentz
transformation changes the second derivative by the matrix of the transformation. The metric
trace is unchanged because the matrix preserves the metric. A translation commutes with every
derivative. Together these show that the wave operator commutes with the action of the Poincaré
group on smooth fields.

## ii. Key results

- `sum_eta_lorentz` : the matrix of a Lorentz transformation preserves the metric.
- `waveTrace_comp_lorentz` : the metric trace of the second derivative of `u ∘ Λ`.
- `smoothWaveOperator_actSmooth` : the wave operator commutes with the action of the Poincaré group.

## iii. Table of contents

- A. The metric is preserved
- B. Derivatives of Lorentz transformed functions
- C. Derivatives of translated functions

## iv. References

None.

## A. The metric is preserved

- `sum_eta_lorentz` : the matrix of a Lorentz transformation preserves the metric.

## B. Derivatives of Lorentz transformed functions

- `waveTrace_comp_lorentz` : the metric trace of the second derivative of `u ∘ Λ`.

## C. Derivatives of translated functions

- `deriv_comp_add_right` : a translation commutes with the spacetime derivative.
-/

@[expose] public section

noncomputable section

open scoped ContDiff
open Minkowski SpaceTime minkowskiMatrix Matrix

namespace WaveEquation

variable {d : ℕ}

section Metric

/-- The matrix of a Lorentz transformation preserves the metric. -/
lemma sum_eta_lorentz (Λ : LorentzGroup d) (ν ρ : Fin 1 ⊕ Fin d) :
    ∑ μ, η μ μ * Λ.1 ν μ * Λ.1 ρ μ = η ν ρ := by
  have h : Λ.1 * dual Λ.1 = 1 := LorentzGroup.mem_iff_self_mul_dual.mp Λ.2
  have h1 : Λ.1 * η * Λ.1ᵀ * η = 1 := by simpa [dual, Matrix.mul_assoc] using h
  have h2 : Λ.1 * η * Λ.1ᵀ = η := by
    calc Λ.1 * η * Λ.1ᵀ = Λ.1 * η * Λ.1ᵀ * (η * η) := by rw [minkowskiMatrix.sq, mul_one]
      _ = (Λ.1 * η * Λ.1ᵀ * η) * η := by rw [Matrix.mul_assoc _ η η]
      _ = η := by rw [h1, one_mul]
  have h3 : (Λ.1 * η * Λ.1ᵀ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) ν ρ = η ν ρ := by
    rw [h2]
  rw [← h3, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h4 : (Λ.1 * η : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) ν μ = Λ.1 ν μ * η μ μ := by
    rw [Matrix.mul_apply, Finset.sum_eq_single μ]
    · intro σ _ hσ
      rw [minkowskiMatrix.off_diag_zero hσ]
      ring
    · intro h; exact absurd (Finset.mem_univ μ) h
  rw [h4, Matrix.transpose_apply]
  ring

end Metric

section Derivatives

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The spacetime derivative of a finite sum is the sum of the derivatives. -/
lemma deriv_finset_sum {ι : Type*} (s : Finset ι) (f : ι → SpaceTime d → V)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (μ : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
    ∂_ μ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, ∂_ μ (f i) x := by
  rw [SpaceTime.deriv_eq, fderiv_fun_sum (fun i hi => hf i hi x)]
  simp [SpaceTime.deriv_eq]

/-- The second derivative of a Lorentz transformed function. -/
lemma deriv_deriv_comp_lorentz (u : SpaceTime d → V) (hu : ContDiff ℝ ∞ u) (Λ : LorentzGroup d)
    (μ : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
    ∂_ μ (∂_ μ (fun y => u (Λ • y))) x =
      ∑ ν, ∑ ρ, (Λ.1 ν μ * Λ.1 ρ μ) • ∂_ ρ (∂_ ν u) (Λ • x) := by
  have hd : ∀ ν, ContDiff ℝ ∞ (∂_ ν u) := fun ν => SpaceTime.contDiff_deriv ν u (by simpa using hu)
  have h1 : ∀ y, ∂_ μ (fun z => u (Λ • z)) y = ∑ ν, Λ.1 ν μ • ∂_ ν u (Λ • y) := fun y =>
    SpaceTime.deriv_comp_lorentz_action μ u (hu.differentiable (by simp)) Λ y
  have h2 : ∂_ μ (fun z => u (Λ • z)) = fun y => ∑ ν, Λ.1 ν μ • ∂_ ν u (Λ • y) := funext h1
  have hdiff : ∀ ν, Differentiable ℝ (fun y => Λ.1 ν μ • ∂_ ν u (Λ • y)) := fun ν => by
    have : Differentiable ℝ (fun y => ∂_ ν u (Λ • y)) :=
      ((hd ν).differentiable (by simp)).comp (Lorentz.Vector.actionCLM Λ).differentiable
    exact this.const_smul _
  rw [h2, deriv_finset_sum _ _ (fun ν _ => hdiff ν)]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have h3 : ∂_ μ (fun y => Λ.1 ν μ • ∂_ ν u (Λ • y)) x =
      Λ.1 ν μ • ∂_ μ (fun y => ∂_ ν u (Λ • y)) x := by
    have := SpaceTime.deriv_const_smul μ (Λ.1 ν μ) (f := fun y => ∂_ ν u (Λ • y))
      (((hd ν).differentiable (by simp)).comp (Lorentz.Vector.actionCLM Λ).differentiable)
    exact congrFun this x
  rw [h3, SpaceTime.deriv_comp_lorentz_action μ (∂_ ν u) ((hd ν).differentiable (by simp)) Λ x,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_smul]

/-- The metric trace of the second derivative of a Lorentz transformed function. -/
lemma waveTrace_comp_lorentz (u : SpaceTime d → V) (hu : ContDiff ℝ ∞ u) (Λ : LorentzGroup d)
    (x : SpaceTime d) :
    ∑ μ, (η μ μ : ℝ) • ∂_ μ (∂_ μ (fun y => u (Λ • y))) x =
      ∑ ν, (η ν ν : ℝ) • ∂_ ν (∂_ ν u) (Λ • x) := by
  have key : ∀ ν ρ, ∑ μ, (η μ μ : ℝ) * (Λ.1 ν μ * Λ.1 ρ μ) = η ν ρ := fun ν ρ => by
    rw [← sum_eta_lorentz Λ ν ρ]
    exact Finset.sum_congr rfl fun μ _ => by ring
  calc ∑ μ, (η μ μ : ℝ) • ∂_ μ (∂_ μ (fun y => u (Λ • y))) x
      = ∑ μ, ∑ ν, ∑ ρ, ((η μ μ : ℝ) * (Λ.1 ν μ * Λ.1 ρ μ)) • ∂_ ρ (∂_ ν u) (Λ • x) := by
        simp_rw [deriv_deriv_comp_lorentz u hu Λ, Finset.smul_sum, smul_smul]
    _ = ∑ ν, ∑ μ, ∑ ρ, ((η μ μ : ℝ) * (Λ.1 ν μ * Λ.1 ρ μ)) • ∂_ ρ (∂_ ν u) (Λ • x) :=
        Finset.sum_comm
    _ = ∑ ν, ∑ ρ, ∑ μ, ((η μ μ : ℝ) * (Λ.1 ν μ * Λ.1 ρ μ)) • ∂_ ρ (∂_ ν u) (Λ • x) :=
        Finset.sum_congr rfl fun ν _ => Finset.sum_comm
    _ = ∑ ν, ∑ ρ, (η ν ρ : ℝ) • ∂_ ρ (∂_ ν u) (Λ • x) := by
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => ?_
        rw [← Finset.sum_smul, key]
    _ = ∑ ν, (η ν ν : ℝ) • ∂_ ν (∂_ ν u) (Λ • x) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.sum_eq_single ν]
        · intro ρ _ hρ
          rw [minkowskiMatrix.off_diag_zero (Ne.symm hρ), zero_smul]
        · intro h; exact absurd (Finset.mem_univ ν) h

end Derivatives

section Translation

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A translation commutes with the spacetime derivative. -/
lemma deriv_comp_add_right (u : SpaceTime d → V) (b : SpaceTime d) (μ : Fin 1 ⊕ Fin d) :
    ∂_ μ (fun y => u (y + b)) = fun y => ∂_ μ u (y + b) := by
  funext y
  simp only [SpaceTime.deriv_eq]
  rw [fderiv_comp_add_right]

/-- The metric trace of the second derivative of a transformed function. -/
lemma waveTrace_act (g : PoincareGroup d) (u : SpaceTime d → V) (hu : ContDiff ℝ ∞ u)
    (x : SpaceTime d) :
    ∑ μ, (η μ μ : ℝ) • ∂_ μ (∂_ μ (PoincareGroup.act g u)) x =
      ∑ μ, (η μ μ : ℝ) • ∂_ μ (∂_ μ u) (g⁻¹ • x) := by
  set b : SpaceTime d := g⁻¹.translation with hb
  have hub : ContDiff ℝ ∞ (fun z => u (z + b)) := hu.comp (contDiff_id.add contDiff_const)
  have h : PoincareGroup.act g u = fun y => (fun z => u (z + b)) (g⁻¹.lorentz • y) := rfl
  rw [h, waveTrace_comp_lorentz (fun z => u (z + b)) hub g⁻¹.lorentz x]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [deriv_comp_add_right u b ν, deriv_comp_add_right (∂_ ν u) b ν]
  rfl

end Translation

section Operator

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The wave operator commutes with the action of the Poincaré group. -/
lemma smoothWaveOperator_actSmooth (g : PoincareGroup d) (u : smoothFields d V) :
    smoothWaveOperator (PoincareGroup.actSmooth g u) =
      PoincareGroup.actSmooth g (smoothWaveOperator u) := by
  apply Subtype.ext
  funext x
  rw [smoothWaveOperator_coe]
  simp only [Finset.sum_apply, Pi.smul_apply, PoincareGroup.actSmooth_coe]
  rw [waveTrace_act g u.1 (smoothFields_contDiff u) x, PoincareGroup.act_apply,
    smoothWaveOperator_coe]
  simp only [Finset.sum_apply, Pi.smul_apply]

end Operator

end WaveEquation
