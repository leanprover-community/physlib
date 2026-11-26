/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Laplacian
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric

/-!

# Three-dimensional spatial Laplacian on spacetime coordinates

The spatial Laplacian `∇² Φ = ∂₁² Φ + ∂₂² Φ + ∂₃² Φ` and its bridge to `Space.laplacian`.

## i. Overview

For static weak-field sources on four-dimensional spacetime coordinates `(x₀, x₁, x₂, x₃)`,
the flat spatial Laplacian `laplacian3 Φ x` sums the second partial derivatives along the spatial
coordinates `1, 2, 3`. This module isolates `laplacian3` and proves `laplacian3_eq_space_laplacian`,
equating it to `Space.laplacian` on the constant-time slice `x 0` for every `C²` potential `Φ`.

## ii. Key results

- `laplacian3` : spatial Laplacian `∂₁² Φ + ∂₂² Φ + ∂₃² Φ` on `Fin 4 → ℝ`.
- `laplacian3_eq_space_laplacian` : identification with `Space.laplacian` on spatial slices.

## iii. Table of contents

- A. Spatial Laplacian and `Space.laplacian` bridge

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.4). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 18.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 6
  (https://arxiv.org/pdf/gr-qc/9712019#page=144). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. Spatial Laplacian and `Space.laplacian` bridge

The spatial part `∂₁² + ∂₂² + ∂₃²` of the Minkowski d'Alembertian restricts on each constant-time
slice to the Euclidean Laplacian `Space.laplacian` in `Physlib`.

-/

/-- Three-dimensional spatial Laplacian `∇² Φ = ∂₁² Φ + ∂₂² Φ + ∂₃² Φ`. -/
noncomputable def laplacian3 (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  coordDeriv 1 (coordDeriv 1 Φ) x + coordDeriv 2 (coordDeriv 2 Φ) x +
    coordDeriv 3 (coordDeriv 3 Φ) x

/-- `laplacian3 Φ x` coincides with `Space.laplacian` on the constant-time spatial slice at
`x 0`. -/
lemma laplacian3_eq_space_laplacian (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hΦ : ContDiffAt ℝ 2 Φ x) :
    laplacian3 Φ x =
      Space.laplacian (fun s : Space 3 => Φ ![x 0, s 0, s 1, s 2]) ⟨![x 1, x 2, x 3]⟩ := by
  let L : Space 3 →L[ℝ] (Fin 4 → ℝ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun s => ![0, s 0, s 1, s 2]
        map_add' := fun a b => by ext i; fin_cases i <;> simp
        map_smul' := fun c a => by ext i; fin_cases i <;> simp }
  let x₀ : Fin 4 → ℝ := ![x 0, 0, 0, 0]
  let f : Space 3 → (Fin 4 → ℝ) := fun s => x₀ + L s
  let s₀ : Space 3 := ⟨![x 1, x 2, x 3]⟩
  have hf_eq : ∀ s : Space 3, f s = ![x 0, s 0, s 1, s 2] := fun s => by
    ext i; fin_cases i <;> simp [f, x₀, L]
  have hfs0 : f s₀ = x := by
    ext i; fin_cases i <;> simp [f, x₀, L, s₀]
  have hLbasis : ∀ k : Fin 3, L (Space.basis k) = Pi.single k.succ 1 := fun k => by
    ext i; fin_cases k <;> fin_cases i <;> simp [L, Space.basis_apply]
  have hderiv : ∀ (g : (Fin 4 → ℝ) → ℝ) (s : Space) (k : Fin 3),
      DifferentiableAt ℝ g (f s) →
      Space.deriv k (fun u => g (f u)) s = coordDeriv k.succ g (f s) := by
    intro g s k hg
    have hf_deriv : HasFDerivAt f L s :=
      ((hasFDerivAt_const x₀ s).add L.hasFDerivAt).congr_fderiv (by simp)
    have hcomp : HasFDerivAt (fun u => g (f u)) ((fderiv ℝ g (f s)).comp L) s :=
      hg.hasFDerivAt.comp s hf_deriv
    rw [Space.deriv_eq_fderiv_basis, hcomp.fderiv, ContinuousLinearMap.comp_apply,
      hLbasis k, coordDeriv_eq_fderiv hg]
  have hΦ_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 Φ y := hΦ.eventually (by simp)
  have hf_cont : Continuous f := continuous_const.add L.continuous
  have hf_tend : Filter.Tendsto f (nhds s₀) (nhds x) := by
    rw [← hfs0]
    exact hf_cont.continuousAt.tendsto
  have hs_nhds : ∀ᶠ s in nhds s₀, ContDiffAt ℝ 2 Φ (f s) :=
    Filter.Tendsto.eventually hf_tend hΦ_nhds
  have hΦs0 : ContDiffAt ℝ 2 Φ (f s₀) := hfs0.symm ▸ hΦ
  have h_snd : ∀ k : Fin 3,
      Space.deriv k (Space.deriv k (fun u : Space 3 => Φ (f u))) s₀ =
        coordDeriv k.succ (coordDeriv k.succ Φ) x := by
    intro k
    have hev : Space.deriv k (fun u => Φ (f u)) =ᶠ[nhds s₀]
        fun u => coordDeriv k.succ Φ (f u) := by
      filter_upwards [hs_nhds] with u hu
      exact hderiv Φ u k (hu.differentiableAt (by norm_num))
    rw [Space.deriv_eq_fderiv_basis, hev.fderiv_eq, ← Space.deriv_eq_fderiv_basis]
    rw [hderiv (coordDeriv k.succ Φ) s₀ k (coordDeriv_differentiableAt k.succ hΦs0), hfs0]
  have hslice : (fun s : Space 3 => Φ ![x 0, s 0, s 1, s 2]) = fun s => Φ (f s) :=
    funext fun s => congrArg Φ (hf_eq s).symm
  rw [hslice, congrFun (Space.laplacian_eq_sum_snd_deriv (fun s => Φ (f s))) s₀,
    Fin.sum_univ_three]
  rw [h_snd 0, h_snd 1, h_snd 2]
  simp only [laplacian3, Fin.succ_zero_eq_one]
  rfl

end Linearized

end GeneralRelativity
