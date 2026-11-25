/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.CurvDeriv
public import PhyslibAlpha.Relativity.General.Schwarzschild.ElectricWeyl
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Schwarzschild–de Sitter curvature in the orthonormal frame

Frame-level curvature decomposition, Kretschmann scalar, Einstein-space identities, and
conservation of the Einstein tensor for Schwarzschild–de Sitter spacetime.

## i. Overview

In the orthonormal frame `(t, r, θ, φ)`, the Schwarzschild–de Sitter Riemann curvature splits into
the trace-free Schwarzschild Weyl tensor `schwarzschild (M / r³)` and a pure-trace de Sitter
contribution `deSitterPart Λ i j k l = (Λ / 3) (η_{ik} η_{jl} - η_{il} η_{jk})`.

Squaring this decomposition yields the Kretschmann scalar `48 M² / r⁶ + 8 Λ² / 3`, where cross
terms vanish by trace-freeness of the Weyl part. Contracting against `η` annihilates the Weyl part
(`weylRic_zero`) and leaves `Ric = Λ η`, `S = 4 Λ`, and `G = -Λ η`, specialising at `Λ = 0` to
Schwarzschild's vacuum solution. Because `Ric = Λ η` and `S = 4 Λ` are constant in the frame, the
contracted Bianchi identity holds without being assumed (`sds_frame_einstein_conserved`).

## ii. Key results

- `deSitterPart` : constant-curvature trace part `(Λ / 3) (η_{ik} η_{jl} - η_{il} η_{jk})`
  with its Riemann symmetries.
- `sdsFrameSqSum_eq`, `kretschmann_sds` : frame Kretschmann scalar `48 M² / r⁶ + 8 Λ² / 3`.
- `sdsRic_eq`, `sdsScalar_eq`, `sdsEinstein_eq` : `Ric = Λ η`, `S = 4 Λ`, `G = -Λ η`.
- `schwarzschild_ricci_zero`, `schwarzschild_scalar_zero`, `schwarzschild_einstein_zero` :
  `Λ = 0` vacuum specialisation.
- `sds_frame_bianchi`, `sds_frame_einstein_conserved` : proved frame Bianchi identity and
  `∇ · G = 0`.

## iii. Table of contents

- A. The de Sitter trace part and its symmetries
- B. Frame Kretschmann scalar
- C. Frame Ricci, scalar curvature, and Einstein tensors
- D. Vacuum limit at `Λ = 0`
- E. Conservation of the frame Einstein tensor

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace SchwarzschildDeSitter

/-!

## A. The de Sitter trace part and its symmetries

-/

/-- The pure-trace part of the frame Riemann tensor for cosmological constant `Λ`:
`(Λ / 3) (η_{ik} η_{jl} - η_{il} η_{jk})`. -/
noncomputable def deSitterPart (Λ : ℝ) (i j k l : Fin 4) : ℝ :=
  (Λ / 3) * (minkowskiMetric4 i k * minkowskiMetric4 j l
    - minkowskiMetric4 i l * minkowskiMetric4 j k)

/-- Antisymmetry of `deSitterPart` in its last pair of indices. -/
lemma deSitterPart_skew_last (Λ : ℝ) (i j k l : Fin 4) :
    deSitterPart Λ i j k l = -deSitterPart Λ i j l k := by
  simp only [deSitterPart]
  ring

/-- Pair symmetry of `deSitterPart`. -/
lemma deSitterPart_pair_symm (Λ : ℝ) (i j k l : Fin 4) :
    deSitterPart Λ i j k l = deSitterPart Λ k l i j := by
  have h1 : minkowskiMetric4 k i = minkowskiMetric4 i k := minkowskiMetric4_symm.apply i k
  have h2 : minkowskiMetric4 l j = minkowskiMetric4 j l := minkowskiMetric4_symm.apply j l
  have h3 : minkowskiMetric4 k j = minkowskiMetric4 j k := minkowskiMetric4_symm.apply j k
  have h4 : minkowskiMetric4 l i = minkowskiMetric4 i l := minkowskiMetric4_symm.apply i l
  simp only [deSitterPart, h1, h2, h3, h4]
  ring

/-- First Bianchi identity for `deSitterPart`. -/
lemma deSitterPart_bianchi (Λ : ℝ) (i j k l : Fin 4) :
    deSitterPart Λ i j k l + deSitterPart Λ i k l j + deSitterPart Λ i l j k = 0 := by
  have h1 : minkowskiMetric4 k j = minkowskiMetric4 j k := minkowskiMetric4_symm.apply j k
  have h2 : minkowskiMetric4 l k = minkowskiMetric4 k l := minkowskiMetric4_symm.apply k l
  have h3 : minkowskiMetric4 l j = minkowskiMetric4 j l := minkowskiMetric4_symm.apply j l
  simp only [deSitterPart, h1, h2, h3]
  ring

/-!

## B. Frame Kretschmann scalar

-/

/-- Sum of squares of the orthonormal-frame components of the Schwarzschild–de Sitter
curvature: Weyl part plus trace part. -/
noncomputable def sdsFrameSqSum (M Λ r : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    ((Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l) *
    ((Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l)

section kretschmann

private lemma sum_minkowskiMetric4_mul (i : Fin 4) (f : Fin 4 → ℝ) :
    (∑ k : Fin 4, minkowskiMetric4 i k * f k) = minkowskiMetric4 i i * f i := by
  rw [Finset.sum_eq_single i]
  · intro k _ hki
    simp [minkowskiMetric4_apply, hki.symm]
  · simp

private lemma sum_kl_mul_deSitterPart (Λ : ℝ) (F : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) :
    (∑ k : Fin 4, ∑ l : Fin 4, F k l * deSitterPart Λ i j k l) =
      (Λ / 3) * minkowskiMetric4 i i * minkowskiMetric4 j j * (F i j - F j i) := by
  have h1 : (∑ k : Fin 4, ∑ l : Fin 4, F k l * (minkowskiMetric4 i k * minkowskiMetric4 j l)) =
      minkowskiMetric4 i i * (minkowskiMetric4 j j * F i j) := by
    have hinner : ∀ k : Fin 4,
        (∑ l : Fin 4, F k l * (minkowskiMetric4 i k * minkowskiMetric4 j l)) =
          minkowskiMetric4 i k * (∑ l : Fin 4, minkowskiMetric4 j l * F k l) := by
      intro k
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    simp_rw [hinner, sum_minkowskiMetric4_mul]
  have h2 : (∑ k : Fin 4, ∑ l : Fin 4, F k l * (minkowskiMetric4 i l * minkowskiMetric4 j k)) =
      minkowskiMetric4 i i * (minkowskiMetric4 j j * F j i) := by
    rw [Finset.sum_comm]
    have hinner : ∀ l : Fin 4,
        (∑ k : Fin 4, F k l * (minkowskiMetric4 i l * minkowskiMetric4 j k)) =
          minkowskiMetric4 i l * (∑ k : Fin 4, minkowskiMetric4 j k * F k l) := by
      intro l
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hinner, sum_minkowskiMetric4_mul]
  have hsplit : ∀ k l : Fin 4, F k l * deSitterPart Λ i j k l =
      (Λ / 3) * (F k l * (minkowskiMetric4 i k * minkowskiMetric4 j l)
        - F k l * (minkowskiMetric4 i l * minkowskiMetric4 j k)) := by
    intro k l
    simp only [deSitterPart]
    ring
  simp_rw [hsplit, ← Finset.mul_sum, Finset.sum_sub_distrib, h1, h2]
  ring

/-- Sum of squares of the de Sitter trace part equals `8 Λ² / 3`. -/
private lemma deSitterPart_sq_sum (Λ : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, deSitterPart Λ i j k l * deSitterPart Λ i j k l) =
      8 * Λ ^ 2 / 3 := by
  simp_rw [sum_kl_mul_deSitterPart, deSitterPart, Fin.sum_univ_four, minkowskiMetric4_apply]
  norm_num
  ring

/-- Cross term between the Schwarzschild Weyl part and the de Sitter trace part vanishes. -/
private lemma weyl_deSitter_cross_zero (M Λ r : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      (Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l * deSitterPart Λ i j k l) = 0 := by
  simp_rw [sum_kl_mul_deSitterPart, Fin.sum_univ_four, minkowskiMetric4_apply,
    Schwarzschild.schwarzschild, Schwarzschild.electricPart]
  norm_num
  ring

/-- Frame Kretschmann sum of squares for Schwarzschild–de Sitter: `48 k² + 8 Λ² / 3` with
`k = M / r³`. -/
lemma sdsFrameSqSum_eq (M Λ r : ℝ) :
    sdsFrameSqSum M Λ r = 48 * (M / r ^ 3) ^ 2 + 8 * Λ ^ 2 / 3 := by
  have hW : (∑ i, ∑ j, ∑ k, ∑ l,
      (Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l *
        (Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l)
      = 48 * (M / r ^ 3) ^ 2 := Schwarzschild.frameSqSum_eq (M / r ^ 3)
  have hA := deSitterPart_sq_sum Λ
  have hX := weyl_deSitter_cross_zero M Λ r
  have hpt : ∀ i j k l : Fin 4,
      ((Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l) *
          ((Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l)
        = ((Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l *
              (Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l
            + (Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l * deSitterPart Λ i j k l)
          + ((Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l * deSitterPart Λ i j k l
            + deSitterPart Λ i j k l * deSitterPart Λ i j k l) := by
    intro i j k l
    ring
  simp only [sdsFrameSqSum, hpt, Finset.sum_add_distrib]
  simp only [hW, hX, hA]
  ring

/-- The Schwarzschild–de Sitter Kretschmann scalar `48 M² / r⁶ + 8 Λ² / 3`. -/
lemma kretschmann_sds (M Λ r : ℝ) (hr : r ≠ 0) :
    sdsFrameSqSum M Λ r = 48 * M ^ 2 / r ^ 6 + 8 * Λ ^ 2 / 3 := by
  rw [sdsFrameSqSum_eq]
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  have hr6 : r ^ 6 ≠ 0 := pow_ne_zero 6 hr
  field_simp [hr3, hr6]

end kretschmann

/-!

## C. Frame Ricci, scalar curvature, and Einstein tensors

-/

/-- Frame components of the Schwarzschild–de Sitter curvature: Weyl part plus trace part. -/
noncomputable def sdsFrameComp (M Λ r : ℝ) (i j k l : Fin 4) : ℝ :=
  (Schwarzschild.schwarzschild (M / r ^ 3)).comp i j k l + deSitterPart Λ i j k l

/-- Frame Ricci tensor `Ric_{σν} = ∑ ρ ρ', η^{ρρ'} R_{ρ'σρν}`. -/
noncomputable def sdsRic (M Λ r : ℝ) (σ ν : Fin 4) : ℝ :=
  ∑ ρ, ∑ ρ', minkowskiMetric4 ρ ρ' * sdsFrameComp M Λ r ρ' σ ρ ν

/-- The Weyl part is trace free and contributes nothing to the Ricci tensor. -/
lemma weylRic_zero (M r : ℝ) (σ ν : Fin 4) :
    (∑ ρ, ∑ ρ', minkowskiMetric4 ρ ρ' * (Schwarzschild.schwarzschild (M / r ^ 3)).comp ρ' σ ρ ν)
      = 0 := by
  fin_cases σ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, Schwarzschild.schwarzschild, Schwarzschild.electricPart] <;>
    ring

/-- The de Sitter trace part contracts to `Λ η` in every entry. -/
lemma traceRic_eq (Λ : ℝ) (σ ν : Fin 4) :
    (∑ ρ, ∑ ρ', minkowskiMetric4 ρ ρ' * deSitterPart Λ ρ' σ ρ ν) = Λ * minkowskiMetric4 σ ν := by
  fin_cases σ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, deSitterPart] <;> ring

/-- The frame Ricci tensor of Schwarzschild–de Sitter equals `Λ η`. -/
lemma sdsRic_eq (M Λ r : ℝ) (σ ν : Fin 4) :
    sdsRic M Λ r σ ν = Λ * minkowskiMetric4 σ ν := by
  have hW := weylRic_zero M r σ ν
  have hT := traceRic_eq Λ σ ν
  simp only [sdsRic, sdsFrameComp, mul_add, Finset.sum_add_distrib]
  simp only [hW, hT]
  ring

/-- Frame scalar curvature `S = ∑ σ ν, η^{σν} Ric_{σν}`. -/
noncomputable def sdsRicciScalar (M Λ r : ℝ) : ℝ :=
  ∑ σ, ∑ ν, minkowskiMetric4 σ ν * sdsRic M Λ r σ ν

/-- The frame scalar curvature of Schwarzschild–de Sitter equals `4 Λ`. -/
lemma sdsScalar_eq (M Λ r : ℝ) : sdsRicciScalar M Λ r = 4 * Λ := by
  simp only [sdsRicciScalar, sdsRic_eq]
  simp [Fin.sum_univ_four]
  ring

/-- Frame Einstein tensor `G_{ij} = Ric_{ij} - (1/2) S η_{ij}`. -/
noncomputable def sdsEinstein (M Λ r : ℝ) (i j : Fin 4) : ℝ :=
  sdsRic M Λ r i j - (1 / 2) * sdsRicciScalar M Λ r * minkowskiMetric4 i j

/-- The frame Einstein tensor of Schwarzschild–de Sitter equals `-Λ η`, solving
`G_{ij} + Λ η_{ij} = 0`. -/
lemma sdsEinstein_eq (M Λ r : ℝ) (i j : Fin 4) :
    sdsEinstein M Λ r i j = -(Λ * minkowskiMetric4 i j) := by
  simp only [sdsEinstein, sdsRic_eq, sdsScalar_eq]
  ring

/-- Diagonal frame components of `Ric`: `Ric_{tt} = -Λ`, `Ric_{rr} = Ric_{θθ} = Ric_{φφ} = Λ`. -/
lemma sdsRic_diag (M Λ r : ℝ) :
    sdsRic M Λ r 0 0 = -Λ ∧ sdsRic M Λ r 1 1 = Λ ∧
      sdsRic M Λ r 2 2 = Λ ∧ sdsRic M Λ r 3 3 = Λ := by
  have h0 : sdsRic M Λ r 0 0 = -Λ := by rw [sdsRic_eq]; simp
  have h1 : sdsRic M Λ r 1 1 = Λ := by rw [sdsRic_eq]; simp
  have h2 : sdsRic M Λ r 2 2 = Λ := by rw [sdsRic_eq]; simp
  have h3 : sdsRic M Λ r 3 3 = Λ := by rw [sdsRic_eq]; simp
  exact ⟨h0, h1, h2, h3⟩

/-- Off-diagonal frame entries of `Ric` vanish. -/
lemma sdsRic_offdiag (M Λ r : ℝ) {σ ν : Fin 4} (h : σ ≠ ν) :
    sdsRic M Λ r σ ν = 0 := by
  rw [sdsRic_eq]
  fin_cases σ <;> fin_cases ν <;> simp_all

/-- Diagonal frame components of `G`: `G_{tt} = Λ`, `G_{rr} = G_{θθ} = G_{φφ} = -Λ`. -/
lemma sdsEinstein_diag (M Λ r : ℝ) :
    sdsEinstein M Λ r 0 0 = Λ ∧ sdsEinstein M Λ r 1 1 = -Λ ∧
      sdsEinstein M Λ r 2 2 = -Λ ∧ sdsEinstein M Λ r 3 3 = -Λ := by
  have h0 : sdsEinstein M Λ r 0 0 = Λ := by rw [sdsEinstein_eq]; simp
  have h1 : sdsEinstein M Λ r 1 1 = -Λ := by rw [sdsEinstein_eq]; simp
  have h2 : sdsEinstein M Λ r 2 2 = -Λ := by rw [sdsEinstein_eq]; simp
  have h3 : sdsEinstein M Λ r 3 3 = -Λ := by rw [sdsEinstein_eq]; simp
  exact ⟨h0, h1, h2, h3⟩

/-!

## D. Vacuum limit at `Λ = 0`

-/

/-- At `Λ = 0`, the frame Ricci tensor vanishes: Schwarzschild is Ricci flat. -/
lemma schwarzschild_ricci_zero (M r : ℝ) (σ ν : Fin 4) :
    sdsRic M 0 r σ ν = 0 := by
  rw [sdsRic_eq]
  ring

/-- At `Λ = 0`, the frame scalar curvature vanishes. -/
lemma schwarzschild_scalar_zero (M r : ℝ) : sdsRicciScalar M 0 r = 0 := by
  rw [sdsScalar_eq]
  ring

/-- At `Λ = 0`, the frame Einstein tensor vanishes: Schwarzschild is a vacuum solution. -/
lemma schwarzschild_einstein_zero (M r : ℝ) (i j : Fin 4) :
    sdsEinstein M 0 r i j = 0 := by
  rw [sdsEinstein_eq]
  ring

/-!

## E. Conservation of the frame Einstein tensor

-/

/-- The frame derivative bundle of the Schwarzschild–de Sitter Einstein space: since `Ric = Λ η`
and `S = 4 Λ` are constant in the orthonormal frame, all frame derivatives vanish. -/
noncomputable def sdsFrameCurvDeriv : CurvDeriv where
  dRic := fun _ _ _ => 0
  dS := fun _ => 0

/-- The contracted Bianchi identity holds for the frame Einstein space without assumption. -/
lemma sds_frame_bianchi :
    ∀ b, (∑ a, minkowskiMetric4 a a * sdsFrameCurvDeriv.dRic a a b)
      = (1 / 2) * sdsFrameCurvDeriv.dS b := by
  intro b
  simp [sdsFrameCurvDeriv]

/-- The frame Einstein tensor of Schwarzschild–de Sitter is conserved (`∇ · G = 0`), proved
from `sds_frame_bianchi`. -/
lemma sds_frame_einstein_conserved (b : Fin 4) :
    divergence (CurvDeriv.dEinstein sdsFrameCurvDeriv) b = 0 :=
  divergence_einstein_eq_zero sdsFrameCurvDeriv sds_frame_bianchi b

end SchwarzschildDeSitter

end GeneralRelativity
