/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.FrameKretschmann
public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.Basic
public import PhyslibAlpha.Relativity.Metrics.CurvatureDerivatives
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Schwarzschild–de Sitter curvature in the orthonormal frame

Frame-level curvature decomposition, Kretschmann scalar, Einstein-space identities, and
conservation of the Einstein tensor for `SchwarzschildDeSitterSpacetime`.

## i. Overview

In the orthonormal frame `(t, r, θ, φ)`, the Schwarzschild–de Sitter Riemann curvature splits into
the trace-free Schwarzschild Weyl tensor `electricWeylRiemann (S.M / r³)` and a pure-trace de Sitter
contribution `deSitterPart S.Λ i j k l = (S.Λ / 3) (η_{ik} η_{jl} - η_{il} η_{jk})`.

Squaring this decomposition yields the Kretschmann scalar `48 M² / r⁶ + 8 Λ² / 3`, where cross
terms vanish by trace-freeness of the Weyl part. Contracting against `η` annihilates the Weyl part
(`weylRic_zero`) and leaves `Ric = Λ η`, `R = 4 Λ`, and `G = -Λ η`, specializing at `Λ = 0` to
Schwarzschild's vacuum solution. Because `Ric = Λ η` and `R = 4 Λ` are constant in the frame, the
contracted Bianchi identity holds without being assumed (`frame_einstein_conserved`).

## ii. Key results

- `deSitterPart` : constant-curvature trace part `(Λ / 3) (η_{ik} η_{jl} - η_{il} η_{jk})`
  with its Riemann symmetries.
- `SchwarzschildDeSitterSpacetime.frameSumOfSquares`,
  `SchwarzschildDeSitterSpacetime.frameSumOfSquares_eq`,
  `SchwarzschildDeSitterSpacetime.kretschmann` : frame Kretschmann scalar
  `48 M² / r⁶ + 8 Λ² / 3`.
- `SchwarzschildDeSitterSpacetime.frameRicciTensor_eq`,
  `SchwarzschildDeSitterSpacetime.frameScalar_eq`,
  `SchwarzschildDeSitterSpacetime.frameEinstein_eq` : `Ric = Λ η`, `R = 4 Λ`, `G = -Λ η`.
- `SchwarzschildDeSitterSpacetime.vacuum_ricci_zero`,
  `SchwarzschildDeSitterSpacetime.vacuum_scalar_zero`,
  `SchwarzschildDeSitterSpacetime.vacuum_einstein_zero` : `Λ = 0` vacuum specialization.
- `SchwarzschildDeSitterSpacetime.frame_bianchi`,
  `SchwarzschildDeSitterSpacetime.frame_einstein_conserved` : proved frame Bianchi identity and
  `∇ · G = 0`.

## iii. Table of contents

- A. The de Sitter trace part and its symmetries
- B. Sum of squared frame curvature components
- C. Frame Ricci, scalar curvature, and Einstein tensors
- D. Vacuum limit at `Λ = 0`
- E. Conservation of the frame Einstein tensor

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1) & Sec. 4.2.
  [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 & Ch. 27.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace SchwarzschildDeSitter

/-!

## A. The de Sitter trace part and its symmetries

Constant-curvature spaces contribute a pure-trace Riemann tensor constructed solely from the
Minkowski frame metric and the cosmological constant `Λ`.

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

namespace SchwarzschildDeSitterSpacetime

/-!

## B. Sum of squared frame curvature components

Because the Weyl tensor is trace-free, its contraction with the pure-trace de Sitter Riemann part
vanishes identically, so the Kretschmann scalar separates cleanly into `48 M² / r⁶ + 8 Λ² / 3`.

-/

/-- Frame components of the Schwarzschild–de Sitter curvature: Weyl part plus trace part. -/
noncomputable def frameCurvatureComponent (S : SchwarzschildDeSitterSpacetime) (r : ℝ)
    (i j k l : Fin 4) : ℝ :=
  (Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l + deSitterPart S.Λ i j k l

/-- Sum of squares of the orthonormal-frame components of the Schwarzschild–de Sitter
curvature: Weyl part plus trace part. -/
noncomputable def frameSumOfSquares (S : SchwarzschildDeSitterSpacetime) (r : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, S.frameCurvatureComponent r i j k l * S.frameCurvatureComponent r i j k l

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
    simp_rw [hinner, sum_minkowskiMetric4_left]
  have h2 : (∑ k : Fin 4, ∑ l : Fin 4, F k l * (minkowskiMetric4 i l * minkowskiMetric4 j k)) =
      minkowskiMetric4 i i * (minkowskiMetric4 j j * F j i) := by
    rw [Finset.sum_comm]
    have hinner : ∀ l : Fin 4,
        (∑ k : Fin 4, F k l * (minkowskiMetric4 i l * minkowskiMetric4 j k)) =
          minkowskiMetric4 i l * (∑ k : Fin 4, minkowskiMetric4 j k * F k l) := by
      intro l
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hinner, sum_minkowskiMetric4_left]
  have hsplit : ∀ k l : Fin 4, F k l * deSitterPart Λ i j k l =
      (Λ / 3) * (F k l * (minkowskiMetric4 i k * minkowskiMetric4 j l)
        - F k l * (minkowskiMetric4 i l * minkowskiMetric4 j k)) := by
    intro k l
    simp only [deSitterPart]
    ring
  simp_rw [hsplit, ← Finset.mul_sum, Finset.sum_sub_distrib, h1, h2]
  ring

private lemma deSitterPart_sq_sum (Λ : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, deSitterPart Λ i j k l * deSitterPart Λ i j k l) =
      8 * Λ ^ 2 / 3 := by
  simp_rw [sum_kl_mul_deSitterPart, deSitterPart, Fin.sum_univ_four, minkowskiMetric4_apply]
  norm_num
  ring

private lemma weyl_deSitter_cross_zero (M Λ r : ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      (Schwarzschild.electricWeylRiemann (M / r ^ 3)).comp i j k l *
        deSitterPart Λ i j k l) = 0 := by
  simp_rw [sum_kl_mul_deSitterPart, Fin.sum_univ_four, minkowskiMetric4_apply,
    Schwarzschild.electricWeylRiemann, Schwarzschild.electricPart]
  norm_num
  ring

/-- Frame Kretschmann sum of squares for Schwarzschild–de Sitter: `48 k² + 8 Λ² / 3` with
`k = M / r³`. -/
lemma frameSumOfSquares_eq (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    S.frameSumOfSquares r = 48 * (S.M / r ^ 3) ^ 2 + 8 * S.Λ ^ 2 / 3 := by
  have hW : (∑ i, ∑ j, ∑ k, ∑ l,
      (Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l *
        (Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l)
      = 48 * (S.M / r ^ 3) ^ 2 :=
    Schwarzschild.electricWeyl_frameSumOfSquares_eq (S.M / r ^ 3)
  have hA := deSitterPart_sq_sum S.Λ
  have hX := weyl_deSitter_cross_zero S.M S.Λ r
  have hpt : ∀ i j k l : Fin 4,
      ((Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l +
          deSitterPart S.Λ i j k l) *
        ((Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l +
          deSitterPart S.Λ i j k l)
      = ((Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l *
            (Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l
          + (Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l *
            deSitterPart S.Λ i j k l)
        + ((Schwarzschild.electricWeylRiemann (S.M / r ^ 3)).comp i j k l *
            deSitterPart S.Λ i j k l
          + deSitterPart S.Λ i j k l * deSitterPart S.Λ i j k l) := by
    intro i j k l
    ring
  simp only [frameSumOfSquares, frameCurvatureComponent, hpt, Finset.sum_add_distrib]
  simp only [hW, hX, hA]
  ring

/-- The Schwarzschild–de Sitter Kretschmann scalar `48 M² / r⁶ + 8 Λ² / 3`. -/
lemma kretschmann (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    S.frameSumOfSquares r = 48 * S.M ^ 2 / r ^ 6 + 8 * S.Λ ^ 2 / 3 := by
  rw [S.frameSumOfSquares_eq]
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  have hr6 : r ^ 6 ≠ 0 := pow_ne_zero 6 hr
  field_simp [hr3, hr6]

/-!

## C. Frame Ricci, scalar curvature, and Einstein tensors

Contracting the frame Riemann tensor annihilates the trace-free Weyl contribution and leaves an
Einstein space `Ric = Λ η`, `R = 4 Λ`, and `G = -Λ η`.

-/

/-- Frame Ricci tensor `Ric_{σν} = ∑ ρ ρ', η^{ρρ'} R_{ρ'σρν}`. -/
noncomputable def frameRicciTensor (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (σ ν : Fin 4) : ℝ :=
  ∑ ρ, ∑ ρ', minkowskiMetric4 ρ ρ' * S.frameCurvatureComponent r ρ' σ ρ ν

/-- The Weyl part is trace free and contributes nothing to the Ricci tensor. -/
lemma weylRic_zero (M r : ℝ) (σ ν : Fin 4) :
    (∑ ρ, ∑ ρ', minkowskiMetric4 ρ ρ' *
      (Schwarzschild.electricWeylRiemann (M / r ^ 3)).comp ρ' σ ρ ν)
      = 0 := by
  fin_cases σ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, Schwarzschild.electricWeylRiemann, Schwarzschild.electricPart] <;>
    ring

/-- The de Sitter trace part contracts to `Λ η` in every entry. -/
lemma traceRic_eq (Λ : ℝ) (σ ν : Fin 4) :
    (∑ ρ, ∑ ρ', minkowskiMetric4 ρ ρ' * deSitterPart Λ ρ' σ ρ ν) = Λ * minkowskiMetric4 σ ν := by
  fin_cases σ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, deSitterPart] <;> ring

/-- The frame Ricci tensor of Schwarzschild–de Sitter equals `Λ η`. -/
lemma frameRicciTensor_eq (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (σ ν : Fin 4) :
    S.frameRicciTensor r σ ν = S.Λ * minkowskiMetric4 σ ν := by
  have hW := weylRic_zero S.M r σ ν
  have hT := traceRic_eq S.Λ σ ν
  simp only [frameRicciTensor, frameCurvatureComponent, mul_add, Finset.sum_add_distrib]
  simp only [hW, hT]
  ring

/-- Frame scalar curvature `S = ∑ σ ν, η^{σν} Ric_{σν}`. -/
noncomputable def frameScalarCurvature (S : SchwarzschildDeSitterSpacetime) (r : ℝ) : ℝ :=
  ∑ σ, ∑ ν, minkowskiMetric4 σ ν * S.frameRicciTensor r σ ν

/-- The frame scalar curvature of Schwarzschild–de Sitter equals `4 Λ`. -/
lemma frameScalar_eq (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    S.frameScalarCurvature r = 4 * S.Λ := by
  simp only [frameScalarCurvature, frameRicciTensor_eq]
  simp [Fin.sum_univ_four]
  ring

/-- Frame Einstein tensor `G_{ij} = Ric_{ij} - (1/2) S η_{ij}`. -/
noncomputable def frameEinstein (S : SchwarzschildDeSitterSpacetime) (r : ℝ)
    (i j : Fin 4) : ℝ :=
  S.frameRicciTensor r i j - (1 / 2) * S.frameScalarCurvature r * minkowskiMetric4 i j

/-- The frame Einstein tensor of Schwarzschild–de Sitter equals `-Λ η`, solving
`G_{ij} + Λ η_{ij} = 0`. -/
lemma frameEinstein_eq (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (i j : Fin 4) :
    S.frameEinstein r i j = -(S.Λ * minkowskiMetric4 i j) := by
  simp only [frameEinstein, frameRicciTensor_eq, frameScalar_eq]
  ring

/-- Diagonal frame components of `Ric`: `Ric_{tt} = -Λ`, `Ric_{rr} = Ric_{θθ} = Ric_{φφ} = Λ`. -/
lemma frameRicciTensor_diag (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    S.frameRicciTensor r 0 0 = -S.Λ ∧ S.frameRicciTensor r 1 1 = S.Λ ∧
      S.frameRicciTensor r 2 2 = S.Λ ∧ S.frameRicciTensor r 3 3 = S.Λ := by
  have h0 : S.frameRicciTensor r 0 0 = -S.Λ := by rw [frameRicciTensor_eq]; simp
  have h1 : S.frameRicciTensor r 1 1 = S.Λ := by rw [frameRicciTensor_eq]; simp
  have h2 : S.frameRicciTensor r 2 2 = S.Λ := by rw [frameRicciTensor_eq]; simp
  have h3 : S.frameRicciTensor r 3 3 = S.Λ := by rw [frameRicciTensor_eq]; simp
  exact ⟨h0, h1, h2, h3⟩

/-- Off-diagonal frame entries of `Ric` vanish. -/
lemma frameRicciTensor_offdiag (S : SchwarzschildDeSitterSpacetime) (r : ℝ) {σ ν : Fin 4}
    (h : σ ≠ ν) :
    S.frameRicciTensor r σ ν = 0 := by
  rw [frameRicciTensor_eq]
  fin_cases σ <;> fin_cases ν <;> simp [minkowskiMetric4_apply] at h ⊢

/-- Diagonal frame components of `G`: `G_{tt} = Λ`, `G_{rr} = G_{θθ} = G_{φφ} = -Λ`. -/
lemma frameEinstein_diag (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    S.frameEinstein r 0 0 = S.Λ ∧ S.frameEinstein r 1 1 = -S.Λ ∧
      S.frameEinstein r 2 2 = -S.Λ ∧ S.frameEinstein r 3 3 = -S.Λ := by
  have h0 : S.frameEinstein r 0 0 = S.Λ := by rw [frameEinstein_eq]; simp
  have h1 : S.frameEinstein r 1 1 = -S.Λ := by rw [frameEinstein_eq]; simp
  have h2 : S.frameEinstein r 2 2 = -S.Λ := by rw [frameEinstein_eq]; simp
  have h3 : S.frameEinstein r 3 3 = -S.Λ := by rw [frameEinstein_eq]; simp
  exact ⟨h0, h1, h2, h3⟩

/-!

## D. Vacuum limit at `Λ = 0`

Setting the cosmological constant `Λ = 0` specializes the Einstein space to the Ricci-flat
Schwarzschild vacuum exterior.

-/

/-- At `Λ = 0`, the frame Ricci tensor vanishes: Schwarzschild is Ricci flat. -/
lemma vacuum_ricci_zero (S : SchwarzschildDeSitterSpacetime) (hΛ : S.Λ = 0) (r : ℝ)
    (σ ν : Fin 4) :
    S.frameRicciTensor r σ ν = 0 := by
  rw [frameRicciTensor_eq, hΛ]
  ring

/-- At `Λ = 0`, the frame scalar curvature vanishes. -/
lemma vacuum_scalar_zero (S : SchwarzschildDeSitterSpacetime) (hΛ : S.Λ = 0) (r : ℝ) :
    S.frameScalarCurvature r = 0 := by
  rw [frameScalar_eq, hΛ]
  ring

/-- At `Λ = 0`, the frame Einstein tensor vanishes: Schwarzschild is a vacuum solution. -/
lemma vacuum_einstein_zero (S : SchwarzschildDeSitterSpacetime) (hΛ : S.Λ = 0) (r : ℝ)
    (i j : Fin 4) :
    S.frameEinstein r i j = 0 := by
  rw [frameEinstein_eq, hΛ]
  ring

/-!

## E. Conservation of the frame Einstein tensor

Because the frame Ricci tensor `Λ η` and scalar curvature `4 Λ` are constant, all frame
derivatives vanish and the contracted Bianchi identity holds identically.

-/

/-- The frame derivatives of the Schwarzschild–de Sitter Einstein space: since `Ric = Λ η`
and `R = 4 Λ` are constant in the orthonormal frame, all frame derivatives vanish. -/
noncomputable def frameCurvatureDerivatives : CurvatureDerivatives where
  dRic := fun _ _ _ => 0
  dS := fun _ => 0

/-- The contracted Bianchi identity holds for the frame Einstein space without assumption. -/
lemma frame_bianchi :
    ∀ b, (∑ a, minkowskiMetric4 a a * frameCurvatureDerivatives.dRic a a b)
      = (1 / 2) * frameCurvatureDerivatives.dS b := by
  intro b
  simp [frameCurvatureDerivatives]

/-- The frame Einstein tensor of Schwarzschild–de Sitter is conserved (`∇ · G = 0`), proved
from `frame_bianchi`. -/
lemma frame_einstein_conserved (b : Fin 4) :
    inertialDivergence (CurvatureDerivatives.einsteinDeriv frameCurvatureDerivatives) b = 0 :=
  inertialDivergence_einstein_eq_zero frameCurvatureDerivatives frame_bianchi b

end SchwarzschildDeSitterSpacetime

end SchwarzschildDeSitter

end GeneralRelativity
