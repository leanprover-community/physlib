/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Schwarzschild.Basic
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Tensors.RicciTensor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Schwarzschild curvature in the orthonormal frame

The Schwarzschild Weyl tensor, Ricci flatness, Kretschmann scalar, and Newtonian tidal potential
in the orthonormal frame `(t, r, θ, φ)`.

## i. Overview

In the orthonormal frame `(t, r, θ, φ)`, the Schwarzschild curvature is a purely electric Weyl
tensor determined by `E = diag(0, -2k, k, k)` with `k = M / r³`:

`R_{ijlm} = δ_{il} E_{jm} - δ_{im} E_{jl} - δ_{jl} E_{im} + δ_{jm} E_{il}`.

This module builds that tensor as a `RiemannTensor 4`, proves its Ricci flatness against
`minkowski` (via the general Ricci contraction), computes its sum of squares `48 k²` (yielding
the Kretschmann scalar `48 M² / r⁶` for any `SchwarzschildSpacetime`), proves it is purely
electric, and verifies that the static Newtonian potential `Φ = -M / r` has Hessian eigenvalues
`electricPart (M / r³)` matching those extracted directly from `SchwarzschildSpacetime.metric`.

## ii. Key results

- `electricPart`, `electricPart_symm`, `electricPart_trace` : trace-free static Weyl electric
  matrix `diag(0, -2k, k, k)`.
- `schwarzschild`, `ricci_eq_zero`, `schwarzschild_frameKretschmannScalar_eq` : Schwarzschild
  frame curvature `RiemannTensor 4`, Ricci flatness, and frame sum of squares `48 k²`.
- `weyl_purely_electric` : every component with one temporal index vanishes.
- `SchwarzschildSpacetime.frameRiemann`, `SchwarzschildSpacetime.kretschmann_scalar`,
  `SchwarzschildSpacetime.tidalPart_eq_electricPart`,
  `SchwarzschildSpacetime.electricPart_from_metric` : Schwarzschild spacetime frame curvature,
  Kretschmann invariant `48 M² / r⁶`, tidal Hessian match, and metric electric eigenvalues.

## iii. Table of contents

- A. The electric Weyl tensor and frame curvature
- B. Ricci flatness, Kretschmann scalar, and purely electric property
- C. Tidal Hessian and electric eigenvalues for SchwarzschildSpacetime

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1-6.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 & Ch. 31.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Schwarzschild

/-!

## A. The electric Weyl tensor and frame curvature

In a static orthonormal frame `(t, r, θ, φ)` outside a spherical mass, tidal gravity is captured by
the trace-free electric part `E = diag(0, -2k, k, k)` of the Weyl tensor, with `k = M / r³`.

-/

/-- The electric part of a static Weyl tensor in the orthonormal frame `(t, r, θ, φ)`:
`diag(0, -2k, k, k)`, symmetric and trace free. -/
noncomputable def electricPart (k : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 0 else if i = 1 then -2 * k else k) else 0

/-- Symmetry of the electric Weyl matrix `diag(0, -2k, k, k)` for any tidal scale `k`. -/
lemma electricPart_symm (k : ℝ) (i j : Fin 4) :
    electricPart k i j = electricPart k j i := by
  fin_cases i <;> fin_cases j <;> simp [electricPart]

/-- The electric Weyl matrix `diag(0, -2k, k, k)` is trace-free for every tidal scale `k`. -/
lemma electricPart_trace (k : ℝ) : (∑ i, electricPart k i i) = 0 := by
  simp [electricPart, Fin.sum_univ_four]
  ring

/-- The Schwarzschild curvature in the orthonormal frame, with `k = M / r³` at a point: the
static Weyl tensor of electric part `E = diag(0, -2k, k, k)`. -/
noncomputable def schwarzschild (k : ℝ) : RiemannTensor 4 where
  comp := fun i j l m =>
    (if i = l then electricPart k j m else 0)
      - (if i = m then electricPart k j l else 0)
      - (if j = l then electricPart k i m else 0)
      + (if j = m then electricPart k i l else 0)
  skew_last := by
    intro i j l m
    ring
  pair_symm := by
    intro i j l m
    rw [electricPart_symm k m j, electricPart_symm k m i,
      electricPart_symm k l j, electricPart_symm k l i]
    simp only [eq_comm (a := l) (b := i), eq_comm (a := l) (b := j),
      eq_comm (a := m) (b := i), eq_comm (a := m) (b := j)]
    ring
  bianchi := by
    intro i j l m
    rw [electricPart_symm k l j, electricPart_symm k l m,
      electricPart_symm k m j]
    simp only [eq_comm (a := l) (b := j), eq_comm (a := m) (b := j),
      eq_comm (a := m) (b := l)]
    ring

/-!

## B. Ricci flatness, Kretschmann scalar, and purely electric property

Contracting `schwarzschild k` with the Minkowski frame metric yields zero Ricci tensor, while
squaring all 256 frame components yields `48 k²`.

-/

/-- Schwarzschild frame curvature is Ricci flat for every tidal-scale parameter `k`. -/
lemma ricci_eq_zero (k : ℝ) : ricci minkowski (schwarzschild k) = 0 := by
  ext i j
  rw [ricci_of_diag minkowski (schwarzschild k) (fun _ _ h => minkowski_ginv_offdiag h) i j]
  fin_cases i <;> fin_cases j
  all_goals simp [minkowski, schwarzschild, electricPart, Fin.sum_univ_four,
    two_mul, add_assoc]

/-- The frame Kretschmann sum of squares of `schwarzschild k` equals `48 k²`. -/
lemma schwarzschild_frameKretschmannScalar_eq (k : ℝ) :
    (schwarzschild k).frameKretschmannScalar = 48 * k ^ 2 := by
  simp [RiemannTensor.frameKretschmannScalar, schwarzschild, electricPart, Fin.sum_univ_four,
    two_mul, add_assoc]
  ring

/-- The Schwarzschild frame Weyl tensor is purely electric: for spatial `j, l, m`, every
component carrying exactly one temporal index vanishes. -/
lemma weyl_purely_electric (k : ℝ) (j l m : Fin 4) (hj : j ≠ 0) (hl : l ≠ 0)
    (hm : m ≠ 0) :
    (schwarzschild k).comp 0 j l m = 0 ∧ (schwarzschild k).comp j 0 l m = 0 ∧
      (schwarzschild k).comp j l 0 m = 0 ∧ (schwarzschild k).comp j l m 0 = 0 := by
  have h0j : (0 : Fin 4) ≠ j := fun h => hj h.symm
  have h0l : (0 : Fin 4) ≠ l := fun h => hl h.symm
  have h0m : (0 : Fin 4) ≠ m := fun h => hm h.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [schwarzschild, electricPart]

/-!

## C. Tidal Hessian and electric eigenvalues for SchwarzschildSpacetime

In the weak-field exterior region, the radial tidal eigenvalues `diag(0, -2M/r³, M/r³, M/r³)` of
a `SchwarzschildSpacetime` match both the Newtonian potential Hessian and the orthonormal-frame
components rescaled from the Schwarzschild coordinate metric.

-/

/-- The tidal Hessian of a static radial potential in the orthonormal frame `(t, r, θ, φ)`:
eigenvalues `0`, `Φ''`, `Φ'/r`, `Φ'/r`. -/
noncomputable def tidalPart (phiRR phiOverR : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 0 else if i = 1 then phiRR else phiOverR) else 0

namespace SchwarzschildSpacetime

/-- Orthonormal-frame Schwarzschild Weyl curvature tensor at radius `r`. -/
noncomputable def frameRiemann (S : SchwarzschildSpacetime) (r : ℝ) : RiemannTensor 4 :=
  schwarzschild (S.M / r ^ 3)

/-- The Schwarzschild Kretschmann scalar `48 M² / r⁶` in the orthonormal frame at radius `r`. -/
lemma kretschmann_scalar (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0) :
    (S.frameRiemann r).frameKretschmannScalar = 48 * S.M ^ 2 / r ^ 6 := by
  rw [frameRiemann, schwarzschild_frameKretschmannScalar_eq]
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  field_simp

/-- With `Φ = -M / r`, the Newtonian tidal tensor of `S` equals `electricPart (S.M / r³)`. -/
lemma tidalPart_eq_electricPart (S : SchwarzschildSpacetime) (r : ℝ) :
    tidalPart (-2 * S.M / r ^ 3) (S.M / r ^ 3) = electricPart (S.M / r ^ 3) := by
  funext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | (simp [tidalPart, electricPart]; ring)
    | simp [tidalPart, electricPart]

/-- Lowering `R^t{}_{rtr}` with `g_tt = -f` gives `-2M / r³`, the radial entry of
`electricPart (M / r³)`. -/
lemma electric_r_from_metric (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    -(S.metricFn r) * (2 * S.M / (r ^ 3 * S.metricFn r))
      = electricPart (S.M / r ^ 3) 1 1 := by
  have h11 : electricPart (S.M / r ^ 3) 1 1 = -(2 * S.M / r ^ 3) := by
    simp [electricPart]
    ring_nf
  rw [h11]
  field_simp

/-- Orthonormal-frame `θθ` tidal eigenvalue: `M / r³`, the `(2, 2)` entry of
`electricPart (M / r³)`. -/
lemma electric_thetatheta_from_metric (S : SchwarzschildSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    (S.metricFn r)⁻¹ * (r ^ 2)⁻¹ * (-(S.metricFn r) * (-S.M / r))
      = electricPart (S.M / r ^ 3) 2 2 := by
  have h22 : electricPart (S.M / r ^ 3) 2 2 = S.M / r ^ 3 := by
    simp [electricPart]
  rw [h22]
  field_simp

/-- Frame rescaling of `R_{tφtφ}` cancels the metric factors to give `M / r³`. -/
lemma framePhiPhi (S : SchwarzschildSpacetime) (r th : ℝ) (hr : r ≠ 0) (hf : S.metricFn r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (S.metricFn r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * ((S.M * S.metricFn r / r) * Real.sin th ^ 2)
      = S.M / r ^ 3 := by
  have h1 : (S.metricFn r)⁻¹ * S.metricFn r = 1 := inv_mul_cancel₀ hf
  have h2 : (r ^ 2 * Real.sin th ^ 2)⁻¹ * Real.sin th ^ 2 = 1 / r ^ 2 := by
    field_simp
  calc (S.metricFn r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * ((S.M * S.metricFn r / r) * Real.sin th ^ 2)
      = ((S.metricFn r)⁻¹ * S.metricFn r)
          * ((r ^ 2 * Real.sin th ^ 2)⁻¹ * Real.sin th ^ 2) * (S.M / r) := by
        ring
    _ = 1 * (1 / r ^ 2) * (S.M / r) := by rw [h1, h2]
    _ = S.M / r ^ 3 := by
        field_simp

/-- Orthonormal-frame `φφ` tidal eigenvalue: `M / r³`, the `(3, 3)` entry of
`electricPart (M / r³)`. -/
lemma electric_phiphi_from_metric (S : SchwarzschildSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (S.metricFn r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (S.M * S.metricFn r / r * Real.sin th ^ 2)
      = electricPart (S.M / r ^ 3) 3 3 := by
  have h33 : electricPart (S.M / r ^ 3) 3 3 = S.M / r ^ 3 := by
    simp [electricPart]
  rw [h33]
  exact S.framePhiPhi r th hr hf hsin

/-- The entire frame electric part of the Weyl tensor (`diag(0, -2M/r³, M/r³, M/r³)` plus all
seven vanishing entries) assembled from the Schwarzschild metric. -/
lemma electricPart_from_metric (S : SchwarzschildSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (-(S.metricFn r) * (2 * S.M / (r ^ 3 * S.metricFn r))
        = electricPart (S.M / r ^ 3) 1 1)
      ∧ ((S.metricFn r)⁻¹ * (r ^ 2)⁻¹ * (-(S.metricFn r) * (-S.M / r))
          = electricPart (S.M / r ^ 3) 2 2)
      ∧ ((S.metricFn r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
            * (S.M * S.metricFn r / r * Real.sin th ^ 2)
          = electricPart (S.M / r ^ 3) 3 3)
      ∧ electricPart (S.M / r ^ 3) 0 0 = 0
      ∧ electricPart (S.M / r ^ 3) 0 1 = 0
      ∧ electricPart (S.M / r ^ 3) 0 2 = 0
      ∧ electricPart (S.M / r ^ 3) 0 3 = 0
      ∧ electricPart (S.M / r ^ 3) 1 2 = 0
      ∧ electricPart (S.M / r ^ 3) 1 3 = 0
      ∧ electricPart (S.M / r ^ 3) 2 3 = 0 :=
  ⟨S.electric_r_from_metric r hr hf,
   S.electric_thetatheta_from_metric r hr hf,
   S.electric_phiphi_from_metric r th hr hf hsin,
   by simp [electricPart], by simp [electricPart], by simp [electricPart],
   by simp [electricPart], by simp [electricPart], by simp [electricPart],
   by simp [electricPart]⟩

end SchwarzschildSpacetime

end Schwarzschild

end GeneralRelativity
