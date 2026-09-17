/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.DimUncertainty.D8_Szego

/-!
# D9 — Monotonía estricta de `C_Nava` y `deltaGeom`

Sin barrido numérico: `CNava` (y por tanto `deltaGeom`) crece
estrictamente para toda dimensión `d ≥ 4`. En particular, `d = 4` es
el mínimo global de la cola `d ≥ 4` y cada valor finito se aproxima a
`Cinf` estrictamente por debajo (`CNava_lt_Cinf`, `deltaGeom_lt_deltaInf`).

La prueba no supone que `π` sea racional. Las llamadas a `ring`
certifican únicamente identidades algebraicas formales con `π` como
elemento real simbólico. El signo estricto de la derivada se obtiene
mediante cotas formales `3 < π < 22/7`, cotas de Taylor verificadas y
un certificado polinómico de Bernstein de que el resto es
estrictamente negativo en la caja compacta correspondiente.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Gnomon

private lemma sin_taylor_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x :=
  Real.sin_ge_sub_cube hx

private lemma cos_taylor_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hderiv : ∀ t : ℝ, deriv f t = -t + t ^ 3 / 6 + Real.sin t := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have hs := sin_taylor_lower ht.le
    nlinarith
  have h := hmono (by simp) hx hx
  simp only [f, Real.cos_zero] at h
  nlinarith

private lemma sin_taylor_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hderiv : ∀ t : ℝ, deriv f t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have hc := cos_taylor_upper ht.le
    nlinarith
  have h := hmono (by simp) hx hx
  simp only [f, Real.sin_zero] at h
  nlinarith

private lemma cos_taylor_lower {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t =>
    Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720
  have hderiv : ∀ t : ℝ,
      deriv f t = -Real.sin t + t - t ^ 3 / 6 + t ^ 5 / 120 := by
    intro t
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv]
    have hs := sin_taylor_upper ht.le
    nlinarith
  have h := hmono (by simp) hx hx
  simp only [f, Real.cos_zero] at h
  nlinarith

/- A rational Bernstein-box certificate for the polynomial remainder used
below.  The box is `0 ≤ y ≤ 1/5`, `3 ≤ p ≤ 22/7`. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private lemma remainder_poly_neg {y p : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 5)
    (hp0 : 3 ≤ p) (hp1 : p ≤ 22 / 7) :
    (5 * p ^ 12 * y ^ 12 - 180 * p ^ 10 * y ^ 10 +
      1880 * p ^ 8 * y ^ 8 - 160 * p ^ 8 * y ^ 6 +
      160 * p ^ 8 * y ^ 5 - 7552 * p ^ 6 * y ^ 6 -
      384 * p ^ 6 * y ^ 5 + 2048 * p ^ 6 * y ^ 4 -
      2144 * p ^ 6 * y ^ 3 + 6720 * p ^ 4 * y ^ 4 +
      7680 * p ^ 4 * y ^ 3 - 5760 * p ^ 4 * y ^ 2 +
      7680 * p ^ 4 * y + 34560 * p ^ 2 * y ^ 2 -
      46080 * p ^ 2 * y - 11520 * p ^ 2 + 69120) / 5760 < 0 := by
  let u : ℝ := 5 * y
  let v : ℝ := 7 * p - 21
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : 0 ≤ 1 - u := by dsimp [u]; norm_num at hy1 ⊢; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hv1 : 0 ≤ 1 - v := by dsimp [v]; norm_num at hp1 ⊢; linarith
  have hb_0_0 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_0_1 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_0_2 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_0_3 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_0_4 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_0_5 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_0_6 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_0_7 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_0_8 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_0_9 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_0_10 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_0_11 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_0_12 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_1_0 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_1_1 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_1_2 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_1_3 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_1_4 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_1_5 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_1_6 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_1_7 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_1_8 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_1_9 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_1_10 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_1_11 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_1_12 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_2_0 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_2_1 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_2_2 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_2_3 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_2_4 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_2_5 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_2_6 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_2_7 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_2_8 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_2_9 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_2_10 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_2_11 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_2_12 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_3_0 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_3_1 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_3_2 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_3_3 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_3_4 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_3_5 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_3_6 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_3_7 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_3_8 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_3_9 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_3_10 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_3_11 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_3_12 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_4_0 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_4_1 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_4_2 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_4_3 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_4_4 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_4_5 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_4_6 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_4_7 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_4_8 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_4_9 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_4_10 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_4_11 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_4_12 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_5_0 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_5_1 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_5_2 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_5_3 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_5_4 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_5_5 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_5_6 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_5_7 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_5_8 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_5_9 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_5_10 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_5_11 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_5_12 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_6_0 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_6_1 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_6_2 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_6_3 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_6_4 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_6_5 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_6_6 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_6_7 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_6_8 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_6_9 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_6_10 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_6_11 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_6_12 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_7_0 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_7_1 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_7_2 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_7_3 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_7_4 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_7_5 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_7_6 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_7_7 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_7_8 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_7_9 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_7_10 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_7_11 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_7_12 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_8_0 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_8_1 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_8_2 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_8_3 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_8_4 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_8_5 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_8_6 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_8_7 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_8_8 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_8_9 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_8_10 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_8_11 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_8_12 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_9_0 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_9_1 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_9_2 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_9_3 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_9_4 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_9_5 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_9_6 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_9_7 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_9_8 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_9_9 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_9_10 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_9_11 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_9_12 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_10_0 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_10_1 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_10_2 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_10_3 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_10_4 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_10_5 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_10_6 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_10_7 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_10_8 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_10_9 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_10_10 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_10_11 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_10_12 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_11_0 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_11_1 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_11_2 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_11_3 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_11_4 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_11_5 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_11_6 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_11_7 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_11_8 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_11_9 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_11_10 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_11_11 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_11_12 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_12_0 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_12_1 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_12_2 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_12_3 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_12_4 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_12_5 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_12_6 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_12_7 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_12_8 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_12_9 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_12_10 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_12_11 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_12_12 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  dsimp [u, v] at hb_0_0 hb_0_1 hb_0_2 hb_0_3 hb_0_4 hb_0_5 hb_0_6 hb_0_7 hb_0_8 hb_0_9 hb_0_10 hb_0_11 hb_0_12 hb_1_0 hb_1_1 hb_1_2 hb_1_3 hb_1_4 hb_1_5 hb_1_6 hb_1_7 hb_1_8 hb_1_9 hb_1_10 hb_1_11 hb_1_12 hb_2_0 hb_2_1 hb_2_2 hb_2_3 hb_2_4 hb_2_5 hb_2_6 hb_2_7 hb_2_8 hb_2_9 hb_2_10 hb_2_11 hb_2_12 hb_3_0 hb_3_1 hb_3_2 hb_3_3 hb_3_4 hb_3_5 hb_3_6 hb_3_7 hb_3_8 hb_3_9 hb_3_10 hb_3_11 hb_3_12 hb_4_0 hb_4_1 hb_4_2 hb_4_3 hb_4_4 hb_4_5 hb_4_6 hb_4_7 hb_4_8 hb_4_9 hb_4_10 hb_4_11 hb_4_12 hb_5_0 hb_5_1 hb_5_2 hb_5_3 hb_5_4 hb_5_5 hb_5_6 hb_5_7 hb_5_8 hb_5_9 hb_5_10 hb_5_11 hb_5_12 hb_6_0 hb_6_1 hb_6_2 hb_6_3 hb_6_4 hb_6_5 hb_6_6 hb_6_7 hb_6_8 hb_6_9 hb_6_10 hb_6_11 hb_6_12 hb_7_0 hb_7_1 hb_7_2 hb_7_3 hb_7_4 hb_7_5 hb_7_6 hb_7_7 hb_7_8 hb_7_9 hb_7_10 hb_7_11 hb_7_12 hb_8_0 hb_8_1 hb_8_2 hb_8_3 hb_8_4 hb_8_5 hb_8_6 hb_8_7 hb_8_8 hb_8_9 hb_8_10 hb_8_11 hb_8_12 hb_9_0 hb_9_1 hb_9_2 hb_9_3 hb_9_4 hb_9_5 hb_9_6 hb_9_7 hb_9_8 hb_9_9 hb_9_10 hb_9_11 hb_9_12 hb_10_0 hb_10_1 hb_10_2 hb_10_3 hb_10_4 hb_10_5 hb_10_6 hb_10_7 hb_10_8 hb_10_9 hb_10_10 hb_10_11 hb_10_12 hb_11_0 hb_11_1 hb_11_2 hb_11_3 hb_11_4 hb_11_5 hb_11_6 hb_11_7 hb_11_8 hb_11_9 hb_11_10 hb_11_11 hb_11_12 hb_12_0 hb_12_1 hb_12_2 hb_12_3 hb_12_4 hb_12_5 hb_12_6 hb_12_7 hb_12_8 hb_12_9 hb_12_10 hb_12_11 hb_12_12 ⊢
  ring_nf at hb_0_0 hb_0_1 hb_0_2 hb_0_3 hb_0_4 hb_0_5 hb_0_6 hb_0_7 hb_0_8 hb_0_9 hb_0_10 hb_0_11 hb_0_12 hb_1_0 hb_1_1 hb_1_2 hb_1_3 hb_1_4 hb_1_5 hb_1_6 hb_1_7 hb_1_8 hb_1_9 hb_1_10 hb_1_11 hb_1_12 hb_2_0 hb_2_1 hb_2_2 hb_2_3 hb_2_4 hb_2_5 hb_2_6 hb_2_7 hb_2_8 hb_2_9 hb_2_10 hb_2_11 hb_2_12 hb_3_0 hb_3_1 hb_3_2 hb_3_3 hb_3_4 hb_3_5 hb_3_6 hb_3_7 hb_3_8 hb_3_9 hb_3_10 hb_3_11 hb_3_12 hb_4_0 hb_4_1 hb_4_2 hb_4_3 hb_4_4 hb_4_5 hb_4_6 hb_4_7 hb_4_8 hb_4_9 hb_4_10 hb_4_11 hb_4_12 hb_5_0 hb_5_1 hb_5_2 hb_5_3 hb_5_4 hb_5_5 hb_5_6 hb_5_7 hb_5_8 hb_5_9 hb_5_10 hb_5_11 hb_5_12 hb_6_0 hb_6_1 hb_6_2 hb_6_3 hb_6_4 hb_6_5 hb_6_6 hb_6_7 hb_6_8 hb_6_9 hb_6_10 hb_6_11 hb_6_12 hb_7_0 hb_7_1 hb_7_2 hb_7_3 hb_7_4 hb_7_5 hb_7_6 hb_7_7 hb_7_8 hb_7_9 hb_7_10 hb_7_11 hb_7_12 hb_8_0 hb_8_1 hb_8_2 hb_8_3 hb_8_4 hb_8_5 hb_8_6 hb_8_7 hb_8_8 hb_8_9 hb_8_10 hb_8_11 hb_8_12 hb_9_0 hb_9_1 hb_9_2 hb_9_3 hb_9_4 hb_9_5 hb_9_6 hb_9_7 hb_9_8 hb_9_9 hb_9_10 hb_9_11 hb_9_12 hb_10_0 hb_10_1 hb_10_2 hb_10_3 hb_10_4 hb_10_5 hb_10_6 hb_10_7 hb_10_8 hb_10_9 hb_10_10 hb_10_11 hb_10_12 hb_11_0 hb_11_1 hb_11_2 hb_11_3 hb_11_4 hb_11_5 hb_11_6 hb_11_7 hb_11_8 hb_11_9 hb_11_10 hb_11_11 hb_11_12 hb_12_0 hb_12_1 hb_12_2 hb_12_3 hb_12_4 hb_12_5 hb_12_6 hb_12_7 hb_12_8 hb_12_9 hb_12_10 hb_12_11 hb_12_12 ⊢
  linarith [hb_0_0, hb_0_1, hb_0_2, hb_0_3, hb_0_4, hb_0_5, hb_0_6, hb_0_7, hb_0_8, hb_0_9, hb_0_10, hb_0_11, hb_0_12, hb_1_0, hb_1_1, hb_1_2, hb_1_3, hb_1_4, hb_1_5, hb_1_6, hb_1_7, hb_1_8, hb_1_9, hb_1_10, hb_1_11, hb_1_12, hb_2_0, hb_2_1, hb_2_2, hb_2_3, hb_2_4, hb_2_5, hb_2_6, hb_2_7, hb_2_8, hb_2_9, hb_2_10, hb_2_11, hb_2_12, hb_3_0, hb_3_1, hb_3_2, hb_3_3, hb_3_4, hb_3_5, hb_3_6, hb_3_7, hb_3_8, hb_3_9, hb_3_10, hb_3_11, hb_3_12, hb_4_0, hb_4_1, hb_4_2, hb_4_3, hb_4_4, hb_4_5, hb_4_6, hb_4_7, hb_4_8, hb_4_9, hb_4_10, hb_4_11, hb_4_12, hb_5_0, hb_5_1, hb_5_2, hb_5_3, hb_5_4, hb_5_5, hb_5_6, hb_5_7, hb_5_8, hb_5_9, hb_5_10, hb_5_11, hb_5_12, hb_6_0, hb_6_1, hb_6_2, hb_6_3, hb_6_4, hb_6_5, hb_6_6, hb_6_7, hb_6_8, hb_6_9, hb_6_10, hb_6_11, hb_6_12, hb_7_0, hb_7_1, hb_7_2, hb_7_3, hb_7_4, hb_7_5, hb_7_6, hb_7_7, hb_7_8, hb_7_9, hb_7_10, hb_7_11, hb_7_12, hb_8_0, hb_8_1, hb_8_2, hb_8_3, hb_8_4, hb_8_5, hb_8_6, hb_8_7, hb_8_8, hb_8_9, hb_8_10, hb_8_11, hb_8_12, hb_9_0, hb_9_1, hb_9_2, hb_9_3, hb_9_4, hb_9_5, hb_9_6, hb_9_7, hb_9_8, hb_9_9, hb_9_10, hb_9_11, hb_9_12, hb_10_0, hb_10_1, hb_10_2, hb_10_3, hb_10_4, hb_10_5, hb_10_6, hb_10_7, hb_10_8, hb_10_9, hb_10_10, hb_10_11, hb_10_12, hb_11_0, hb_11_1, hb_11_2, hb_11_3, hb_11_4, hb_11_5, hb_11_6, hb_11_7, hb_11_8, hb_11_9, hb_11_10, hb_11_11, hb_11_12, hb_12_0, hb_12_1, hb_12_2, hb_12_3, hb_12_4, hb_12_5, hb_12_6, hb_12_7, hb_12_8, hb_12_9, hb_12_10, hb_12_11, hb_12_12]

/-- Continuous angular form of the exact finite coherence squared. -/
private noncomputable def coherenceSqAngle (x : ℝ) : ℝ :=
  ((Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 + 8 * x / Real.pi) / 3) *
      Real.tan x ^ 2 - 2 + 4 * x / Real.pi

private lemma CNavaSq_eq_coherenceSqAngle (d : ℕ) (hd : 4 ≤ d) :
    CNavaSq d = coherenceSqAngle (theta d) := by
  have hN : Nreal d ≠ 0 := by unfold Nreal; positivity
  have htpos : 0 < theta d := by unfold theta Nreal; positivity
  have htlt : theta d < Real.pi / 2 := by
    unfold theta Nreal
    rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < (d:ℝ) + 1) (by norm_num : (0:ℝ) < 2)]
    nlinarith [show (4 : ℝ) ≤ d by exact_mod_cast hd, Real.pi_pos]
  have hcos : Real.cos (theta d) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, htlt⟩).ne'
  have htne : theta d ≠ 0 := htpos.ne'
  have hpiθ : Real.pi = theta d * Nreal d := by
    unfold theta; field_simp
  have hpyth : Real.sin (theta d) ^ 2 = 1 - Real.cos (theta d) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (theta d)
    linarith
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [CNavaSq, coherenceSqAngle, Real.tan_eq_sin_div_cos, hpiθ]
  unfold Nreal
  field_simp [hcos, htne, hd1]
  rw [hpyth]
  ring

private lemma hasDerivAt_coherenceSqAngle {x : ℝ}
    (hx : x ≠ 0) (hcos : Real.cos x ≠ 0) :
    HasDerivAt coherenceSqAngle
      (((-2 * Real.pi ^ 2 / x ^ 3 + 2 * Real.pi / x ^ 2 + 8 / Real.pi) *
          Real.sin x ^ 2 * Real.cos x +
        2 * (Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 +
          8 * x / Real.pi) * Real.sin x +
        12 / Real.pi * Real.cos x ^ 3) /
        (3 * Real.cos x ^ 3)) x := by
  unfold coherenceSqAngle
  have htan : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x := Real.hasDerivAt_tan hcos
  have da := (hasDerivAt_const x (Real.pi ^ 2)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  have db := (hasDerivAt_const x (2 * Real.pi)).div (hasDerivAt_id x) hx
  have dab := da.sub db
  have dabc := dab.sub (hasDerivAt_const x (4 : ℝ))
  have dd := ((hasDerivAt_const x (8 : ℝ)).mul (hasDerivAt_id x)).div_const Real.pi
  have dQ := dabc.add dd
  have dQdiv3 := dQ.div_const 3
  have dtansq := htan.pow 2
  have dmul := dQdiv3.mul dtansq
  have dsub2 := dmul.sub (hasDerivAt_const x (2 : ℝ))
  have de := ((hasDerivAt_const x (4 : ℝ)).mul (hasDerivAt_id x)).div_const Real.pi
  have dfinal := dsub2.add de
  refine dfinal.congr_deriv ?_
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.div_apply]
  field_simp [hx, Real.pi_ne_zero]
  have hsin : Real.sin x = Real.tan x * Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  rw [hsin]
  ring

set_option maxHeartbeats 1000000 in
private lemma deriv_coherenceSqAngle_neg {x : ℝ}
    (hx0 : 0 < x) (hx5 : x ≤ Real.pi / 5) :
    deriv coherenceSqAngle x < 0 := by
  have hxhalf : x < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hxone : x ≤ 1 := by
    have hpilt : Real.pi < (4 : ℝ) := Real.pi_lt_four
    nlinarith
  have hcospos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hxhalf⟩
  have hspos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by nlinarith [Real.pi_pos])
  let y : ℝ := x / Real.pi
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy5 : y ≤ 1 / 5 := by
    dsimp [y]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpi22 : Real.pi ≤ (22 / 7 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hpoly := remainder_poly_neg hy0 hy5 hpi3 hpi22
  let sl : ℝ := x - x ^ 3 / 6
  let su : ℝ := x - x ^ 3 / 6 + x ^ 5 / 120
  let cl : ℝ := 1 - x ^ 2 / 2
  let cu : ℝ := 1 - x ^ 2 / 2 + x ^ 4 / 24
  let q : ℝ := Real.pi ^ 2 / x ^ 2 - 2 * Real.pi / x - 4 +
    8 * x / Real.pi
  let qp : ℝ := -2 * Real.pi ^ 2 / x ^ 3 + 2 * Real.pi / x ^ 2 +
    8 / Real.pi
  have hsl : sl ≤ Real.sin x := by
    simpa [sl] using sin_taylor_lower hx0.le
  have hsu : Real.sin x ≤ su := by
    simpa [su] using sin_taylor_upper hx0.le
  have hcl : cl ≤ Real.cos x := by
    simpa [cl] using Real.one_sub_sq_div_two_le_cos (x := x)
  have hcu : Real.cos x ≤ cu := by
    simpa [cu] using cos_taylor_upper hx0.le
  have hsl0 : 0 < sl := by
    dsimp [sl]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hxpow : x ^ 3 = x * x ^ 2 := by ring
    rw [hxpow]
    nlinarith
  have hcl0 : 0 < cl := by
    dsimp [cl]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    nlinarith
  have hcu0 : 0 < cu := lt_of_lt_of_le hcospos hcu
  have hqpos : 0 < q := by
    have hypos : 0 < y := by dsimp [y]; positivity
    have hy_sq : y ^ 2 ≤ (1 / 5 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hy0 hy5 2
    have hbase : 0 < 1 - 2 * y - 4 * y ^ 2 + 8 * y ^ 3 := by
      have hy3 : 0 ≤ y ^ 3 := by positivity
      nlinarith
    dsimp [q, y] at hbase ⊢
    field_simp [hx0.ne', Real.pi_ne_zero] at hbase ⊢
    nlinarith [sq_nonneg x, sq_nonneg Real.pi]
  have hqpneg : qp < 0 := by
    have hypos : 0 < y := by dsimp [y]; positivity
    have hy3 : y ^ 3 ≤ (1 / 5 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hy0 hy5 3
    have hbase : -2 + 2 * y + 8 * y ^ 3 < 0 := by nlinarith
    dsimp [qp, y] at hbase ⊢
    field_simp [hx0.ne', Real.pi_ne_zero] at hbase ⊢
    nlinarith [sq_nonneg x, sq_nonneg Real.pi]
  have hsq : sl ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ hsl0.le hsl 2
  have hprod : sl ^ 2 * cl ≤ Real.sin x ^ 2 * Real.cos x := by
    exact mul_le_mul hsq hcl hcl0.le (sq_nonneg _)
  have hcube : Real.cos x ^ 3 ≤ cu ^ 3 :=
    pow_le_pow_left₀ hcospos.le hcu 3
  have hupper :
      qp * (Real.sin x ^ 2 * Real.cos x) + 2 * q * Real.sin x +
          12 / Real.pi * Real.cos x ^ 3 ≤
        qp * (sl ^ 2 * cl) + 2 * q * su +
          12 / Real.pi * cu ^ 3 := by
    have h1 := mul_le_mul_of_nonpos_left hprod hqpneg.le
    have h2 := mul_le_mul_of_nonneg_left hsu (by positivity : 0 ≤ 2 * q)
    have h3 := mul_le_mul_of_nonneg_left hcube
      (by positivity : 0 ≤ 12 / Real.pi)
    linarith
  have hrem : qp * (sl ^ 2 * cl) + 2 * q * su +
      12 / Real.pi * cu ^ 3 < 0 := by
    have heq :
        Real.pi * (qp * (sl ^ 2 * cl) + 2 * q * su +
          12 / Real.pi * cu ^ 3) =
        (5 * Real.pi ^ 12 * y ^ 12 - 180 * Real.pi ^ 10 * y ^ 10 +
          1880 * Real.pi ^ 8 * y ^ 8 - 160 * Real.pi ^ 8 * y ^ 6 +
          160 * Real.pi ^ 8 * y ^ 5 - 7552 * Real.pi ^ 6 * y ^ 6 -
          384 * Real.pi ^ 6 * y ^ 5 + 2048 * Real.pi ^ 6 * y ^ 4 -
          2144 * Real.pi ^ 6 * y ^ 3 + 6720 * Real.pi ^ 4 * y ^ 4 +
          7680 * Real.pi ^ 4 * y ^ 3 - 5760 * Real.pi ^ 4 * y ^ 2 +
          7680 * Real.pi ^ 4 * y + 34560 * Real.pi ^ 2 * y ^ 2 -
          46080 * Real.pi ^ 2 * y - 11520 * Real.pi ^ 2 + 69120) / 5760 := by
      dsimp [qp, q, sl, su, cl, cu, y]
      field_simp [hx0.ne', Real.pi_ne_zero]
      ring
    rw [← heq] at hpoly
    nlinarith [hpoly, Real.pi_pos]
  have hnum := hupper.trans_lt hrem
  rw [(hasDerivAt_coherenceSqAngle hx0.ne' hcospos.ne').deriv]
  dsimp [qp, q] at hnum ⊢
  apply div_neg_of_neg_of_pos _ (by positivity)
  nlinarith [hnum]

private lemma coherenceSqAngle_strictAntiOn :
    StrictAntiOn coherenceSqAngle (Set.Ioc 0 (Real.pi / 5)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (Real.pi / 5))
  · intro x hx
    obtain ⟨hx0, hx5⟩ := hx
    have hxhalf : x < Real.pi / 2 := by nlinarith [Real.pi_pos, hx5]
    have hcospos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxhalf⟩
    exact (hasDerivAt_coherenceSqAngle hx0.ne' hcospos.ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact deriv_coherenceSqAngle_neg hx.1 hx.2.le

/-- The exact finite coherence squared is strictly increasing from dimension four onward. -/
theorem CNavaSq_strictMonoOn_ge_four :
    StrictMonoOn CNavaSq {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  rw [CNavaSq_eq_coherenceSqAngle a ha,
    CNavaSq_eq_coherenceSqAngle b hb]
  have hta0 : 0 < theta a := by unfold theta Nreal; positivity
  have htb0 : 0 < theta b := by unfold theta Nreal; positivity
  have hta5 : theta a ≤ Real.pi / 5 := by
    unfold theta Nreal
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)]
    have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [Real.pi_pos]
  have htb5 : theta b ≤ Real.pi / 5 := by
    unfold theta Nreal
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)]
    have hbR : (4 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [Real.pi_pos]
  have htheta : theta b < theta a := by
    unfold theta Nreal
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    nlinarith [Real.pi_pos]
  exact coherenceSqAngle_strictAntiOn ⟨htb0, htb5⟩ ⟨hta0, hta5⟩ htheta

/-- The exact (square-rooted) finite coherence is strictly increasing from dimension four. -/
theorem CNava_strictMonoOn_ge_four :
    StrictMonoOn CNava {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  unfold CNava
  exact Real.sqrt_lt_sqrt (zero_le_one.trans (one_lt_CNavaSq a ha).le)
    (CNavaSq_strictMonoOn_ge_four ha hb hab)

/-- The geometric defect is strictly increasing from dimension four onward. -/
theorem deltaGeom_strictMonoOn_ge_four :
    StrictMonoOn deltaGeom {d : ℕ | 4 ≤ d} := by
  intro a ha b hb hab
  simpa [deltaGeom] using CNava_strictMonoOn_ge_four ha hb hab

/-- Dimension four is the exact global minimum of finite coherence on the physical tail. -/
theorem CNava_four_le (d : ℕ) (hd : 4 ≤ d) : CNava 4 ≤ CNava d := by
  rcases eq_or_lt_of_le hd with h | h
  · simp [h]
  · have hmem4 : (4 : ℕ) ∈ {d : ℕ | 4 ≤ d} := le_refl 4
    have hmemd : d ∈ {d : ℕ | 4 ≤ d} := hd
    exact (CNava_strictMonoOn_ge_four hmem4 hmemd h).le

/-- Dimension four is the exact global minimum of the geometric defect on the physical tail. -/
theorem deltaGeom_four_le (d : ℕ) (hd : 4 ≤ d) :
    deltaGeom 4 ≤ deltaGeom d := by
  simpa [deltaGeom] using CNava_four_le d hd

/-- The squared geometric defect also has its exact global minimum at dimension four. -/
theorem deltaGeom_sq_four_le (d : ℕ) (hd : 4 ≤ d) :
    deltaGeom 4 ^ 2 ≤ deltaGeom d ^ 2 := by
  have h4 : 0 < deltaGeom 4 := by
    simpa [deltaGeom] using one_lt_CNava_of_four_le 4 (by omega)
  have hd0 : 0 < deltaGeom d := by
    simpa [deltaGeom] using one_lt_CNava_of_four_le d hd
  nlinarith [deltaGeom_four_le d hd]

private theorem CNava_tail_strictMono :
    StrictMono (fun n : ℕ => CNava (n + 4)) := by
  intro a b hab
  have hmemA : a + 4 ∈ {d : ℕ | 4 ≤ d} := Nat.le_add_left 4 a
  have hmemB : b + 4 ∈ {d : ℕ | 4 ≤ d} := Nat.le_add_left 4 b
  have hlt : a + 4 < b + 4 := by omega
  exact CNava_strictMonoOn_ge_four hmemA hmemB hlt

private theorem CNava_tail_tendsto :
    Tendsto (fun n : ℕ => CNava (n + 4)) atTop (𝓝 Cinf) := by
  exact (Filter.tendsto_add_atTop_iff_nat 4).2 limite_nava_szego_CNava

/-- Every finite physical coherence lies strictly below its Nava--Szegő attractor. -/
theorem CNava_lt_Cinf (d : ℕ) (hd : 4 ≤ d) : CNava d < Cinf := by
  let n := d - 4
  have hdn : n + 4 = d := by dsimp [n]; omega
  have hstep : CNava (n + 4) < CNava ((n + 1) + 4) :=
    CNava_tail_strictMono (Nat.lt_succ_self n)
  have hlimit : CNava ((n + 1) + 4) ≤ Cinf :=
    CNava_tail_strictMono.monotone.ge_of_tendsto CNava_tail_tendsto (n + 1)
  rw [← hdn]
  exact hstep.trans_le hlimit

/-- Every finite physical defect approaches the Szegő defect strictly from below. -/
theorem deltaGeom_lt_deltaInf (d : ℕ) (hd : 4 ≤ d) :
    deltaGeom d < deltaInf := by
  simpa [deltaGeom, deltaInf] using CNava_lt_Cinf d hd

end Gnomon
