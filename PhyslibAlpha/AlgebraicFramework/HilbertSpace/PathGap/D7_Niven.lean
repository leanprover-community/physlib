/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D2_Robertson

/-!
# D7 — Niven theorem: saturation only occurs at `d ∈ {2,3}`

Saturation trichotomy: the trigonometric equation

`cos²(π/(d+1)) = (d−1)/4`

— which is exactly the condition for Robertson's bound to saturate
on the fundamental mode of the discrete path — holds if and only if
`d = 2` or `d = 3`. There are no further natural solutions: the proof
distinguishes `d = 4` (explicit algebraic reductio) from `d ≥ 5`
(cosine bound, `Blindaje.R3_techo_coseno`). Consequently, for all
`d ≥ 4` the gap `C_Nava(d) − 1` is strictly positive (second half
of this file, `Constructor_DeltaGeom_Pos`).
-/

@[expose] public section

open Real

namespace Gnomon

/-- Seed `d=2`: exact unit saturation `cos²(π/3) = 1/4`. -/
theorem semilla_d2 : Real.cos (π / 3) ^ 2 = 1 / 4 := by
  rw [Real.cos_pi_div_three]; norm_num

/-- Seed `d=3`: exact unit saturation `cos²(π/4) = 1/2`. -/
theorem semilla_d3 : Real.cos (π / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_pi_div_four]
  rw [div_pow, sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  norm_num

/-- `d=4` does not admit unit saturation: `cos²(π/5) ≠ 3/4`. -/
theorem no_saturacion_d4 : Real.cos (π / 5) ^ 2 ≠ 3 / 4 := by
  rw [Real.cos_pi_div_five]
  intro h
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hs, hnn, h]

/-- NIVEN THEOREM (saturation trichotomy): for `d ≥ 2`,
`cos²(π/(d+1)) = (d−1)/4 ↔ d ∈ {2,3}`. -/
theorem saturacion_iff (d : ℕ) (hd : 2 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨h2, h3⟩ := hne
    rcases Nat.lt_or_ge d 5 with h5 | h5
    · have hd4 : d = 4 := by omega
      subst hd4
      have hc : ((4 : ℕ) : ℝ) + 1 = 5 := by norm_num
      rw [hc] at h
      have h34 : (((4 : ℕ) : ℝ) - 1) / 4 = 3 / 4 := by norm_num
      rw [h34] at h
      exact no_saturacion_d4 h
    · exact absurd h (ne_of_lt (Blindaje.R3_techo_coseno d h5))
  · rintro (rfl | rfl)
    · have hc : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
      rw [hc, semilla_d2]; norm_num
    · have hc : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
      rw [hc, semilla_d3]; norm_num

/-- The unit bound does not recover: for `d ≥ 4` saturation is impossible. -/
theorem no_reposición_saturacion_camino (d : ℕ) (hd : 4 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4 := by
  intro h
  have hsem : d = 2 ∨ d = 3 := (saturacion_iff d (by omega)).mp h
  omega

/-- Citable alias: the only saturation seeds are `d = 2` and `d = 3`. -/
theorem semillas_niven_unicas (d : ℕ) (hd : 2 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 → d = 2 ∨ d = 3 :=
  (saturacion_iff d hd).mp

theorem apertura_no_es_semilla_niven (d : ℕ) (hd : 4 ≤ d) :
    ¬ (d = 2 ∨ d = 3) := by
  omega

end Gnomon


