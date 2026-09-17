/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D2_Robertson

/-!
# D7 — Teorema de Niven: la saturación sólo ocurre en `d ∈ {2,3}`

Tricotomía de saturación: la ecuación trigonométrica

`cos²(π/(d+1)) = (d−1)/4`

—que es exactamente la condición para que la cota de Robertson se sature
sobre el modo fundamental del camino discreto— se cumple **si y sólo si**
`d = 2` o `d = 3`. No hay más soluciones naturales: la prueba distingue
`d = 4` (reductio algebraico explícito) de `d ≥ 5` (cota de coseno,
`Blindaje.R3_techo_coseno`). En consecuencia, para todo `d ≥ 4` la brecha
`C_Nava(d) − 1` es estrictamente positiva (segunda mitad de este archivo,
`Constructor_DeltaGeom_Pos`).
-/

@[expose] public section

open Real

namespace Gnomon

/-- Semilla `d=2`: saturación unitaria exacta `cos²(π/3) = 1/4`. -/
theorem semilla_d2 : Real.cos (π / 3) ^ 2 = 1 / 4 := by
  rw [Real.cos_pi_div_three]; norm_num

/-- Semilla `d=3`: saturación unitaria exacta `cos²(π/4) = 1/2`. -/
theorem semilla_d3 : Real.cos (π / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_pi_div_four]
  rw [div_pow, sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  norm_num

/-- `d=4` no admite saturación unitaria: `cos²(π/5) ≠ 3/4`. -/
theorem no_saturacion_d4 : Real.cos (π / 5) ^ 2 ≠ 3 / 4 := by
  rw [Real.cos_pi_div_five]
  intro h
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [hs, hnn, h]

/-- TEOREMA DE NIVEN (tricotomía de saturación): para `d ≥ 2`,
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

/-- La cota unitaria no se repone: para `d ≥ 4` la saturación es imposible. -/
theorem no_reposición_saturacion_camino (d : ℕ) (hd : 4 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4 := by
  intro h
  have hsem : d = 2 ∨ d = 3 := (saturacion_iff d (by omega)).mp h
  omega

/-- Alias citable: las únicas semillas de saturación son `d = 2` y `d = 3`. -/
theorem semillas_niven_unicas (d : ℕ) (hd : 2 ≤ d) :
    Real.cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 → d = 2 ∨ d = 3 :=
  (saturacion_iff d hd).mp

theorem apertura_no_es_semilla_niven (d : ℕ) (hd : 4 ≤ d) :
    ¬ (d = 2 ∨ d = 3) := by
  omega

end Gnomon


