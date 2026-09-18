/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Tactic.IntervalCases

/-!
# D8 — The Szegő limit and gap positivity

Defines the finite coherence constant `C_Nava(d)` (exact closed form
in `cos`/`sin` of `π/(d+1)`) and its gap `deltaGeom(d) = C_Nava(d) − 1`.
Two central results:

1. **Positivity** (`deltaGeom_pos_of_four_le`): `deltaGeom(d) > 0` for
   all `d ≥ 4`. Verified at `d = 4, 5` in exact closed form and `d ≥ 6`
   via certified Taylor bounds on sine and cosine — without appealing to
   any external numerical computation, only rational algebra and the
   `Real.pi_gt_d2`/`Real.pi_lt_d2` bounds from Mathlib.
2. **Szegő limit** (`limite_szego_CNava`): `C_Nava(d) → C_∞ = √(π²/3−2)`
   as `d → ∞` (as an `atTop` filter over the sequence of finite spaces,
   not as a new Hilbert space at `d = ∞`; see
   `infinito_no_es_dimension_sino_limite`). In particular
   `deltaInf = C_∞ − 1 > 0`, an exact consequence of `π > 3`.
-/

@[expose] public section

noncomputable section

open Real
open Filter
open scoped Topology

namespace Gnomon

/-! ## Closed form and asymptotic limit -/

/-- `N = d + 1`, notation for the path graph `pathGraph d`. -/
noncomputable def Nreal (d : ℕ) : ℝ := (d : ℝ) + 1

/-- Fundamental spectral angle `θ_d = π/(d+1)`. -/
noncomputable def theta (d : ℕ) : ℝ := π / Nreal d

/-- Exact closed form of `C_Nava(d)²`. -/
noncomputable def CNavaSq (d : ℕ) : ℝ :=
  2 * ((d : ℝ) - 1) / (Nreal d * Real.cos (theta d) ^ 2) *
    (((Nreal d ^ 2 + 2) / 6) * Real.sin (theta d) ^ 2 - 1)

/-- Finite coherence constant. -/
noncomputable def CNava (d : ℕ) : ℝ := Real.sqrt (CNavaSq d)

/-- Universal Szegő limit. -/
noncomputable def Cinf : ℝ := Real.sqrt (π ^ 2 / 3 - 2)

/-- Finite geometric defect `δ_geom(d) = C_Nava(d) - 1`. -/
noncomputable def deltaGeom (d : ℕ) : ℝ := CNava d - 1

/-- Asymptotic defect `δ_∞ = C_∞ - 1`. -/
noncomputable def deltaInf : ℝ := Cinf - 1

/-- Leading term of the Szegő expansion. -/
noncomputable def deltaSzegoPrincipal (d : ℕ) : ℝ :=
  deltaInf - Cinf / Nreal d

theorem CNavaSq_forma_cerrada (d : ℕ) :
    CNavaSq d =
      2 * ((d : ℝ) - 1) / (Nreal d * Real.cos (theta d) ^ 2) *
        (((Nreal d ^ 2 + 2) / 6) * Real.sin (theta d) ^ 2 - 1) := rfl

/-- The closed form rewritten via `sinc`. Removes the apparent
singularity and allows taking the limit in Lean. -/
theorem CNavaSq_forma_regularizada (d : ℕ) :
    CNavaSq d =
      2 * (1 - 2 / Nreal d) / Real.cos (theta d) ^ 2 *
        ((π ^ 2 * Real.sinc (theta d) ^ 2 +
          2 * Real.sin (theta d) ^ 2) / 6 - 1) := by
  have hN : Nreal d ≠ 0 := by
    unfold Nreal
    positivity
  have ht : theta d ≠ 0 := by
    unfold theta
    exact div_ne_zero Real.pi_ne_zero hN
  rw [CNavaSq, Real.sinc_of_ne_zero ht]
  unfold theta Nreal
  field_simp
  ring

theorem Nreal_tendsto_atTop : Tendsto Nreal atTop atTop := by
  unfold Nreal
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

theorem theta_tendsto_zero : Tendsto theta atTop (𝓝 0) := by
  unfold theta
  exact Nreal_tendsto_atTop.const_div_atTop π

private theorem CNavaSq_regularizada_tendsto :
    Tendsto
      (fun d : ℕ =>
        2 * (1 - 2 / Nreal d) / Real.cos (theta d) ^ 2 *
          ((π ^ 2 * Real.sinc (theta d) ^ 2 +
            2 * Real.sin (theta d) ^ 2) / 6 - 1))
      atTop (𝓝 (π ^ 2 / 3 - 2)) := by
  have hratio : Tendsto (fun d : ℕ => 1 - 2 / Nreal d) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub
      (Nreal_tendsto_atTop.const_div_atTop 2) using 1
    norm_num
  have hcos : Tendsto
      (fun d : ℕ => Real.cos (theta d) ^ 2) atTop (𝓝 1) := by
    simpa [Real.cos_zero] using
      (Real.continuous_cos.continuousAt.tendsto.comp theta_tendsto_zero).pow 2
  have hsinc : Tendsto
      (fun d : ℕ => Real.sinc (theta d) ^ 2) atTop (𝓝 1) := by
    simpa [Real.sinc_zero] using
      (Real.continuous_sinc.continuousAt.tendsto.comp theta_tendsto_zero).pow 2
  have hsin : Tendsto
      (fun d : ℕ => Real.sin (theta d) ^ 2) atTop (𝓝 0) := by
    simpa [Real.sin_zero] using
      (Real.continuous_sin.continuousAt.tendsto.comp theta_tendsto_zero).pow 2
  have hbracket : Tendsto
      (fun d : ℕ =>
        (π ^ 2 * Real.sinc (theta d) ^ 2 +
          2 * Real.sin (theta d) ^ 2) / 6 - 1)
      atTop (𝓝 (π ^ 2 / 6 - 1)) := by
    convert ((tendsto_const_nhds.mul hsinc).add
      (tendsto_const_nhds.mul hsin)).div_const 6 |>.sub_const 1 using 1
    ring_nf
  have hfactor : Tendsto
      (fun d : ℕ => 2 * (1 - 2 / Nreal d) / Real.cos (theta d) ^ 2)
      atTop (𝓝 2) := by
    have htworatio : Tendsto
        (fun d : ℕ => (2 : ℝ) * (1 - 2 / Nreal d))
        atTop (𝓝 ((2 : ℝ) * 1)) :=
      tendsto_const_nhds.mul hratio
    convert htworatio.div hcos (by norm_num : (1 : ℝ) ≠ 0) using 1
    · ext d
      simp [Pi.div_apply]
    · norm_num
  convert hfactor.mul hbracket using 1
  · ext d
    ring_nf

/-- SZEGŐ THEOREM, quadratic form: `C_Nava(d)² → (π²-6)/3`. -/
theorem limite_szego_CNavaSq :
    Tendsto CNavaSq atTop (𝓝 (π ^ 2 / 3 - 2)) := by
  apply CNavaSq_regularizada_tendsto.congr'
  filter_upwards with d
  exact (CNavaSq_forma_regularizada d).symm

/-- SZEGŐ LIMIT: `C_Nava(d) → C_∞ = √((π²-6)/3)`, built on the
classical Szegő spectral distribution theory. -/
theorem limite_szego_CNava : Tendsto CNava atTop (𝓝 Cinf) := by
  unfold CNava Cinf
  exact Real.continuous_sqrt.continuousAt.tendsto.comp limite_szego_CNavaSq

/-- Citable name for the specialization. An alias of the already proved
result, not a re-derivation of the classical Toeplitz/Szegő theory. -/
theorem limite_nava_szego_CNava : Tendsto CNava atTop (𝓝 Cinf) :=
  limite_szego_CNava

/-- The geometric defect converges to the universal asymptotic defect. -/
theorem limite_defecto_geometrico :
    Tendsto deltaGeom atTop (𝓝 deltaInf) := by
  unfold deltaGeom deltaInf
  exact limite_szego_CNava.sub_const 1

/-- The universal defect never vanishes: `δ_∞ > 0`, an exact consequence
of `π > 3`. -/
theorem deltaInf_pos : 0 < deltaInf := by
  unfold deltaInf Cinf
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hx : (1 : ℝ) < π ^ 2 / 3 - 2 := by
    nlinarith [Real.pi_pos]
  have hs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx
  rw [Real.sqrt_one] at hs
  linarith

/-- Infinity is not added as a realized dimension: the sequence of
finite defects only converges to the strict limit value `δ∞ = C∞ - 1`. -/
theorem infinito_no_es_dimension_sino_limite :
    Tendsto deltaGeom atTop (𝓝 deltaInf) ∧ deltaInf = Cinf - 1 ∧ 0 < deltaInf :=
  ⟨limite_defecto_geometrico, rfl, deltaInf_pos⟩

theorem Cinf_pos : 0 < Cinf := by
  have h := deltaInf_pos
  unfold deltaInf at h
  linarith

/-- Asymptotic monotonicity: the leading term `δ_∞ - C_∞/(d+1)` of the
Szegő expansion is strictly increasing. -/
theorem deltaSzegoPrincipal_strictMono : StrictMono deltaSzegoPrincipal := by
  intro a b hab
  have hNa : 0 < Nreal a := by
    unfold Nreal
    positivity
  have hNlt : Nreal a < Nreal b := by
    have habr : (a : ℝ) < b := by exact_mod_cast hab
    unfold Nreal
    linarith
  have hinv : 1 / Nreal b < 1 / Nreal a :=
    one_div_lt_one_div_of_lt hNa hNlt
  unfold deltaSzegoPrincipal
  have hmul := mul_lt_mul_of_pos_left hinv Cinf_pos
  simpa [div_eq_mul_inv] using sub_lt_sub_left hmul deltaInf

/-! ## Gap positivity for `d ≥ 4`

Niven closes the saturation equation at `d ∈ {2,3}` (`D7_Niven.lean`).
What follows translates that trigonometric fact into the algebraic
inequality `1 < CNava(d)` (equivalently `0 < deltaGeom d`) for all
`d ≥ 4`, verifying `d = 4, 5` in exact closed form and `d ≥ 6` via the
same certified Taylor bounds used above for the limit. -/

/-! ## Consequence: `δ_geom(d) > 0` for all `d ≥ 4`

Niven closes the saturation equation at `d ∈ {2,3}`. The rest of this
section translates that trigonometric fact into the algebraic inequality
`1 < CNava(d)` (equivalently `0 < deltaGeom d`) for all `d ≥ 4`,
verifying `d = 4, 5` in exact closed form and `d ≥ 6` via certified
Taylor bounds on sine and cosine (without appealing to any external
numerical result: only `Real.pi_gt_d2`/`pi_lt_d2` from Mathlib and
rational algebra). -/

theorem CNavaSq_two : CNavaSq 2 = 1 := by
  simp only [CNavaSq, Nreal, theta, Nat.cast_ofNat]
  rw [show (2:ℝ)+1 = 3 by norm_num, show (2:ℝ)-1 = 1 by norm_num]
  rw [cos_pi_div_three, sin_pi_div_three]
  have h3 : (√3)^2 = (3:ℝ) := sq_sqrt (by norm_num)
  have hs : (√3 / 2)^2 = (3:ℝ)/4 := by rw [div_pow, h3]; norm_num
  simp [hs]; norm_num

theorem CNavaSq_three : CNavaSq 3 = 1 := by
  simp only [CNavaSq, Nreal, theta, Nat.cast_ofNat]
  rw [show (3:ℝ)+1 = 4 by norm_num, show (3:ℝ)-1 = 2 by norm_num]
  rw [cos_pi_div_four, sin_pi_div_four]
  have h2 : (√2)^2 = (2:ℝ) := sq_sqrt (by norm_num)
  have hs : (√2 / 2)^2 = (2:ℝ)/4 := by rw [div_pow, h2]; norm_num
  simp [hs]; norm_num

theorem CNavaSq_four_eq : CNavaSq 4 = (99 - 42 * √5) / 5 := by
  simp only [CNavaSq, Nreal, theta, Nat.cast_ofNat]
  rw [show (4:ℝ)+1 = 5 by norm_num, show (4:ℝ)-1 = 3 by norm_num]
  have hc0 : cos (π / 5) = (1 + √5) / 4 := cos_pi_div_five
  have hs5 : (√5)^2 = (5:ℝ) := sq_sqrt (by norm_num)
  have hcos2 : cos (π / 5)^2 = (3 + √5) / 8 := by
    rw [hc0]; ring_nf; simp [hs5]; ring
  have hsin2 : sin (π / 5)^2 = (5 - √5) / 8 := by
    have : sin (π / 5)^2 = 1 - cos (π / 5)^2 := by
      rw [← sin_sq_add_cos_sq (π / 5)]; ring
    rw [this, hcos2]; ring
  rw [hcos2, hsin2]
  ring_nf; field_simp; ring_nf; simp [hs5]; ring

theorem one_lt_CNavaSq_four : 1 < CNavaSq 4 := by
  rw [CNavaSq_four_eq]
  have h5 : (0:ℝ) < 5 := by norm_num
  rw [one_lt_div h5]
  have h : √5 < (47:ℝ) / 21 := by
    rw [sqrt_lt (by norm_num : (0:ℝ) ≤ 5) (by positivity)]; norm_num
  have hs : (√5)^2 = (5:ℝ) := sq_sqrt (by norm_num)
  nlinarith [hs, h, sqrt_nonneg 5]

theorem CNavaSq_five : CNavaSq 5 = (28:ℝ)/27 := by
  simp only [CNavaSq, Nreal, theta, Nat.cast_ofNat]
  rw [show (5:ℝ)+1 = 6 by norm_num, show (5:ℝ)-1 = 4 by norm_num]
  rw [cos_pi_div_six, sin_pi_div_six]
  have h3 : (√3)^2 = (3:ℝ) := sq_sqrt (by norm_num)
  have hc : (√3 / 2)^2 = (3:ℝ)/4 := by rw [div_pow, h3]; norm_num
  simp [hc]; norm_num

theorem one_lt_CNavaSq_five : 1 < CNavaSq 5 := by
  rw [CNavaSq_five]; norm_num

theorem one_lt_CNavaSq_six : 1 < CNavaSq 6 := by
  simp only [CNavaSq, Nreal, theta, Nat.cast_ofNat]
  rw [show (6:ℝ)+1 = 7 by norm_num, show (6:ℝ)-1 = 5 by norm_num]
  set θ := π / 7
  have h7 : (0:ℝ) < 7 := by norm_num
  have hθpos : 0 < θ := div_pos pi_pos h7
  have hθlt : θ < π / 2 := by
    rw [div_lt_div_iff₀ h7 (by norm_num : (0:ℝ)<2)]; nlinarith [pi_pos]
  have hπlo : (314:ℝ)/100 < π := by have := pi_gt_d2; norm_num at this ⊢; linarith
  have hπhi : π < (315:ℝ)/100 := by have := pi_lt_d2; norm_num at this ⊢; linarith
  have hθ_lt_one : θ < 1 := by
    have : θ < (315:ℝ)/100 / 7 := by
      simp only [θ]; exact div_lt_div_of_pos_right hπhi h7
    exact lt_trans this (by norm_num)
  have hs0pos : 0 < θ - θ^3/6 := by
    have : θ^2 < 6 := by nlinarith [hθpos, hθ_lt_one]
    nlinarith [hθpos, this]
  have hsin : θ - θ^3/6 < sin θ := sin_gt_sub_cube hθpos
  set s0 := θ - θ^3/6
  have hcos_pos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hθpos], hθlt⟩
  have hcos2 : cos θ ^ 2 < 1 - s0 ^ 2 := by
    have hsq : s0^2 < sin θ ^ 2 :=
      pow_lt_pow_left₀ hsin (le_of_lt hs0pos) (by norm_num)
    have : cos θ ^ 2 = 1 - sin θ ^ 2 := by rw [← sin_sq_add_cos_sq θ]; ring
    linarith
  have hs0_bound :
      s0 ≥ ((314:ℝ)/100 / 7) * (1 - ((315:ℝ)/100 / 7)^2 / 6) := by
    have hs0θ : s0 = θ * (1 - θ^2/6) := by ring
    have hθlo : (314:ℝ)/100 / 7 ≤ θ := by
      simp only [θ]; exact div_le_div_of_nonneg_right hπlo.le (le_of_lt h7)
    have hθhi2 : θ ≤ (315:ℝ)/100 / 7 := by
      simp only [θ]; exact div_le_div_of_nonneg_right hπhi.le (le_of_lt h7)
    have hfac : 1 - θ^2/6 ≥ 1 - ((315:ℝ)/100 / 7)^2 / 6 := by
      nlinarith [hθpos, hθhi2]
    rw [hs0θ]; nlinarith [hθlo, hfac, hθpos]
  have hpos_lo :
      (0:ℝ) ≤ ((314:ℝ)/100 / 7) * (1 - ((315:ℝ)/100 / 7)^2 / 6) := by
    norm_num
  have hs0sq :
      s0^2 ≥ (((314:ℝ)/100 / 7) * (1 - ((315:ℝ)/100 / 7)^2 / 6))^2 :=
    pow_le_pow_left₀ hpos_lo hs0_bound 2
  have h1s0 :
      1 - s0^2 ≤
        1 - (((314:ℝ)/100 / 7) * (1 - ((315:ℝ)/100 / 7)^2 / 6))^2 := by
    nlinarith [hs0sq]
  have hlt_thr :
      1 - (((314:ℝ)/100 / 7) * (1 - ((315:ℝ)/100 / 7)^2 / 6))^2 <
        (75:ℝ)/92 := by
    norm_num
  have hcos_thr : cos θ ^ 2 < (75:ℝ)/92 :=
    lt_of_lt_of_le hcos2 (le_trans h1s0 hlt_thr.le)
  have hs : sin θ ^ 2 = 1 - cos θ ^ 2 := by
    rw [← sin_sq_add_cos_sq θ]; ring
  rw [hs]
  set c := cos θ ^ 2
  have hcpos : 0 < c := sq_pos_of_pos hcos_pos
  have hc_thr : c < (75:ℝ)/92 := hcos_thr
  have hsimp :
      2 * 5 / (7 * c) * (((7:ℝ)^2 + 2) / 6 * (1 - c) - 1) =
        5 * (15 - 17 * c) / (7 * c) := by
    field_simp; ring
  rw [hsimp]
  have hden : 0 < 7 * c := by positivity
  rw [one_lt_div hden]
  nlinarith [hc_thr, hcpos]

/-- Rational threshold used in the finite-dimensional lower bound for `CNava`. -/
noncomputable def thrCNava (d : ℕ) : ℝ :=
  ((d : ℝ) - 1) * (((d : ℝ) + 1) ^ 2 - 4) /
    (((d : ℝ) - 1) * (((d : ℝ) + 1) ^ 2 + 2) + 3 * ((d : ℝ) + 1))

theorem CNavaSq_eq_cos_form (d : ℕ) (hd : 2 ≤ d)
    (hcos_ne : cos (π / ((d : ℝ) + 1)) ≠ 0) :
    CNavaSq d =
      ((d : ℝ) - 1) / (3 * ((d : ℝ) + 1) * cos (π / ((d : ℝ) + 1)) ^ 2) *
        ((((d : ℝ) + 1) ^ 2 - 4) -
          (((d : ℝ) + 1) ^ 2 + 2) * cos (π / ((d : ℝ) + 1)) ^ 2) := by
  set N := (d : ℝ) + 1
  set c := cos (π / N) ^ 2
  have hs : sin (π / N) ^ 2 = 1 - c := by
    have := sin_sq_add_cos_sq (π / N)
    simp only [c] at *; linarith
  have hcos_ne' : cos (π / N) ≠ 0 := by simpa [N] using hcos_ne
  simp only [CNavaSq, Nreal, theta]
  change
      2 * ((d : ℝ) - 1) / (N * cos (π / N) ^ 2) *
          (((N ^ 2 + 2) / 6) * sin (π / N) ^ 2 - 1) =
        ((d : ℝ) - 1) / (3 * N * cos (π / N) ^ 2) *
          ((N ^ 2 - 4) - (N ^ 2 + 2) * cos (π / N) ^ 2)
  rw [hs]
  have hc0 : c ≠ 0 := by
    have : cos (π / N) ^ 2 ≠ 0 := pow_ne_zero 2 hcos_ne'
    simpa [c] using this
  have hN0 : N ≠ 0 := by positivity
  simp only [c] at hc0 ⊢
  field_simp [hcos_ne', hN0]
  ring

theorem one_lt_CNavaSq_of_cos_lt_thr
    (d : ℕ) (hd : 2 ≤ d)
    (hcos_pos : 0 < cos (π / ((d : ℝ) + 1)))
    (hthr : cos (π / ((d : ℝ) + 1)) ^ 2 < thrCNava d) :
    1 < CNavaSq d := by
  set N := (d : ℝ) + 1
  set c := cos (π / N) ^ 2
  have hcpos : 0 < c := by
    change 0 < cos (π / N) ^ 2
    exact sq_pos_of_pos (by simpa [N] using hcos_pos)
  have hform : CNavaSq d =
      ((d : ℝ) - 1) / (3 * N * c) * ((N ^ 2 - 4) - (N ^ 2 + 2) * c) := by
    have hne : cos (π / ((d : ℝ) + 1)) ≠ 0 := hcos_pos.ne'
    simpa [N, c] using CNavaSq_eq_cos_form d hd hne
  have hden : 0 < 3 * N * c := by
    have : 0 < N := by positivity
    positivity
  have ha : 0 < (d : ℝ) - 1 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set e := (N ^ 2 - 4) - (N ^ 2 + 2) * c with hedef
  have hthr' : c <
      ((d : ℝ) - 1) * (N ^ 2 - 4) /
        (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) := by
    simpa [c, N, thrCNava] using hthr
  have hden' : 0 < ((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N := by positivity
  have hN2 : 0 < N ^ 2 - 4 := by
    have : (3:ℝ) ≤ N := by
      have : (2:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    nlinarith
  have hthr_mul :
      c * (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) <
        ((d : ℝ) - 1) * (N ^ 2 - 4) :=
    (lt_div_iff₀ hden').mp hthr'
  have he : 0 < e := by
    have hcmp :
        ((d : ℝ) - 1) * (N ^ 2 - 4) /
            (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) <
          (N ^ 2 - 4) / (N ^ 2 + 2) := by
      rw [div_lt_div_iff₀ hden' (by positivity)]
      nlinarith [hN2, ha, show 0 < N by positivity]
    have hc_mid : c < (N ^ 2 - 4) / (N ^ 2 + 2) := lt_trans hthr' hcmp
    have : c * (N ^ 2 + 2) < N ^ 2 - 4 := (lt_div_iff₀ (by positivity)).mp hc_mid
    simp only [e]; linarith
  have hmul : ((d : ℝ) - 1) * e > 3 * N * c := by
    simp only [e]
    nlinarith [hthr_mul]
  have hgt : ((d : ℝ) - 1) / (3 * N * c) * e > 1 := by
    have : ((d : ℝ) - 1) * e / (3 * N * c) > 1 :=
      (one_lt_div hden).mpr hmul
    convert this using 1; ring
  rwa [hform]

theorem key_poly_nat (n : ℕ) (hn : 7 ≤ n) :
    ((314:ℝ)/100)^2 * (1 - ((315:ℝ)/100)^2 / (3 * (n:ℝ)^2)) *
        ((n:ℝ)^3 - 2*(n:ℝ)^2 + 5*(n:ℝ) - 4) >
      (9*(n:ℝ) - 12) * (n:ℝ)^2 := by
  by_cases hle : n ≤ 40
  · interval_cases n <;> norm_num
  · have hnR : (41:ℝ) ≤ n := by exact_mod_cast (show 41 ≤ n by omega)
    have hnpos : (0:ℝ) < n := lt_of_lt_of_le (by norm_num : (0:ℝ) < 41) hnR
    have h314 : ((314:ℝ)/100)^2 ≥ (985:ℝ)/100 := by norm_num
    have hfac : 1 - ((315:ℝ)/100)^2 / (3 * (n:ℝ)^2) ≥ (99:ℝ)/100 := by
      have hle' : ((315:ℝ)/100)^2 / (3 * (n:ℝ)^2) ≤
          ((315:ℝ)/100)^2 / (3 * 41 ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hnR]
      have : ((315:ℝ)/100)^2 / (3 * 41 ^ 2) ≤ (1:ℝ)/100 := by norm_num
      linarith
    have hden : (n:ℝ)^3 - 2*(n:ℝ)^2 + 5*(n:ℝ) - 4 ≥ (n:ℝ)^3 - 2*(n:ℝ)^2 := by
      nlinarith [hnpos]
    have hden' : (n:ℝ)^3 - 2*(n:ℝ)^2 = (n:ℝ)^2 * ((n:ℝ) - 2) := by ring
    have hmain : ((985:ℝ)/100) * ((99:ℝ)/100) * ((n:ℝ) - 2) >
        9 * (n:ℝ) - 12 := by
      nlinarith [hnR]
    have hfacpos : (0:ℝ) < 1 - ((315:ℝ)/100)^2 / (3 * (n:ℝ)^2) := by
      linarith [hfac]
    have hdenpos : (0:ℝ) < (n:ℝ)^3 - 2*(n:ℝ)^2 + 5*(n:ℝ) - 4 := by
      nlinarith [hnR]
    nlinarith [h314, hfac, hden, hden', hmain, hfacpos, hdenpos,
      show (0:ℝ) ≤ (n:ℝ)^2 by positivity]

theorem cos_sq_bound_of_seven_le (N : ℝ) (hN : (7:ℝ) ≤ N) :
    cos (π / N) ^ 2 <
      1 - (((314:ℝ)/100 / N) * (1 - ((315:ℝ)/100 / N)^2 / 6)) ^ 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0:ℝ) < 7) hN
  set θ := π / N
  have hθpos : 0 < θ := div_pos pi_pos hNpos
  have hθlt : θ < π / 2 := by
    rw [div_lt_div_iff₀ hNpos (by norm_num : (0:ℝ)<2)]
    nlinarith [pi_pos, hN]
  have hπlo : (314:ℝ)/100 < π := by
    have := pi_gt_d2; norm_num at this ⊢; linarith
  have hπhi : π < (315:ℝ)/100 := by
    have := pi_lt_d2; norm_num at this ⊢; linarith
  have hθle : θ ≤ π / 7 := by
    rw [div_le_div_iff₀ hNpos (by norm_num : (0:ℝ)<7)]
    nlinarith [pi_pos, hN]
  have hθlt1 : θ < 1 := by
    have h1 : π / 7 < (315:ℝ)/100 / 7 :=
      div_lt_div_of_pos_right hπhi (by norm_num)
    have h2 : ((315:ℝ)/100 / 7) < 1 := by norm_num
    exact lt_of_le_of_lt hθle (lt_trans h1 h2)
  have hs0pos : 0 < θ - θ^3/6 := by
    have : θ^2 < 6 := by nlinarith [hθpos, hθlt1]
    nlinarith [hθpos, this]
  have hsin : θ - θ^3/6 < sin θ := sin_gt_sub_cube hθpos
  set s0 := θ - θ^3/6
  set s0lo := ((314:ℝ)/100 / N) * (1 - ((315:ℝ)/100 / N)^2 / 6)
  have hcos2 : cos θ ^ 2 < 1 - s0 ^ 2 := by
    have hsq : s0^2 < sin θ ^ 2 :=
      pow_lt_pow_left₀ hsin hs0pos.le (by norm_num)
    have : cos θ ^ 2 = 1 - sin θ ^ 2 := by
      rw [← sin_sq_add_cos_sq θ]; ring
    linarith
  have hfac_s0lo_pos : 0 ≤ 1 - ((315:ℝ)/100 / N)^2 / 6 := by
    have hle : ((315:ℝ)/100 / N)^2 / 6 ≤ ((315:ℝ)/100 / 7)^2 / 6 := by
      have : (315:ℝ)/100 / N ≤ (315:ℝ)/100 / 7 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hN
      nlinarith [this, show (0:ℝ) ≤ 315/100/N by positivity]
    have : ((315:ℝ)/100 / 7)^2 / 6 < 1 := by norm_num
    linarith
  have hs0_ge : s0 ≥ s0lo := by
    have hs0θ : s0 = θ * (1 - θ^2/6) := by ring
    have hθlo : (314:ℝ)/100 / N ≤ θ := by
      change (314:ℝ)/100 / N ≤ π / N
      exact div_le_div_of_nonneg_right hπlo.le hNpos.le
    have hθhi2 : θ ≤ (315:ℝ)/100 / N := by
      change π / N ≤ (315:ℝ)/100 / N
      exact div_le_div_of_nonneg_right hπhi.le hNpos.le
    have hfac : 1 - θ^2/6 ≥ 1 - ((315:ℝ)/100 / N)^2 / 6 := by
      nlinarith [hθpos, hθhi2]
    have hfacθ : 0 ≤ 1 - θ^2/6 := by
      have : θ^2 ≤ 1 := by nlinarith [hθpos, hθlt1]
      nlinarith
    have ha : (0:ℝ) ≤ (314:ℝ)/100 / N := by positivity
    rw [hs0θ]
    calc
      θ * (1 - θ^2/6)
          ≥ ((314:ℝ)/100 / N) * (1 - θ^2/6) :=
            mul_le_mul_of_nonneg_right hθlo hfacθ
      _ ≥ ((314:ℝ)/100 / N) * (1 - ((315:ℝ)/100 / N)^2 / 6) :=
            mul_le_mul_of_nonneg_left hfac ha
  have hpos_lo : 0 ≤ s0lo := by positivity
  have hs0sq : s0 ^ 2 ≥ s0lo ^ 2 :=
    pow_le_pow_left₀ hpos_lo hs0_ge 2
  linarith [hcos2, hs0sq]

theorem one_sub_thr_eq (d : ℕ) (hd : 2 ≤ d) :
    1 - thrCNava d =
      (9 * ((d : ℝ) + 1) - 12) /
        (((d : ℝ) + 1) ^ 3 - 2 * ((d : ℝ) + 1) ^ 2 +
          5 * ((d : ℝ) + 1) - 4) := by
  set N := (d : ℝ) + 1
  have hd1 : (d : ℝ) - 1 = N - 2 := by ring
  have hden0 : (N - 2) * (N ^ 2 + 2) + 3 * N ≠ 0 := by
    have : 0 < N - 2 := by
      have : (2:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    positivity
  have hthr : thrCNava d =
      (N - 2) * (N ^ 2 - 4) / ((N - 2) * (N ^ 2 + 2) + 3 * N) := by
    unfold thrCNava; rw [hd1]
  rw [hthr]
  have hD : (N - 2) * (N ^ 2 + 2) + 3 * N =
      N ^ 3 - 2 * N ^ 2 + 5 * N - 4 := by ring
  rw [hD]
  have hden : N ^ 3 - 2 * N ^ 2 + 5 * N - 4 ≠ 0 := by
    rw [← hD]; exact hden0
  rw [one_sub_div hden]
  congr 1
  ring

set_option maxHeartbeats 800000 in
theorem one_lt_CNavaSq_of_six_le (d : ℕ) (hd : 6 ≤ d) : 1 < CNavaSq d := by
  have hd2 : 2 ≤ d := by omega
  set N := (d : ℝ) + 1
  have hNnat : 7 ≤ d + 1 := by omega
  have hN : (7:ℝ) ≤ N := by
    have : (6:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hNpos : 0 < N := by positivity
  have hcos_ub := cos_sq_bound_of_seven_le N hN
  set s0lo := ((314:ℝ)/100 / N) * (1 - ((315:ℝ)/100 / N)^2 / 6)
  have hcos_lt : cos (π / N) ^ 2 < 1 - s0lo ^ 2 := by
    simpa [s0lo] using hcos_ub
  have hweak :
      s0lo ^ 2 ≥
        ((314:ℝ)/100)^2 / N ^ 2 *
          (1 - ((315:ℝ)/100)^2 / (3 * N ^ 2)) := by
    have hleft : s0lo ^ 2 =
        ((314:ℝ)/100)^2 / N ^ 2 *
          (1 - ((315:ℝ)/100 / N)^2 / 6) ^ 2 := by
      change
          (((314:ℝ)/100 / N) * (1 - ((315:ℝ)/100 / N)^2 / 6)) ^ 2 =
            ((314:ℝ)/100)^2 / N ^ 2 *
              (1 - ((315:ℝ)/100 / N)^2 / 6) ^ 2
      rw [mul_pow, div_pow]
    have hsq : (1 - ((315:ℝ)/100 / N)^2 / 6) ^ 2 ≥
        1 - 2 * (((315:ℝ)/100 / N)^2 / 6) := by
      nlinarith [sq_nonneg (((315:ℝ)/100 / N)^2 / 6)]
    have h2u : 2 * (((315:ℝ)/100 / N)^2 / 6) =
        ((315:ℝ)/100)^2 / (3 * N ^ 2) := by
      field_simp [hNpos.ne']; ring
    rw [hleft]
    nlinarith [hsq, show (0:ℝ) ≤ ((314:ℝ)/100)^2 / N^2 by positivity, h2u]
  have h1mthr := one_sub_thr_eq d hd2
  have hden_pos : 0 < N ^ 3 - 2 * N ^ 2 + 5 * N - 4 := by
    nlinarith [hN, hNpos]
  have hkey := key_poly_nat (d + 1) hNnat
  have hkey' :
      ((314:ℝ)/100)^2 * (1 - ((315:ℝ)/100)^2 / (3 * N ^ 2)) *
          (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) >
        (9 * N - 12) * N ^ 2 := by
    simpa [N] using hkey
  have hs0_gt : s0lo ^ 2 > 1 - thrCNava d := by
    have h1 : 1 - thrCNava d =
        (9 * N - 12) / (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) := by
      simpa [N] using h1mthr
    rw [h1, gt_iff_lt]
    have hN2pos : 0 < N ^ 2 := sq_pos_of_pos hNpos
    have hlo :
        ((314:ℝ)/100)^2 / N ^ 2 *
            (1 - ((315:ℝ)/100)^2 / (3 * N ^ 2)) *
            (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) >
          9 * N - 12 := by
      have hN2ne : N ^ 2 ≠ 0 := hN2pos.ne'
      have hL :
          ((314:ℝ)/100)^2 / N ^ 2 *
              (1 - ((315:ℝ)/100)^2 / (3 * N ^ 2)) *
              (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) =
            (((314:ℝ)/100)^2 *
                (1 - ((315:ℝ)/100)^2 / (3 * N ^ 2)) *
                (N ^ 3 - 2 * N ^ 2 + 5 * N - 4)) / N ^ 2 := by
        field_simp [hN2ne]
      rw [hL]
      have hdiv :
          (((314:ℝ)/100)^2 *
              (1 - ((315:ℝ)/100)^2 / (3 * N ^ 2)) *
              (N ^ 3 - 2 * N ^ 2 + 5 * N - 4)) / N ^ 2 >
            ((9 * N - 12) * N ^ 2) / N ^ 2 :=
        div_lt_div_of_pos_right hkey' hN2pos
      have hR : ((9 * N - 12) * N ^ 2) / N ^ 2 = 9 * N - 12 := by
        field_simp [hN2ne]
      rwa [hR] at hdiv
    have hmul :
        9 * N - 12 < s0lo ^ 2 * (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) := by
      nlinarith [hweak, hlo, hden_pos]
    exact (div_lt_iff₀ hden_pos).mpr hmul
  have hcos_thr : cos (π / N) ^ 2 < thrCNava d := by
    have : 1 - s0lo ^ 2 < thrCNava d := by linarith [hs0_gt]
    linarith [hcos_lt]
  have hθlt : π / N < π / 2 := by
    rw [div_lt_div_iff₀ hNpos (by norm_num : (0:ℝ)<2)]
    nlinarith [pi_pos, hN]
  have hθpos : 0 < π / N := div_pos pi_pos hNpos
  have hcos_pos : 0 < cos (π / N) :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hθpos], hθlt⟩
  exact one_lt_CNavaSq_of_cos_lt_thr d hd2
    (by simpa [N] using hcos_pos)
    (by simpa [N] using hcos_thr)

/-- `CNava(d)² > 1` for all `d ≥ 4`: exact cases `4, 5`, `d ≥ 6` via
certified Taylor bounds. -/
theorem one_lt_CNavaSq (d : ℕ) (hd : 4 ≤ d) : 1 < CNavaSq d := by
  match d with
  | 0 | 1 | 2 | 3 => omega
  | 4 => exact one_lt_CNavaSq_four
  | 5 => exact one_lt_CNavaSq_five
  | n + 6 => exact one_lt_CNavaSq_of_six_le (n + 6) (by omega)

theorem one_lt_CNava_of_four_le (d : ℕ) (hd : 4 ≤ d) : 1 < CNava d := by
  rw [CNava, ← sqrt_one]
  exact sqrt_lt_sqrt (by norm_num) (one_lt_CNavaSq d hd)

/-- CENTRAL NIVEN THEOREM → POSITIVITY: `δ_geom(d) > 0` for all
`d ≥ 4`. -/
theorem deltaGeom_pos_of_four_le (d : ℕ) (hd : 4 ≤ d) : 0 < deltaGeom d := by
  unfold deltaGeom
  linarith [one_lt_CNava_of_four_le d hd]

end Gnomon
