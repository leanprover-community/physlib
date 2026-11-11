/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.RadialQuantization
public import Mathlib.Analysis.ODE.ExistUnique

/-!

# Completeness of the regular radial solutions of hydrogen

Every solution of the radial equation of hydrogen that vanishes at the origin is of the power
series form assumed in `RadialQuantization`. Together with `radial_quantization` this shows,
without any ansatz, that a square integrable solution vanishing at the origin exists only for the
Bohr levels.

## i. Overview

In Rydberg units the reduced radial function of a state of energy `-κ²` and angular momentum `l`
solves `u'' = q u` on `(0, ∞)` with `q(ρ) = l(l+1)/ρ² - 2/ρ + κ²` (`radialPot`). The origin is a
regular singular point with indicial exponents `l + 1` and `-l`.

- The Frobenius solution for the exponent `l + 1` is built explicitly: the coefficients
  `regCoeff κ l` solve the recursion `RadialRec` with `c_0 = 1` and define an everywhere
  convergent series (ratio test), and `radialSeries κ l (regCoeff κ l)` solves the radial equation
  (`radial_ode_of_radialRec`). It behaves like `ρ^(l+1)` near `0`.
- The second solution is never constructed. Instead, for any solution `u` the Wronskian
  `u u₁' - u' u₁` with the regular solution `u₁` is constant; if it were non-zero, `u` would grow
  like `ρ^(-l)` at `0` (and tend to a non-zero constant for `l = 0`). So `u → 0` forces the
  Wronskian to vanish, and `u` is a multiple of `u₁` near `0`.
- Uniqueness for the first-order system `(u, u')` (`ODE_solution_unique_of_mem_Ioo`) extends this
  to all of `(0, ∞)`.

The boundary condition `u(ρ) → 0` as `ρ → 0⁺` is the physical one: for `l = 0` the second solution
tends to a non-zero constant, so `u₂(r)/r ~ 1/r` near the origin, which lies in `L²(ℝ³)` but not in
the domain of the Hamiltonian.

## ii. Key results

- `entireCoeff_regCoeff`, `radial_ode_of_radialRec`: the regular solution.
- `wronskian_eq_zero_of_tendsto`: a solution tending to `0` has vanishing Wronskian with it.
- `eqOn_zero_of_eqOn_Ioo`: a solution vanishing near `0` vanishes on `(0, ∞)`.
- `radial_regular_solution`: every solution vanishing at `0` is `radialSeries κ l c` for an
  everywhere convergent `c` satisfying the recursion.
- `radial_quantization_of_tendsto`: the quantisation of the hydrogen levels without the power
  series ansatz.

## iii. Table of contents

- A. The regular solution
- B. The regular solution near the origin and the Wronskian
- C. Solutions vanishing at the origin
- D. Uniqueness away from the origin
- E. Completeness and quantisation

## iv. References

- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.7.

## A. The regular solution

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open MeasureTheory Set Filter Topology

variable {κ : ℝ} {l : ℕ}

/-- The radial potential term `q(ρ) = l(l+1)/ρ² - 2/ρ + κ²`, so that the radial equation reads
`u'' = q u`. -/
def radialPot (κ : ℝ) (l : ℕ) (ρ : ℝ) : ℝ := (l : ℝ) * (l + 1) / ρ ^ 2 - 2 / ρ + κ ^ 2

/-- The coefficients of the regular solution: `c_0 = 1` and
`c_{k+1} = (2κ(k + l + 1) - 2) / ((k + 1)(k + 2l + 2)) c_k`. -/
def regCoeff (κ : ℝ) (l : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (2 * κ * (k + l + 1) - 2) / (((k : ℝ) + 1) * (k + 2 * l + 2)) * regCoeff κ l k

@[simp]
lemma regCoeff_zero : regCoeff κ l 0 = 1 := rfl

lemma radialRec_regCoeff : RadialRec κ l (regCoeff κ l) := by
  intro k
  have h : ((k : ℝ) + 1) * (k + 2 * l + 2) ≠ 0 := by positivity
  simp only [regCoeff]
  field_simp

lemma entireCoeff_regCoeff : EntireCoeff (regCoeff κ l) := by
  intro r hr
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1) ?_
  filter_upwards [eventually_ge_atTop ⌈4 * (|κ| + 1) * r⌉₊] with k hk
  have hk' : 4 * (|κ| + 1) * r ≤ k := Nat.ceil_le.mp hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hpos : (0 : ℝ) < ((k : ℝ) + 1) * (k + 2 * l + 2) := by positivity
  have hnum : |2 * κ * (k + l + 1) - 2| ≤ 2 * (|κ| + 1) * (k + 2 * l + 2) := by
    have h1 : 0 ≤ (|κ| - κ) * ((k : ℝ) + l + 1) :=
      mul_nonneg (sub_nonneg.2 (le_abs_self κ)) (by positivity)
    have h2 : 0 ≤ (|κ| + κ) * ((k : ℝ) + l + 1) :=
      mul_nonneg (by linarith [neg_abs_le κ]) (by positivity)
    have h3 : 0 ≤ |κ| * (l : ℝ) := mul_nonneg (abs_nonneg κ) hl0
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg κ]
  have key : |2 * κ * (k + l + 1) - 2| / (((k : ℝ) + 1) * (k + 2 * l + 2)) * r ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have h4 : 0 ≤ ((k : ℝ) + 2 * l + 2) * ((k + 1) - 4 * (|κ| + 1) * r) :=
      mul_nonneg (by positivity) (by linarith)
    calc |2 * κ * (k + l + 1) - 2| * r ≤ 2 * (|κ| + 1) * (k + 2 * l + 2) * r := by gcongr
      _ ≤ 1 / 2 * (((k : ℝ) + 1) * (k + 2 * l + 2)) := by nlinarith
  simp only [Real.norm_eq_abs, regCoeff, abs_mul, abs_div, abs_pow, abs_of_nonneg hr, abs_abs,
    abs_of_pos hpos]
  calc |2 * κ * (k + l + 1) - 2| / (((k : ℝ) + 1) * (k + 2 * l + 2)) * |regCoeff κ l k| *
        r ^ (k + 1) =
      (|2 * κ * (k + l + 1) - 2| / (((k : ℝ) + 1) * (k + 2 * l + 2)) * r) *
        (|regCoeff κ l k| * r ^ k) := by ring
    _ ≤ 1 / 2 * (|regCoeff κ l k| * r ^ k) := by gcongr

/-- **Converse of `recursion_of_radial_ode`.** If the coefficients satisfy the recursion, the
ansatz solves the radial equation on `(0, ∞)`. -/
lemma radial_ode_of_radialRec {c : ℕ → ℝ} (hc : EntireCoeff c) (hrec : RadialRec κ l c) {ρ : ℝ}
    (hρ : 0 < ρ) :
    HasDerivAt (radialSeriesD κ l c) (radialPot κ l ρ * radialSeries κ l c ρ) ρ := by
  have hK : psum (fun k => (k : ℝ) * dcoeff c k + ((2 * (l : ℝ) + 2) * dcoeff c k +
      ((-2 * κ) * ((k : ℝ) * c k) + (2 - 2 * κ * ((l : ℝ) + 1)) * c k))) ρ = 0 := by
    have h0 : (fun k : ℕ => (k : ℝ) * dcoeff c k + ((2 * (l : ℝ) + 2) * dcoeff c k +
        ((-2 * κ) * ((k : ℝ) * c k) + (2 - 2 * κ * ((l : ℝ) + 1)) * c k))) = fun _ => 0 :=
      funext fun k => by
        simp only [dcoeff]
        linear_combination hrec k
    rw [h0, psum]
    simp
  rw [psum_add hc.derivCoeff.natMul ((hc.derivCoeff.const_mul _).add
      ((hc.natMul.const_mul _).add (hc.const_mul _))),
    psum_add (hc.derivCoeff.const_mul _) ((hc.natMul.const_mul _).add (hc.const_mul _)),
    psum_add (hc.natMul.const_mul _) (hc.const_mul _), psum_const_mul, psum_const_mul,
    psum_const_mul, ← mul_psum_dcoeff hc.derivCoeff, ← mul_psum_dcoeff hc] at hK
  have hid := radial_identity κ ρ (psum c ρ) (psum (dcoeff c) ρ) (psum (dcoeff (dcoeff c)) ρ)
    (Real.exp (-(κ * ρ))) l hρ.ne'
  refine (hasDerivAt_radialSeriesD hc ρ).congr_deriv ?_
  rw [radialPot, radialSeries]
  linear_combination hid + ρ ^ l * Real.exp (-(κ * ρ)) * hK

/-!

## B. The regular solution near the origin and the Wronskian

-/

/-- Near the origin the regular solution is comparable to `ρ^(l+1)`. -/
lemma regSol_near_zero : ∃ δ > 0, ∃ a > 0, ∃ b > 0, ∀ ρ ∈ Ioc 0 δ,
    a * ρ ^ (l + 1) ≤ radialSeries κ l (regCoeff κ l) ρ ∧
      radialSeries κ l (regCoeff κ l) ρ ≤ b * ρ ^ (l + 1) := by
  have hcont : ContinuousAt (psum (regCoeff κ l)) 0 :=
    (hasDerivAt_psum entireCoeff_regCoeff 0).continuousAt
  have h1 : psum (regCoeff κ l) 0 = 1 := by rw [psum_zero]; rfl
  have hev : ∀ᶠ ρ in 𝓝 (0 : ℝ), psum (regCoeff κ l) ρ ∈ Ioo (1 / 2 : ℝ) (3 / 2) :=
    hcont.eventually (Ioo_mem_nhds (by rw [h1]; norm_num) (by rw [h1]; norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (ε / 2) 1, by positivity, Real.exp (-|κ|) * (1 / 2), by positivity,
    Real.exp |κ| * (3 / 2), by positivity, fun ρ hρ => ?_⟩
  have hρ1 : ρ ≤ 1 := hρ.2.trans (min_le_right _ _)
  have hS := hball (y := ρ) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hρ.1]
    linarith [hρ.2.trans (min_le_left _ _)])
  have hκρ : |κ * ρ| ≤ |κ| := by
    rw [abs_mul, abs_of_pos hρ.1]
    exact mul_le_of_le_one_right (abs_nonneg κ) hρ1
  have hE1 : Real.exp (-|κ|) ≤ Real.exp (-(κ * ρ)) :=
    Real.exp_le_exp.mpr (by linarith [le_abs_self (κ * ρ)])
  have hE2 : Real.exp (-(κ * ρ)) ≤ Real.exp |κ| :=
    Real.exp_le_exp.mpr (by linarith [neg_abs_le (κ * ρ)])
  have hP : 0 < ρ ^ (l + 1) := pow_pos hρ.1 _
  have hlow : Real.exp (-|κ|) * (1 / 2) ≤ Real.exp (-(κ * ρ)) * psum (regCoeff κ l) ρ :=
    mul_le_mul hE1 hS.1.le (by norm_num) (Real.exp_pos _).le
  have hup : Real.exp (-(κ * ρ)) * psum (regCoeff κ l) ρ ≤ Real.exp |κ| * (3 / 2) :=
    mul_le_mul hE2 hS.2.le (by linarith [hS.1]) (Real.exp_pos _).le
  have e : radialSeries κ l (regCoeff κ l) ρ =
      ρ ^ (l + 1) * (Real.exp (-(κ * ρ)) * psum (regCoeff κ l) ρ) := by
    rw [radialSeries, mul_assoc]
  rw [e, mul_comm _ (ρ ^ (l + 1)), mul_comm _ (ρ ^ (l + 1))]
  exact ⟨mul_le_mul_of_nonneg_left hlow hP.le, mul_le_mul_of_nonneg_left hup hP.le⟩

/-- A function with vanishing derivative on an open preconnected set is constant there. -/
lemma exists_const_of_hasDerivAt_zero {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hs' : IsPreconnected s) (h : ∀ x ∈ s, HasDerivAt f 0 x) : ∃ a, ∀ x ∈ s, f x = a :=
  hs.exists_is_const_of_deriv_eq_zero hs'
    (fun x hx => (h x hx).differentiableAt.differentiableWithinAt) fun x hx => (h x hx).deriv

/-- The Wronskian of two solutions of `u'' = q u` on `(0, ∞)` is constant. -/
lemma wronskian_const {q u u' v v' : ℝ → ℝ}
    (hu : ∀ ρ, 0 < ρ → HasDerivAt u (u' ρ) ρ) (hu' : ∀ ρ, 0 < ρ → HasDerivAt u' (q ρ * u ρ) ρ)
    (hv : ∀ ρ, 0 < ρ → HasDerivAt v (v' ρ) ρ) (hv' : ∀ ρ, 0 < ρ → HasDerivAt v' (q ρ * v ρ) ρ) :
    ∃ W : ℝ, ∀ ρ, 0 < ρ → u ρ * v' ρ - u' ρ * v ρ = W :=
  exists_const_of_hasDerivAt_zero (f := fun ρ => u ρ * v' ρ - u' ρ * v ρ) isOpen_Ioi
    isPreconnected_Ioi fun ρ hρ => by
      convert ((hu ρ hρ).mul (hv' ρ hρ)).sub ((hu' ρ hρ).mul (hv ρ hρ)) using 1
      ring

/-!

## C. Solutions vanishing at the origin

-/

/-- One sign of the Wronskian: if it were positive, `u/u₁ - K ρ^(-(2l+1))` would be antitone near
`0`, so `u(ρ) ≥ K a - |M| b ρ` for small `ρ`, contradicting `u → 0`. -/
lemma wronskian_nonpos_of_tendsto {u u' : ℝ → ℝ}
    (hu : ∀ ρ, 0 < ρ → HasDerivAt u (u' ρ) ρ)
    (hu' : ∀ ρ, 0 < ρ → HasDerivAt u' (radialPot κ l ρ * u ρ) ρ)
    (h0 : Tendsto u (𝓝[>] 0) (𝓝 0)) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    u ρ₀ * radialSeriesD κ l (regCoeff κ l) ρ₀ -
      u' ρ₀ * radialSeries κ l (regCoeff κ l) ρ₀ ≤ 0 := by
  set u₁ := radialSeries κ l (regCoeff κ l) with hu₁def
  set u₁' := radialSeriesD κ l (regCoeff κ l) with hu₁'def
  have hd1 : ∀ ρ, 0 < ρ → HasDerivAt u₁ (u₁' ρ) ρ := fun ρ _ =>
    hasDerivAt_radialSeries entireCoeff_regCoeff ρ
  have hd2 : ∀ ρ, 0 < ρ → HasDerivAt u₁' (radialPot κ l ρ * u₁ ρ) ρ := fun ρ hρ =>
    radial_ode_of_radialRec entireCoeff_regCoeff radialRec_regCoeff hρ
  obtain ⟨W, hW⟩ := wronskian_const hu hu' hd1 hd2
  rw [hW ρ₀ hρ₀]
  by_contra hWpos
  replace hWpos := not_le.mp hWpos
  obtain ⟨δ, hδ, a, ha, b, hb, hab⟩ := regSol_near_zero (κ := κ) (l := l)
  have hu₁pos : ∀ ρ ∈ Ioc 0 δ, 0 < u₁ ρ := fun ρ hρ =>
    lt_of_lt_of_le (mul_pos ha (pow_pos hρ.1 _)) (hab ρ hρ).1
  set K : ℝ := W / (b ^ 2 * ((2 * l + 1 : ℕ) : ℝ)) with hKdef
  have hK : 0 < K := by positivity
  set g : ℝ → ℝ := fun ρ => u ρ / u₁ ρ - K * (ρ ^ (2 * l + 1))⁻¹ with hgdef
  -- the derivative of `g`
  have hg : ∀ ρ ∈ Ioo 0 δ, HasDerivAt g
      (-W / u₁ ρ ^ 2 + W / (b * ρ ^ (l + 1)) ^ 2) ρ := by
    intro ρ hρ
    have hpos := hu₁pos ρ ⟨hρ.1, hρ.2.le⟩
    have h1 := (hu ρ hρ.1).div (hd1 ρ hρ.1) hpos.ne'
    have h2 := ((hasDerivAt_pow (2 * l + 1) ρ).inv (pow_ne_zero _ hρ.1.ne')).const_mul K
    convert h1.sub h2 using 1
    rw [hKdef, Nat.add_sub_cancel, ← hW ρ hρ.1]
    have hρ0 := hρ.1.ne'
    field_simp
    ring
  -- `g` is antitone on `(0, δ)`
  have hneg : ∀ ρ ∈ Ioo 0 δ, -W / u₁ ρ ^ 2 + W / (b * ρ ^ (l + 1)) ^ 2 ≤ 0 := by
    intro ρ hρ
    have hpos := hu₁pos ρ ⟨hρ.1, hρ.2.le⟩
    have hsq : u₁ ρ ^ 2 ≤ (b * ρ ^ (l + 1)) ^ 2 :=
      pow_le_pow_left₀ hpos.le (hab ρ ⟨hρ.1, hρ.2.le⟩).2 2
    have := div_le_div_of_nonneg_left hWpos.le (by positivity) hsq
    rw [neg_div]
    linarith
  have hanti : AntitoneOn g (Ioo 0 δ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 δ)
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioo]
      exact fun x hx => (hg x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro x hx
      rw [(hg x hx).deriv]
      exact hneg x hx
  set M : ℝ := g (δ / 2) with hMdef
  -- lower bound for `u` near `0`
  have hlow : ∀ ρ, 0 < ρ → ρ ≤ δ / 2 → ρ ≤ 1 → K * a - |M| * b * ρ ≤ u ρ := by
    intro ρ hρ0 hρδ hρ1
    have hρI : ρ ∈ Ioc 0 δ := ⟨hρ0, by linarith⟩
    have hpos := hu₁pos ρ hρI
    have hgm : M ≤ g ρ := hanti ⟨hρ0, by linarith⟩ ⟨by positivity, by linarith⟩ hρδ
    have hq : M + K * (ρ ^ (2 * l + 1))⁻¹ ≤ u ρ / u₁ ρ := by
      simp only [hgdef] at hgm
      linarith
    have h3 : (M + K * (ρ ^ (2 * l + 1))⁻¹) * u₁ ρ ≤ u ρ := (le_div_iff₀ hpos).mp hq
    have h4 : a ≤ (ρ ^ (2 * l + 1))⁻¹ * u₁ ρ := by
      rw [inv_mul_eq_div, le_div_iff₀ (pow_pos hρ0 _)]
      calc a * ρ ^ (2 * l + 1) ≤ a * ρ ^ (l + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1 (by omega)) ha.le
        _ ≤ u₁ ρ := (hab ρ hρI).1
    have h5 : |M| * u₁ ρ ≤ |M| * (b * ρ) := by
      refine mul_le_mul_of_nonneg_left ((hab ρ hρI).2.trans ?_) (abs_nonneg M)
      exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hρ0.le hρ1 (by omega)) hb.le
    have h6 : 0 ≤ (M + |M|) * u₁ ρ := mul_nonneg (by linarith [neg_abs_le M]) hpos.le
    have h7 := mul_le_mul_of_nonneg_left h4 hK.le
    nlinarith
  -- contradiction with `u → 0`
  set m : ℝ := min (min (δ / 2) 1) (K * a / (2 * (|M| * b + 1))) with hmdef
  have hm : 0 < m := by positivity
  obtain ⟨ρ, h1, h2⟩ := ((h0.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < K * a / 2))).and
    (Ioo_mem_nhdsGT hm)).exists
  have hρm : ρ < K * a / (2 * (|M| * b + 1)) := h2.2.trans_le (min_le_right _ _)
  have hρ' : (|M| * b + 1) * ρ < K * a / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hρm
    linarith
  have := hlow ρ h2.1 (h2.2.le.trans ((min_le_left _ _).trans (min_le_left _ _)))
    (h2.2.le.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have : 0 ≤ ρ := h2.1.le
  have h1' : u ρ < K * a / 2 := h1
  nlinarith

/-- A solution tending to `0` at the origin has vanishing Wronskian with the regular solution. -/
lemma wronskian_eq_zero_of_tendsto {u u' : ℝ → ℝ}
    (hu : ∀ ρ, 0 < ρ → HasDerivAt u (u' ρ) ρ)
    (hu' : ∀ ρ, 0 < ρ → HasDerivAt u' (radialPot κ l ρ * u ρ) ρ)
    (h0 : Tendsto u (𝓝[>] 0) (𝓝 0)) {ρ : ℝ} (hρ : 0 < ρ) :
    u ρ * radialSeriesD κ l (regCoeff κ l) ρ - u' ρ * radialSeries κ l (regCoeff κ l) ρ = 0 := by
  refine le_antisymm (wronskian_nonpos_of_tendsto hu hu' h0 hρ) ?_
  have h := wronskian_nonpos_of_tendsto (u := fun ρ => -u ρ) (u' := fun ρ => -u' ρ)
    (fun ρ hρ => (hu ρ hρ).neg)
    (fun ρ hρ => (hu' ρ hρ).neg.congr_deriv (by ring)) (by simpa using h0.neg) hρ
  linarith

/-- A solution tending to `0` at the origin is a multiple of the regular solution near `0`. -/
lemma exists_eqOn_near_zero_of_tendsto {u u' : ℝ → ℝ}
    (hu : ∀ ρ, 0 < ρ → HasDerivAt u (u' ρ) ρ)
    (hu' : ∀ ρ, 0 < ρ → HasDerivAt u' (radialPot κ l ρ * u ρ) ρ)
    (h0 : Tendsto u (𝓝[>] 0) (𝓝 0)) :
    ∃ δ > 0, ∃ A : ℝ, ∀ ρ ∈ Ioo 0 δ, u ρ = A * radialSeries κ l (regCoeff κ l) ρ := by
  obtain ⟨δ, hδ, a, ha, b, -, hab⟩ := regSol_near_zero (κ := κ) (l := l)
  have hpos : ∀ ρ ∈ Ioo 0 δ, 0 < radialSeries κ l (regCoeff κ l) ρ := fun ρ hρ =>
    lt_of_lt_of_le (mul_pos ha (pow_pos hρ.1 _)) (hab ρ ⟨hρ.1, hρ.2.le⟩).1
  obtain ⟨A, hA⟩ := exists_const_of_hasDerivAt_zero
    (f := fun ρ => u ρ / radialSeries κ l (regCoeff κ l) ρ) isOpen_Ioo isPreconnected_Ioo
    fun ρ hρ => by
      have h := (hu ρ hρ.1).div (hasDerivAt_radialSeries entireCoeff_regCoeff ρ) (hpos ρ hρ).ne'
      convert h using 1
      have hW := wronskian_eq_zero_of_tendsto hu hu' h0 hρ.1
      rw [eq_div_iff (pow_ne_zero 2 (hpos ρ hρ).ne')]
      linarith
  refine ⟨δ, hδ, A, fun ρ hρ => ?_⟩
  have := hA ρ hρ
  rw [div_eq_iff (hpos ρ hρ).ne'] at this
  exact this

/-!

## D. Uniqueness away from the origin

-/

/-- A solution of `w'' = q w` with continuous `q` that vanishes on `(0, δ)` vanishes on `(0, ∞)`. -/
lemma eqOn_zero_of_eqOn_Ioo {q w w' : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    (hw : ∀ ρ, 0 < ρ → HasDerivAt w (w' ρ) ρ) (hw' : ∀ ρ, 0 < ρ → HasDerivAt w' (q ρ * w ρ) ρ)
    {δ : ℝ} (hδ : 0 < δ) (h : ∀ ρ ∈ Ioo 0 δ, w ρ = 0) :
    ∀ ρ, 0 < ρ → w ρ = 0 := by
  intro ρ hρ
  set m := min δ ρ with hm
  have hm0 : 0 < m := lt_min hδ hρ
  have hmδ : m ≤ δ := min_le_left δ ρ
  have hmρ : m ≤ ρ := min_le_right δ ρ
  -- `q` is bounded on `[m/2, ρ + 1]`, so the first-order system is Lipschitz there
  have hsub : Icc (m / 2) (ρ + 1) ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le (by positivity) ht.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hq.mono hsub)
  have hK0 : (0 : ℝ) ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have hlip : ∀ t ∈ Ioo (m / 2) (ρ + 1),
      LipschitzOnWith (Real.toNNReal (max 1 C)) (fun p : ℝ × ℝ => (p.2, q t * p.1)) univ := by
    intro t ht
    refine (LipschitzWith.of_dist_le_mul fun p p' => ?_).lipschitzOnWith
    have hqt : |q t| ≤ C := by simpa [Real.norm_eq_abs] using hC t (Ioo_subset_Icc_self ht)
    rw [Prod.dist_eq, Prod.dist_eq, Real.coe_toNNReal _ hK0]
    simp only [Real.dist_eq]
    have h1 : |p.1 - p'.1| ≤ max |p.1 - p'.1| |p.2 - p'.2| := le_max_left _ _
    have h2 : |p.2 - p'.2| ≤ max |p.1 - p'.1| |p.2 - p'.2| := le_max_right _ _
    refine max_le ?_ ?_
    · calc |p.2 - p'.2| = 1 * |p.2 - p'.2| := (one_mul _).symm
        _ ≤ max 1 C * max |p.1 - p'.1| |p.2 - p'.2| :=
          mul_le_mul (le_max_left _ _) h2 (abs_nonneg _) hK0
    · rw [← mul_sub, abs_mul]
      exact mul_le_mul (hqt.trans (le_max_right _ _)) h1 (abs_nonneg _) hK0
  -- initial point inside `(0, δ)`, where `w = w' = 0`
  set t₀ := 3 / 4 * m with ht₀def
  have ht₀ : t₀ ∈ Ioo (m / 2) (ρ + 1) := ⟨by linarith, by linarith⟩
  have ht₀δ : t₀ < δ := by linarith
  have hloc : w =ᶠ[𝓝 t₀] fun _ => 0 :=
    Filter.eventually_of_mem (Ioo_mem_nhds (by positivity) ht₀δ) h
  have hw'0 : w' t₀ = 0 :=
    (hw t₀ (by positivity)).unique ((hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq hloc)
  have key := ODE_solution_unique_of_mem_Ioo (v := fun t (p : ℝ × ℝ) => (p.2, q t * p.1))
    (s := fun _ => univ) (f := fun t => (w t, w' t)) (g := fun _ => ((0 : ℝ), (0 : ℝ))) hlip ht₀
    (fun t ht => ⟨(hw t (lt_trans (by positivity) ht.1)).prodMk
      (hw' t (lt_trans (by positivity) ht.1)), mem_univ _⟩)
    (fun t ht => ⟨(hasDerivAt_const t _).congr_deriv (by ext <;> simp), mem_univ _⟩)
    (by simp [h t₀ ⟨by positivity, ht₀δ⟩, hw'0])
  have := @key ρ ⟨by linarith, by linarith⟩
  simpa using congrArg Prod.fst this

/-!

## E. Completeness and quantisation

-/

/-- **Completeness of the regular radial solutions.** Every solution of the radial equation
`u'' = (l(l+1)/ρ² - 2/ρ + κ²) u` on `(0, ∞)` with `u(ρ) → 0` as `ρ → 0⁺` is of the form
`ρ^(l+1) e^(-κρ) Σ_k c_k ρ^k` with an everywhere convergent series whose coefficients satisfy the
recursion; if `u` is not identically zero on `(0, ∞)`, then `c_0 ≠ 0`. -/
lemma radial_regular_solution {u : ℝ → ℝ}
    (hd : ∀ ρ, 0 < ρ → DifferentiableAt ℝ u ρ ∧ DifferentiableAt ℝ (deriv u) ρ)
    (hode : ∀ ρ, 0 < ρ → deriv (deriv u) ρ =
      ((l : ℝ) * (l + 1) / ρ ^ 2 - 2 / ρ + κ ^ 2) * u ρ)
    (h0 : Tendsto u (𝓝[>] 0) (𝓝 0)) :
    ∃ c : ℕ → ℝ, EntireCoeff c ∧ RadialRec κ l c ∧ (∀ ρ, 0 < ρ → u ρ = radialSeries κ l c ρ) ∧
      ((∃ ρ, 0 < ρ ∧ u ρ ≠ 0) → c 0 ≠ 0) := by
  have hu : ∀ ρ, 0 < ρ → HasDerivAt u (deriv u ρ) ρ := fun ρ hρ => (hd ρ hρ).1.hasDerivAt
  have hu' : ∀ ρ, 0 < ρ → HasDerivAt (deriv u) (radialPot κ l ρ * u ρ) ρ := fun ρ hρ => by
    have h := (hd ρ hρ).2.hasDerivAt
    rwa [hode ρ hρ] at h
  obtain ⟨δ, hδ, A, hA⟩ := exists_eqOn_near_zero_of_tendsto hu hu' h0
  have hq : ContinuousOn (radialPot κ l) (Ioi 0) := by
    unfold radialPot
    exact ((continuousOn_const.div (continuous_pow 2).continuousOn
      fun x hx => pow_ne_zero 2 (ne_of_gt hx)).sub
      (continuousOn_const.div continuousOn_id fun x hx => ne_of_gt hx)).add continuousOn_const
  -- `u - A u₁` vanishes near `0`, hence on `(0, ∞)`
  have hw := eqOn_zero_of_eqOn_Ioo (w := fun ρ => u ρ - A * radialSeries κ l (regCoeff κ l) ρ)
    (w' := fun ρ => deriv u ρ - A * radialSeriesD κ l (regCoeff κ l) ρ) hq
    (fun ρ hρ => (hu ρ hρ).sub ((hasDerivAt_radialSeries entireCoeff_regCoeff ρ).const_mul A))
    (fun ρ hρ => ((hu' ρ hρ).sub ((radial_ode_of_radialRec entireCoeff_regCoeff
      radialRec_regCoeff hρ).const_mul A)).congr_deriv (by ring))
    hδ fun ρ hρ => by simp [hA ρ hρ]
  have hser : ∀ ρ, radialSeries κ l (fun k => A * regCoeff κ l k) ρ =
      A * radialSeries κ l (regCoeff κ l) ρ := fun ρ => by
    simp only [radialSeries, psum_const_mul]
    ring
  refine ⟨fun k => A * regCoeff κ l k, entireCoeff_regCoeff.const_mul A, fun k => ?_,
    fun ρ hρ => ?_, fun ⟨ρ, hρ, hne⟩ => ?_⟩
  · linear_combination A * radialRec_regCoeff (κ := κ) (l := l) k
  · rw [hser]
    linarith [hw ρ hρ]
  · simp only [regCoeff_zero, mul_one]
    rintro rfl
    exact hne (by linarith [hw ρ hρ, zero_mul (radialSeries κ l (regCoeff κ l) ρ)])

/-- **Quantisation of the hydrogen levels without ansatz.** A non-zero square integrable solution
of the radial equation on `(0, ∞)` with energy `-κ²`, `κ > 0`, and `u(ρ) → 0` as `ρ → 0⁺` exists
only for `κ = 1/ν` with a natural number `ν > l`, and is then a multiple of `u_{νl}`. -/
lemma radial_quantization_of_tendsto (hκ : 0 < κ) {u : ℝ → ℝ}
    (hd : ∀ ρ, 0 < ρ → DifferentiableAt ℝ u ρ ∧ DifferentiableAt ℝ (deriv u) ρ)
    (hode : ∀ ρ, 0 < ρ → deriv (deriv u) ρ =
      ((l : ℝ) * (l + 1) / ρ ^ 2 - 2 / ρ + κ ^ 2) * u ρ)
    (h0 : Tendsto u (𝓝[>] 0) (𝓝 0)) (hint : IntegrableOn (fun ρ => u ρ ^ 2) (Ioi 0))
    (hne : ∃ ρ, 0 < ρ ∧ u ρ ≠ 0) :
    ∃ ν : ℕ, l < ν ∧ κ = 1 / (ν : ℝ) ∧ ∃ C : ℝ, ∀ ρ, 0 < ρ → u ρ = C * radialU ν l ρ := by
  obtain ⟨c, hc, hrec, hu, hc0⟩ := radial_regular_solution hd hode h0
  have hD : deriv (radialSeries κ l c) = radialSeriesD κ l c :=
    funext fun x => (hasDerivAt_radialSeries hc x).deriv
  obtain ⟨ν, hν, hκν, C, hC⟩ := radial_quantization hκ hc (hc0 hne)
    (fun ρ hρ => by rw [hD, (radial_ode_of_radialRec hc hrec hρ).deriv]; rfl)
    (hint.congr_fun (fun ρ hρ => by simp only [hu ρ hρ]) measurableSet_Ioi)
  exact ⟨ν, hν, hκν, C, fun ρ hρ => (hu ρ hρ).trans (hC ρ)⟩

end PhyslibAlpha.Hydrogen
