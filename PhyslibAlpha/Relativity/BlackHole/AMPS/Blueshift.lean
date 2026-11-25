/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The frequency of an outgoing radial Hawking ray

Radial propagation in Schwarzschild.

## i. Overview

AMPS, arXiv:1207.3123v4, §2 before Eq. (2.2) and Fig. 1, trace an outgoing
wavepacket back to a region where its local frequency greatly exceeds its
asymptotic frequency but can still lie below the Planck scale.

Here we specialize to the radial geometric-optics carrier in a stationary
Schwarzschild exterior and an observer falling radially from rest at infinity.
In units with light speed one, the radial metric in ingoing Eddington–Finkelstein
coordinates is `-f dv² + 2 dv dr`, where `f = 1 - rs/r` (Tong, *General
Relativity*, §6.1.3, Eq. 6.263). The outgoing phase has covector
`k = -ωinf dv + (2 ωinf / f) dr`. Its Killing frequency is the same parameter
at every radius. The observer's velocity is the infalling branch of the unit
timelike, unit Killing-energy first integrals. Below we check both first
integrals, the outgoing null condition and the locally measured frequency.
The frequency pertains to the carrier. Propagation of an extended quantum
wavepacket, scattering off the angular-momentum barrier, and detector dynamics
are separate physical questions.

AMPS §3 discusses a stretched horizon at a Planckian distance from the event
horizon. We specify this distance on a Schwarzschild static slice. The
regular coordinate `x = √(r - rs)` gives its radial line element
`2 √(rs + x²) dx`, including a finite one-sided value at the horizon.

## ii. Key results

* `outgoing_null`
* `infaller_first_integrals`

## iii. Table of contents

- A. Radial propagation in Schwarzschild

## iv. References

* [ref: Almheiri2013]
* [ref: TongGeneralRelativitySchwarzschild]

## A. Radial propagation in Schwarzschild
-/

@[expose] public section

namespace AMPS.Blueshift

noncomputable section

/-- Radial ingoing-Eddington–Finkelstein components `(v,r)` of the outgoing
wave covector, with frequency `ωinf` relative to the stationary Killing field
normalized at infinity. -/
def outgoingCovector (rs r ωinf : ℝ) : ℝ × ℝ :=
  (-ωinf, 2 * ωinf / (1 - rs / r))

/-- Contravariant radial velocity `(dv/dτ, dr/dτ)` of the infaller from rest
at infinity. -/
def infallerVelocity (rs r : ℝ) : ℝ × ℝ :=
  (1 / (1 + Real.sqrt (rs / r)), -Real.sqrt (rs / r))

/-- Frequency measured in the freely falling frame, the negative contraction
of the wave covector with the observer's velocity. -/
def infallFrequency (rs r ωinf : ℝ) : ℝ :=
  let k := outgoingCovector rs r ωinf
  let u := infallerVelocity rs r;
  -(k.1 * u.1 + k.2 * u.2)

private lemma exterior_factors {rs r : ℝ} (hs : 0 < rs) (hr : rs < r) :
    0 < 1 - Real.sqrt (rs / r) ∧
    1 - rs / r = (1 - Real.sqrt (rs / r)) * (1 + Real.sqrt (rs / r)) := by
  have hratio := (div_lt_one (hs.trans hr)).mpr hr
  have hsq := Real.sq_sqrt (div_nonneg hs.le (hs.trans hr).le)
  constructor
  · nlinarith [Real.sqrt_nonneg (rs / r)]
  · nlinarith

/-- Raising the wave covector using the inverse metric gives zero norm and
positive outward radial component `kʳ = ωinf` for positive `ωinf`. -/
lemma outgoing_null {rs r : ℝ} (hs : 0 < rs) (hr : rs < r) (ωinf : ℝ) :
    let k := outgoingCovector rs r ωinf
    let f := 1 - rs / r
    2 * k.1 * k.2 + f * k.2 ^ 2 = 0 ∧ k.1 + f * k.2 = ωinf := by
  have hf : 1 - rs / r ≠ 0 := ne_of_gt (sub_pos.mpr ((div_lt_one (hs.trans hr)).mpr hr))
  dsimp [outgoingCovector]
  constructor <;> field_simp [hf] <;> ring

/-- The infaller has unit timelike norm and unit specific Killing energy,
the value for rest at infinity. -/
lemma infaller_first_integrals {rs r : ℝ} (hs : 0 < rs) (hr : rs < r) :
    let u := infallerVelocity rs r
    let f := 1 - rs / r;
    -f * u.1 ^ 2 + 2 * u.1 * u.2 = -1 ∧ f * u.1 - u.2 = 1 := by
  have hp : 0 < 1 + Real.sqrt (rs / r) := by linarith [Real.sqrt_nonneg (rs / r)]
  dsimp [infallerVelocity]
  rw [(exterior_factors hs hr).2]
  constructor <;> field_simp [ne_of_gt hp] <;> ring

/-- Along a radial worldline parametrized by proper time, the inward
unit-Killing-energy velocity field obeys the Schwarzschild radial geodesic
equation `d uʳ / dτ = -rs / (2 r²)`. The velocity hypothesis selects the
observer falling from rest at infinity at the event. -/
lemma infaller_radial_acceleration {rs τ : ℝ} {ρ : ℝ → ℝ}
    (hs : 0 < rs) (hr : rs < ρ τ)
    (hfall : HasDerivAt ρ (infallerVelocity rs (ρ τ)).2 τ) :
    HasDerivAt (fun s => (infallerVelocity rs (ρ s)).2) (-rs / (2 * ρ τ ^ 2)) τ := by
  have hp := hs.trans hr
  have hq := div_pos hs hp
  have hd := HasDerivAt.neg (((hasDerivAt_const τ rs).fun_div hfall hp.ne').sqrt hq.ne')
  apply hd.congr_deriv
  dsimp [infallerVelocity]
  field_simp [hp.ne', (Real.sqrt_pos.2 hq).ne']
  ring

/-- The local frequency of the very same outgoing ray as a function of radius. -/
lemma infallFrequency_eq {rs r : ℝ} (hs : 0 < rs) (hr : rs < r) (ωinf : ℝ) :
    infallFrequency rs r ωinf = ωinf / (1 - Real.sqrt (rs / r)) := by
  obtain ⟨hm, hf⟩ := exterior_factors hs hr
  have hp : 0 < 1 + Real.sqrt (rs / r) := by linarith [Real.sqrt_nonneg (rs / r)]
  dsimp [infallFrequency, outgoingCovector, infallerVelocity]
  rw [hf]
  field_simp [ne_of_gt hm, ne_of_gt hp]
  ring

/-- Schwarzschild tortoise coordinate on the exterior, up to an additive constant. -/
def tortoise (rs r : ℝ) : ℝ := r + rs * Real.log (r - rs)

/-- Outgoing null coordinate in the ingoing Eddington–Finkelstein chart. -/
def retarded (rs v r : ℝ) : ℝ := v - 2 * tortoise rs r

/-- The tortoise derivative is the inverse redshift factor in the static metric. -/
lemma hasDerivAt_tortoise {rs r : ℝ} (hrs : 0 < rs) (hr : rs < r) :
    HasDerivAt (tortoise rs) (1 / (1 - rs / r)) r := by
  have hsub := sub_pos.mpr hr
  have hrad := hrs.trans hr
  have hlog := ((hasDerivAt_id r).sub_const rs).log hsub.ne'
  have ht := (hasDerivAt_id r).add (hlog.const_mul rs)
  apply ht.congr_deriv
  change 1 + rs * (1 / (r - rs)) = 1 / (1 - rs / r)
  rw [show 1 - rs / r = (r - rs) / r by field_simp [hrad.ne']]
  field_simp [hsub.ne', hrad.ne']
  ring

/-- Trace-back is along the level sets of the same retarded coordinate that labels
the asymptotic packet. Here a ray is any parametrized outward solution with
dv/dr = 2/(1−rs/r), and the theorem proves conservation locally. -/
lemma retarded_constant_along_ray {rs r : ℝ} {v : ℝ → ℝ} (hrs : 0 < rs)
    (hr : rs < r) (hv : HasDerivAt v (2 / (1 - rs / r)) r) :
    HasDerivAt (fun ρ => retarded rs (v ρ) ρ) 0 r := by
  apply (hv.sub ((hasDerivAt_tortoise hrs hr).const_mul 2)).congr_deriv
  ring

/-- An arbitrary differentiable retarded profile is sampled along the infaller
with the same instantaneous dilation factor as a monochromatic phase.
This statement propagates the full retarded profile in the radial model. -/
lemma retarded_profile_along_infaller {rs τ : ℝ} {v ρ : ℝ → ℝ} {profile : ℝ → ℂ}
    {profileRate : ℂ} (hrs : 0 < rs) (hr : rs < ρ τ)
    (hv : HasDerivAt v (infallerVelocity rs (ρ τ)).1 τ)
    (hρ : HasDerivAt ρ (infallerVelocity rs (ρ τ)).2 τ)
    (hp : HasDerivAt profile profileRate (retarded rs (v τ) (ρ τ))) :
    HasDerivAt (fun t => profile (retarded rs (v t) (ρ t)))
      ((infallFrequency rs (ρ τ) 1 : ℂ) * profileRate) τ := by
  have hd := hv.sub (((hasDerivAt_tortoise hrs hr).comp τ hρ).const_mul 2)
  have heq :
      (infallerVelocity rs (ρ τ)).1 -
        2 * (1 / (1 - rs / ρ τ) * (infallerVelocity rs (ρ τ)).2) =
        infallFrequency rs (ρ τ) 1 := by
    simp only [infallFrequency, outgoingCovector, neg_mul, one_mul, mul_one]
    ring
  exact (hp.scomp τ (hd.congr_deriv heq)).congr_deriv (by simp only [Complex.real_smul])

open Filter Topology

/-- Far from the hole, the infaller's measured frequency converges to the
conserved Killing frequency that labels the ray. -/
lemma tendsto_infallFrequency_at_infinity {rs : ℝ} (hs : 0 < rs) (ωinf : ℝ) :
    Tendsto (fun r ↦ infallFrequency rs r ωinf) atTop (𝓝 ωinf) := by
  have hratio : Tendsto (fun r : ℝ ↦ rs / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsqrt : Tendsto (fun r : ℝ ↦ Real.sqrt (rs / r)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  have hlim : Tendsto (fun r : ℝ ↦ ωinf / (1 - Real.sqrt (rs / r))) atTop (𝓝 ωinf) := by
    simpa [Pi.div_def] using (tendsto_const_nhds (x := ωinf)).div (hsqrt.const_sub 1) (by norm_num)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop rs] with r hr using (infallFrequency_eq hs hr ωinf).symm

/-- At one exterior event the same positive factor rescales every frequency
in a radial packet's asymptotic band. This concerns its local frequencies in
geometric optics and permits packets with nonzero bandwidth. -/
lemma packet_frequency_band {rs r lo ω hi : ℝ} (hs : 0 < rs) (hr : rs < r)
    (hlo : lo ≤ ω) (hhi : ω ≤ hi) :
    lo / (1 - Real.sqrt (rs / r)) ≤ infallFrequency rs r ω ∧
    infallFrequency rs r ω ≤ hi / (1 - Real.sqrt (rs / r)) := by
  rw [infallFrequency_eq hs hr]
  have hden := (exterior_factors hs hr).1.le
  exact ⟨div_le_div_of_nonneg_right hlo hden, div_le_div_of_nonneg_right hhi hden⟩

/-- Radius at which the outgoing carrier is observed with the prescribed
local frequency `ωstar > ωinf > 0`. -/
def radiusForFrequency (rs ωinf ωstar : ℝ) : ℝ :=
  rs / (1 - ωinf / ωstar) ^ 2

/-- A target blueshift selects an exterior radius and the covector-velocity
contraction there attains the target frequency. -/
lemma radiusForFrequency_spec {rs ωinf ωstar : ℝ}
    (hs : 0 < rs) (hω : 0 < ωinf) (hhigh : ωinf < ωstar) :
    rs < radiusForFrequency rs ωinf ωstar ∧
    infallFrequency rs (radiusForFrequency rs ωinf ωstar) ωinf = ωstar := by
  have ht := hω.trans hhigh
  let a := 1 - ωinf / ωstar
  have ha : 0 < a := sub_pos.mpr ((div_lt_one ht).mpr hhigh)
  have ha' : a < 1 := by dsimp [a]; linarith [div_pos hω ht]
  have hasq : a ^ 2 < 1 := by nlinarith [mul_pos ha (sub_pos.mpr ha')]
  change rs < rs / a ^ 2 ∧ infallFrequency rs (rs / a ^ 2) ωinf = ωstar
  have hext : rs < rs / a ^ 2 := (lt_div_iff₀ (sq_pos_of_pos ha)).mpr (by
    simpa using mul_lt_mul_of_pos_left hasq hs)
  refine ⟨hext, ?_⟩
  rw [infallFrequency_eq hs hext, div_div_eq_mul_div, mul_div_cancel_left₀ _ hs.ne',
      Real.sqrt_sq ha.le]
  dsimp [a]
  rw [sub_sub_cancel, div_div_eq_mul_div, mul_div_cancel_left₀ _ hω.ne']

/-- Lower bound on the radial carrier's areal-coordinate separation from the
horizon at the required blueshift. An exterior cutoff with coordinate thickness
at most this lower bound lies strictly inside the selected radius. -/
lemma radiusForFrequency_radial_margin {rs ωinf ωstar : ℝ}
    (hs : 0 < rs) (hω : 0 < ωinf) (hhigh : ωinf < ωstar) :
    rs * (ωinf / ωstar) < radiusForFrequency rs ωinf ωstar - rs := by
  let q := ωinf / ωstar
  have ht := hω.trans hhigh
  have hq : 0 < q := div_pos hω ht
  have hsmall : q < 1 := (div_lt_one ht).mpr hhigh
  have hden : 0 < (1 - q) ^ 2 := sq_pos_of_pos (sub_pos.mpr hsmall)
  have hfactor : (q + 1) * (1 - q) ^ 2 < 1 := by
    nlinarith [mul_pos (sq_pos_of_pos hq) (sub_pos.mpr hsmall)]
  change rs * q < rs / (1 - q) ^ 2 - rs
  apply (lt_sub_iff_add_lt).2
  apply (lt_div_iff₀ hden).2
  calc
    (rs * q + rs) * (1 - q) ^ 2 = rs * ((q + 1) * (1 - q) ^ 2) := by ring
    _ < rs * 1 := mul_lt_mul_of_pos_left hfactor hs
    _ = rs := mul_one rs

/-- Squared radial line element on a Schwarzschild static slice, under
`r = rs + x²`. At fixed Schwarzschild time and angles the radial metric
is `dr² / (1 - rs/r)`, and the radial coordinate derivative is `2x`. -/
lemma static_radial_metric_pullback {rs x : ℝ} (hs : 0 < rs) (hx : 0 < x) :
    (2 * x) ^ 2 / (1 - rs / (rs + x ^ 2)) = (2 * Real.sqrt (rs + x ^ 2)) ^ 2 := by
  have hp := add_pos_of_pos_of_nonneg hs (sq_nonneg x)
  have hnon : 1 - rs / (rs + x ^ 2) ≠ 0 :=
    (sub_pos.mpr ((div_lt_one hp).mpr (lt_add_of_pos_right _ (sq_pos_of_pos hx)))).ne'
  rw [mul_pow 2 (Real.sqrt _), Real.sq_sqrt hp.le]
  field_simp [hnon, hp.ne']
  ring

/-- Outward proper radial length from the horizon to areal radius `r ≥ rs`
along the Schwarzschild static slice. The integral uses the continuous length
density in the regular coordinate `x = √(r - rs)`. -/
def staticProperDistance (rs r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.sqrt (r - rs), 2 * Real.sqrt (rs + x ^ 2)

private lemma continuous_radial_density (rs : ℝ) :
    Continuous (fun x : ℝ => 2 * Real.sqrt (rs + x ^ 2)) :=
  continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))

/-- The proper distance is bounded by the endpoint values of the radial
length density times the coordinate interval. Both bounds have leading term
`2 √rs √(r - rs)` as `r` approaches the horizon from outside. -/
lemma staticProperDistance_bounds {rs r : ℝ} (hr : rs ≤ r) :
    2 * Real.sqrt rs * Real.sqrt (r - rs) ≤ staticProperDistance rs r ∧
    staticProperDistance rs r ≤ 2 * Real.sqrt r * Real.sqrt (r - rs) := by
  let b := Real.sqrt (r - rs)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hsq : b ^ 2 = r - rs := Real.sq_sqrt (sub_nonneg.mpr hr)
  have hi := (continuous_radial_density rs).intervalIntegrable (μ := MeasureTheory.volume) 0 b
  constructor
  · calc
      _ = ∫ _ in (0 : ℝ)..b, 2 * Real.sqrt rs := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
      _ ≤ _ := intervalIntegral.integral_mono_on hb intervalIntegrable_const hi
        (fun x _ => mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_add_of_nonneg_right
          (sq_nonneg x))) (by norm_num))
  · calc
      _ ≤ ∫ _ in (0 : ℝ)..b, 2 * Real.sqrt r := by
        apply intervalIntegral.integral_mono_on hb hi intervalIntegrable_const
        intro x hx
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by
          nlinarith [sq_le_sq' (by linarith [hx.1] : -b ≤ x) hx.2])) (by norm_num)
      _ = _ := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]

/-- A specified static proper distance labels at most one exterior spherical
surface, and larger proper distance puts a carrier farther out in areal radius. -/
lemma staticProperDistance_strictMonoOn {rs : ℝ} (hs : 0 < rs) :
    StrictMonoOn (staticProperDistance rs) (Set.Ici rs) := by
  intro a ha b _ hab
  let x := Real.sqrt (a - rs)
  let y := Real.sqrt (b - rs)
  have hxy : x < y := Real.sqrt_lt_sqrt (sub_nonneg.mpr ha) (sub_lt_sub_right hab rs)
  have hc := continuous_radial_density rs
  have hpos : 0 < ∫ t in x..y, 2 * Real.sqrt (rs + t ^ 2) := by
    apply intervalIntegral.integral_pos hxy hc.continuousOn
    · exact fun t _ => mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · exact ⟨x, ⟨le_rfl, hxy.le⟩, mul_pos (by norm_num)
        (Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg hs (sq_nonneg _)))⟩
  change (∫ t in (0 : ℝ)..x, 2 * Real.sqrt (rs + t ^ 2)) < ∫ t in (0 : ℝ)..y, _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 x) (hc.intervalIntegrable x y)]
  linarith

/-- Every positive proper cutoff below the carrier's proper distance selects
an actual, unique sphere strictly between the horizon and the carrier. -/
lemma existsUnique_stretched_radius {rs r ℓ : ℝ} (hs : 0 < rs) (hr : rs < r)
    (hℓ : 0 < ℓ) (hcut : ℓ < staticProperDistance rs r) :
    ∃! s, (rs < s ∧ s < r) ∧ staticProperDistance rs s = ℓ := by
  have hc : Continuous (staticProperDistance rs) :=
    (intervalIntegral.continuous_primitive
      (continuous_radial_density rs).intervalIntegrable 0).comp
        (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))
  have hz : staticProperDistance rs rs = 0 := by simp [staticProperDistance]
  obtain ⟨s, hsI, heq⟩ := intermediate_value_Ioo hr.le hc.continuousOn
    ⟨hz ▸ hℓ, hcut⟩
  exact ⟨s, ⟨hsI, heq⟩, fun t ht => (staticProperDistance_strictMonoOn hs).injOn
    ht.1.1.le hsI.1.le (ht.2.trans heq.symm)⟩

/-- A lower bound on the areal separation implies a bound on proper
distance after integrating the static spatial metric. -/
lemma staticProperDistance_of_radial_margin {rs r q : ℝ} (hs : 0 < rs) (hq : 0 < q)
    (hgap : rs * q < r - rs) :
    2 * rs * Real.sqrt q < staticProperDistance rs r := by
  have hlt := Real.sqrt_lt_sqrt (mul_pos hs hq).le hgap
  rw [Real.sqrt_mul hs.le] at hlt
  have hbound := (staticProperDistance_bounds (show rs ≤ r by linarith [mul_pos hs hq])).1
  calc
    _ = 2 * Real.sqrt rs * (Real.sqrt rs * Real.sqrt q) := by
      calc
        _ = 2 * (Real.sqrt rs * Real.sqrt rs) * Real.sqrt q := by rw [Real.mul_self_sqrt hs.le]
        _ = _ := by ring
    _ < _ := mul_lt_mul_of_pos_left hlt (mul_pos (by norm_num) (Real.sqrt_pos.2 hs))
    _ ≤ _ := hbound

/-- The frequency-selected carrier lies beyond every static proper-distance
cutoff at most `2 rs √(ωinf / ωstar)`. This sufficient scale follows from
the integrated metric and the radius selected by the unit-energy infaller. -/
lemma radiusForFrequency_proper_margin {rs ωinf ωstar : ℝ}
    (hs : 0 < rs) (hω : 0 < ωinf) (hhigh : ωinf < ωstar) :
    2 * rs * Real.sqrt (ωinf / ωstar) <
      staticProperDistance rs (radiusForFrequency rs ωinf ωstar) := by
  exact staticProperDistance_of_radial_margin hs (div_pos hω (hω.trans hhigh))
    (radiusForFrequency_radial_margin hs hω hhigh)

/-- Planck units, a Schwarzschild radius of at least one Planck length, and
the Hawking-scale carrier convention `ωinf = 1/rs`. Every target between
the asymptotic frequency and one Planck frequency is attained outside the
one-Planck-length stretched surface. Its proper distance exceeds
`2 √(rs / ωstar)`. The carrier convention fixes an order-one factor. -/
lemma hawking_carrier_outside_planck_surface {rs ωstar : ℝ} (hsize : 1 ≤ rs)
    (hhigh : 1 / rs < ωstar) (hsub : ωstar < 1) :
    let r := radiusForFrequency rs (1 / rs) ωstar
    ∃ s, rs < s ∧ s < r ∧ staticProperDistance rs s = 1 ∧
      2 * Real.sqrt (rs / ωstar) < staticProperDistance rs r ∧
      infallFrequency rs r (1 / rs) = ωstar := by
  have hs := lt_of_lt_of_le zero_lt_one hsize
  have hω := one_div_pos.mpr hs
  have ht := hω.trans hhigh
  have hq := div_pos hω ht
  have hsquare : (rs * Real.sqrt (1 / rs / ωstar)) ^ 2 = rs / ωstar := by
    rw [mul_pow, Real.sq_sqrt hq.le]
    field_simp
  have hroot : Real.sqrt (rs / ωstar) = rs * Real.sqrt (1 / rs / ωstar) := by
    rw [← hsquare, Real.sqrt_sq (mul_nonneg hs.le (Real.sqrt_nonneg _))]
  have hproper := radiusForFrequency_proper_margin hs hω hhigh
  rw [mul_assoc, ← hroot] at hproper
  have hunit : 1 ≤ Real.sqrt (rs / ωstar) :=
    Real.one_le_sqrt.mpr ((one_le_div ht).mpr (hsub.le.trans hsize))
  have ⟨hr, hfreq⟩ := radiusForFrequency_spec hs hω hhigh
  obtain ⟨s, ⟨horder, heq⟩, _⟩ := existsUnique_stretched_radius hs hr zero_lt_one
    ((by linarith : 1 < 2 * Real.sqrt (rs / ωstar)).trans hproper)
  exact ⟨s, horder.1, horder.2, heq, hproper, hfreq⟩

/-- An arbitrarily specified lower frequency above `ωinf` and a higher cutoff
leave an exterior radius where the local carrier frequency lies strictly between
them. For a Hawking-frequency packet the lower scale can be a large multiple
of `1/rs`, and the cutoff can be the Planck frequency. -/
lemma exists_radius_in_window {rs ωinf lower cutoff : ℝ}
    (hs : 0 < rs) (hω : 0 < ωinf) (hl : ωinf < lower) (hc : lower < cutoff) :
    ∃ r, rs < r ∧ lower < infallFrequency rs r ωinf ∧ infallFrequency rs r ωinf < cutoff := by
  let target := (lower + cutoff) / 2
  have hlt : lower < target := by dsimp [target]; linarith
  obtain ⟨hr, heq⟩ := radiusForFrequency_spec hs hω (hl.trans hlt)
  exact ⟨_, hr, heq.symm ▸ hlt, heq.symm ▸ (show target < cutoff by dsimp [target]; linarith)⟩

/-- Example in Planck units: a Schwarzschild radius of one million, a Hawking-scale
asymptotic frequency `1/rs`, and a local carrier frequency one thousand times
larger and strictly below the Planck frequency. -/
lemma subplanckian_example :
    ∃ r : ℝ, 10 ^ 6 < r ∧
      infallFrequency (10 ^ 6) r (1 / 10 ^ 6) = 1 / 10 ^ 3 ∧
      (1 / 10 ^ 3 : ℝ) < 1 := by
  obtain ⟨hr, hfreq⟩ := radiusForFrequency_spec
    (rs := (10 ^ 6 : ℝ)) (ωinf := 1 / 10 ^ 6) (ωstar := 1 / 10 ^ 3)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, hr, hfreq, by norm_num⟩

end

end AMPS.Blueshift
