/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube
public import PhyslibAlpha.CondensedMatter.TightBindingChain.LongChainMonotonicity
/-!

# The NRS angle and the volumetric quantum of the open tight binding cube

## i. Overview

In the maximal current state the energy and position fluctuations are uncorrelated, so the
pairing `ω(δH δX)` reduces to the bracket term `a t cos (π / (N + 1))`. Its modulus over
`σ_H σ_X` is the cosine of the angle between the two fluctuations: the NRS angle, with
`cos θ_NRS = 1 / C_Nava`. It vanishes exactly for `N = 2, 3`, opens from four sites on, grows
strictly with `N` and stays below `arccos (1 / √(π² / 3 - 2))`.

The excess `δ = C_Nava - 1` is the dimensional quantum of an axis. A cube `Nx × Ny × Nz` carries
one constant per axis, so its volumetric quantum is `δ(Nx) δ(Ny) δ(Nz)`: it vanishes iff some axis
has `2` or `3` sites, is positive from `4 × 4 × 4` on, grows strictly in each axis and stays
below `(√(π² / 3 - 2) - 1)³`.

## ii. Key results

- `angleNRS` : the angle between the energy and position fluctuations.
- `angleNRS_eq` : `θ_NRS = arccos (1 / C_Nava)`.
- `angleNRS_eq_zero_iff`, `angleNRS_pos` : it vanishes iff `N = 2, 3`, and opens from `N = 4`.
- `angleNRS_lt_angleNRS`, `angleNRS_lt` : it grows strictly with `N`, below its limit.
- `dimQuantum` : the dimensional quantum `δ = C_Nava - 1`.
- `angleNRS_eq_dimQuantum` : `θ_NRS = arccos (1 / (1 + δ))`.
- `volQuantum` : the volumetric quantum `δ(Nx) δ(Ny) δ(Nz)` of the cube.
- `volQuantum_eq_zero_iff`, `volQuantum_pos` : it vanishes iff some axis has `2` or `3` sites.
- `volQuantum_lt_volQuantum_x` (and `y`, `z`), `volQuantum_lt` : strict growth in each axis,
  below its limit.

## iii. Table of contents

- A. The NRS angle
- B. The dimensional quantum
- C. The volumetric quantum

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open ProbabilisticTheory UnitalPositiveLinearMap

variable (T : TightBindingChain)

/-!

## A. The NRS angle

-/

/-- The NRS angle: the angle between the energy and position fluctuations in the maximal current
state, `arccos (‖ω(δH δX)‖ / (σ_H σ_X))`. -/
noncomputable def angleNRS : ℝ :=
  Real.arccos (‖T.maxCurrentVectorState
      ((centered T.maxCurrentVectorState T.openHamiltonianObservable : _) *
        centered T.maxCurrentVectorState T.positionObservable)‖ /
    √(variance T.maxCurrentVectorState T.openHamiltonianObservable *
      variance T.maxCurrentVectorState T.positionObservable))

/-- **The NRS angle.** `cos θ_NRS = 1 / C_Nava`. -/
theorem angleNRS_eq (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.angleNRS = Real.arccos (1 / T.CNava) := by
  have hC := (zero_lt_one.trans_le (T.one_le_CNava ht hN)).ne'
  have hB : |T.a * T.t * Real.cos (Real.pi / (T.N + 1))| ≠ 0 := fun h => by
    rw [CNava, h, div_zero] at hC
    exact hC rfl
  rw [angleNRS, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, normSq_centered_pairing,
    covariance_maxCurrentState, expectation_bracket_maxCurrentState, CNava, one_div_div]
  congr 2
  rw [sq, zero_mul, zero_add, neg_sq, Real.sqrt_sq_eq_abs]

/-- The NRS angle vanishes exactly for `N = 2` and `N = 3`. -/
lemma angleNRS_eq_zero_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.angleNRS = 0 ↔ T.N = 2 ∨ T.N = 3 := by
  have h1 := T.one_le_CNava ht hN
  rw [T.angleNRS_eq ht hN, Real.arccos_eq_zero, le_div_iff₀ (by linarith), one_mul,
    ← T.CNava_eq_one_iff ht hN]
  exact ⟨fun h => le_antisymm h h1, fun h => h.le⟩

/-- From four sites on, the NRS angle is open. -/
lemma angleNRS_pos (ht : T.t ≠ 0) (hN : 4 ≤ T.N) : 0 < T.angleNRS :=
  (Real.arccos_nonneg _).lt_of_ne fun h => by
    rcases (T.angleNRS_eq_zero_iff ht (by omega)).mp h.symm with h | h <;> omega

private lemma arccos_inv_lt {C C' : ℝ} (hC : 1 ≤ C) (hCC' : C < C') :
    Real.arccos (1 / C) < Real.arccos (1 / C') :=
  Real.arccos_lt_arccos (by have := one_div_pos.mpr (by linarith : 0 < C'); linarith)
    (one_div_lt_one_div_of_lt (by linarith) hCC') (div_le_one_of_le₀ hC (by linarith))

/-- From four sites on, the NRS angle grows strictly with the number of sites. -/
theorem angleNRS_lt_angleNRS {T T' : TightBindingChain} (ht : T.t ≠ 0) (ht' : T'.t ≠ 0)
    (hN : 4 ≤ T.N) (hNN' : T.N < T'.N) : T.angleNRS < T'.angleNRS := by
  rw [T.angleNRS_eq ht (by omega), T'.angleNRS_eq ht' (by omega)]
  exact arccos_inv_lt (T.one_le_CNava ht (by omega)) (CNava_lt_CNava ht ht' hN hNN')

/-- From four sites on, the NRS angle stays below `arccos (1 / √(π² / 3 - 2))`. -/
theorem angleNRS_lt (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.angleNRS < Real.arccos (1 / √(Real.pi ^ 2 / 3 - 2)) := by
  rw [T.angleNRS_eq ht (by omega)]
  exact arccos_inv_lt (T.one_le_CNava ht (by omega)) (T.CNava_lt_sqrt_pi_sq_div_three_sub_two ht hN)

/-!

## B. The dimensional quantum

-/

/-- The dimensional quantum of the chain: the excess `C_Nava - 1` over saturation. -/
noncomputable def dimQuantum : ℝ := T.CNava - 1

lemma dimQuantum_nonneg (ht : T.t ≠ 0) (hN : 2 ≤ T.N) : 0 ≤ T.dimQuantum :=
  sub_nonneg.mpr (T.one_le_CNava ht hN)

/-- The dimensional quantum vanishes exactly for `N = 2` and `N = 3`. -/
lemma dimQuantum_eq_zero_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.dimQuantum = 0 ↔ T.N = 2 ∨ T.N = 3 := by
  rw [dimQuantum, sub_eq_zero, T.CNava_eq_one_iff ht hN]

/-- From four sites on, the dimensional quantum is positive. -/
lemma dimQuantum_pos (ht : T.t ≠ 0) (hN : 4 ≤ T.N) : 0 < T.dimQuantum :=
  sub_pos.mpr (T.one_lt_CNava ht hN)

/-- From four sites on, the dimensional quantum grows strictly with the number of sites. -/
lemma dimQuantum_lt_dimQuantum {T T' : TightBindingChain} (ht : T.t ≠ 0) (ht' : T'.t ≠ 0)
    (hN : 4 ≤ T.N) (hNN' : T.N < T'.N) : T.dimQuantum < T'.dimQuantum :=
  sub_lt_sub_right (CNava_lt_CNava ht ht' hN hNN') 1

/-- From four sites on, the dimensional quantum stays below `√(π² / 3 - 2) - 1`. -/
lemma dimQuantum_lt (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.dimQuantum < √(Real.pi ^ 2 / 3 - 2) - 1 :=
  sub_lt_sub_right (T.CNava_lt_sqrt_pi_sq_div_three_sub_two ht hN) 1

/-- The dimensional quantum fixes the NRS angle: `θ_NRS = arccos (1 / (1 + δ))`. -/
lemma angleNRS_eq_dimQuantum (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.angleNRS = Real.arccos (1 / (1 + T.dimQuantum)) := by
  rw [T.angleNRS_eq ht hN, dimQuantum, add_sub_cancel]

/-!

## C. The volumetric quantum

-/

variable (Tx Ty Tz : TightBindingChain)

/-- The volumetric quantum of the cube `Nx × Ny × Nz`: the product of the dimensional quanta of
its axes, each axis carrying its own `C_Nava` (`CNava_alongX`, `CNava_alongY`, `CNava_alongZ`). -/
noncomputable def volQuantum : ℝ := Tx.dimQuantum * Ty.dimQuantum * Tz.dimQuantum

variable {Tx Ty Tz}

/-- The volumetric quantum vanishes iff some axis has `2` or `3` sites. -/
theorem volQuantum_eq_zero_iff (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    volQuantum Tx Ty Tz = 0 ↔
      (Tx.N = 2 ∨ Tx.N = 3) ∨ (Ty.N = 2 ∨ Ty.N = 3) ∨ (Tz.N = 2 ∨ Tz.N = 3) := by
  rw [volQuantum, mul_eq_zero, mul_eq_zero, Tx.dimQuantum_eq_zero_iff hx hNx,
    Ty.dimQuantum_eq_zero_iff hy hNy, Tz.dimQuantum_eq_zero_iff hz hNz, or_assoc]

/-- From `4 × 4 × 4` on, the volumetric quantum is positive. -/
theorem volQuantum_pos (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) : 0 < volQuantum Tx Ty Tz :=
  mul_pos (mul_pos (Tx.dimQuantum_pos hx hNx) (Ty.dimQuantum_pos hy hNy))
    (Tz.dimQuantum_pos hz hNz)

/-- From `4 × 4 × 4` on, the volumetric quantum grows strictly along `x`. -/
theorem volQuantum_lt_volQuantum_x {Tx' : TightBindingChain} (hx : Tx.t ≠ 0) (hx' : Tx'.t ≠ 0)
    (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Tx.N < Tx'.N) : volQuantum Tx Ty Tz < volQuantum Tx' Ty Tz := by
  have := Ty.dimQuantum_pos hy hNy
  have := Tz.dimQuantum_pos hz hNz
  unfold volQuantum
  gcongr
  exact dimQuantum_lt_dimQuantum hx hx' hNx h

/-- From `4 × 4 × 4` on, the volumetric quantum grows strictly along `y`. -/
theorem volQuantum_lt_volQuantum_y {Ty' : TightBindingChain} (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hy' : Ty'.t ≠ 0) (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Ty.N < Ty'.N) : volQuantum Tx Ty Tz < volQuantum Tx Ty' Tz := by
  have := Tx.dimQuantum_pos hx hNx
  have := Tz.dimQuantum_pos hz hNz
  unfold volQuantum
  gcongr
  exact dimQuantum_lt_dimQuantum hy hy' hNy h

/-- From `4 × 4 × 4` on, the volumetric quantum grows strictly along `z`. -/
theorem volQuantum_lt_volQuantum_z {Tz' : TightBindingChain} (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hz : Tz.t ≠ 0) (hz' : Tz'.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Tz.N < Tz'.N) : volQuantum Tx Ty Tz < volQuantum Tx Ty Tz' := by
  have := Tx.dimQuantum_pos hx hNx
  have := Ty.dimQuantum_pos hy hNy
  unfold volQuantum
  gcongr
  exact dimQuantum_lt_dimQuantum hz hz' hNz h

/-- From `4 × 4 × 4` on, the volumetric quantum stays below `(√(π² / 3 - 2) - 1)³`. -/
theorem volQuantum_lt (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    volQuantum Tx Ty Tz < (√(Real.pi ^ 2 / 3 - 2) - 1) ^ 3 := by
  have := Tx.dimQuantum_pos hx hNx
  have := Ty.dimQuantum_pos hy hNy
  have := Tz.dimQuantum_pos hz hNz
  rw [volQuantum, pow_three, ← mul_assoc]
  gcongr
  · exact Tx.dimQuantum_lt hx hNx
  · exact Ty.dimQuantum_lt hy hNy
  · exact Tz.dimQuantum_lt hz hNz

end TightBindingChain
end CondensedMatter
