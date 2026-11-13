/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Geometry

/-!
# Kepler time for the Hohmann ellipse

The eccentric anomaly is obtained by inverting Kepler time.

## i. Overview

The derivative of the clock is strictly positive for eccentricity below one. Monotonicity and
surjectivity give an inverse on all real times, whose derivative follows from the inverse rule.

## ii. Key results

- `hasDerivAt_anomaly` gives the main result of this module.

## iii. Table of contents

- A. The clock and its inverse

## iv. References

- [ref: hohmann_jpl_orbital_mechanics] describes the Hohmann ellipse and its apses.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannTransfer

/-!
## A. The clock and its inverse
-/

/-- The elapsed Kepler time at a given eccentric anomaly. -/
def clock (p : Parameters) (u : ℝ) : ℝ := (u - p.e * Real.sin u) / p.n

lemma hasDerivAt_clock (p : Parameters) (u : ℝ) :
    HasDerivAt (clock p) (D p u / p.n) u := by
  exact ((hasDerivAt_id u).sub ((Real.hasDerivAt_sin u).const_mul p.e)).div_const p.n
lemma clock_continuous (p : Parameters) : Continuous (clock p) := by
  exact continuous_iff_continuousAt.2 (fun u => (hasDerivAt_clock p u).continuousAt)
lemma clock_strictMono (p : Parameters) : StrictMono (clock p) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_clock p)
  intro u
  exact div_pos (D_pos p u) p.n_pos
lemma clock_bounds (p : Parameters) (u : ℝ) :
    (u-p.e)/p.n ≤ clock p u ∧ clock p u ≤ (u+p.e)/p.n := by
  constructor
  · apply (div_le_div_iff_of_pos_right p.n_pos).2
    nlinarith [p.e_pos, Real.sin_le_one u]
  · apply (div_le_div_iff_of_pos_right p.n_pos).2
    nlinarith [p.e_pos, Real.neg_one_le_sin u]
lemma clock_surjective (p : Parameters) : Function.Surjective (clock p) := by
  intro t
  apply mem_range_of_exists_le_of_exists_ge (clock_continuous p)
  · refine ⟨p.n*t-p.e, ?_⟩
    calc
      clock p (p.n*t-p.e) ≤ (p.n*t-p.e+p.e)/p.n := (clock_bounds p _).2
      _ = t := by field_simp [p.n_ne]; ring
  · refine ⟨p.n*t+p.e, ?_⟩
    calc
      t = (p.n*t+p.e-p.e)/p.n := by field_simp [p.n_ne]; ring
      _ ≤ clock p (p.n*t+p.e) := (clock_bounds p _).1

/-- The inverse is the inverse of a proved order isomorphism. -/
def clockIso (p : Parameters) : ℝ ≃o ℝ where
  toEquiv := Equiv.ofBijective (clock p)
    ⟨(clock_strictMono p).injective, clock_surjective p⟩
  map_rel_iff' := by
    intro x y
    exact (clock_strictMono p).le_iff_le

/-- The eccentric anomaly at the given physical time. -/
def anomaly (p : Parameters) (t : ℝ) : ℝ := (clockIso p).symm t

lemma clock_anomaly (p : Parameters) (t : ℝ) : clock p (anomaly p t) = t := by
  exact (clockIso p).apply_symm_apply t
lemma anomaly_clock (p : Parameters) (u : ℝ) : anomaly p (clock p u) = u := by
  exact (clockIso p).symm_apply_apply u
lemma anomaly_continuous (p : Parameters) : Continuous (anomaly p) :=
  (clockIso p).symm.continuous
lemma anomaly_strictMono (p : Parameters) : StrictMono (anomaly p) :=
  (clockIso p).symm.strictMono
lemma hasDerivAt_anomaly (p : Parameters) (t : ℝ) :
    HasDerivAt (anomaly p) (p.n / D p (anomaly p t)) t := by
  have h := HasDerivAt.of_local_left_inverse
    (anomaly_continuous p).continuousAt
    (hasDerivAt_clock p (anomaly p t))
    (ne_of_gt (div_pos (D_pos p _) p.n_pos))
    (Filter.Eventually.of_forall (clock_anomaly p))
  simpa only [inv_div] using h
@[simp] lemma clock_zero (p : Parameters) : clock p 0 = 0 := by simp [clock]
@[simp] lemma clock_pi (p : Parameters) : clock p Real.pi = p.transferTime := by
  simp [clock, Parameters.transferTime]
@[simp] lemma anomaly_zero (p : Parameters) : anomaly p 0 = 0 := by
  simpa using anomaly_clock p 0
@[simp] lemma anomaly_transferTime (p : Parameters) :
    anomaly p p.transferTime = Real.pi := by
  simpa using anomaly_clock p Real.pi
lemma kepler_equation (p : Parameters) (t : ℝ) :
    anomaly p t - p.e * Real.sin (anomaly p t) = p.n*t := by
  have h := clock_anomaly p t
  unfold clock at h
  exact ((div_eq_iff p.n_ne).mp h).trans (mul_comm t p.n)
lemma anomaly_bounds (p : Parameters) {t : ℝ} (ht : t ∈ Set.Icc 0 p.transferTime) :
    anomaly p t ∈ Set.Icc 0 Real.pi := by
  constructor
  · simpa using (anomaly_strictMono p).monotone ht.1
  · simpa using (anomaly_strictMono p).monotone ht.2
lemma clock_add_two_pi (p : Parameters) (u : ℝ) :
    clock p (u+2*Real.pi) = clock p u + 2*p.transferTime := by
  simp only [clock, Real.sin_add_two_pi, Parameters.transferTime]
  ring
lemma anomaly_add_period (p : Parameters) (t : ℝ) :
    anomaly p (t+2*p.transferTime) = anomaly p t + 2*Real.pi := by
  apply (clock_strictMono p).injective
  rw [clock_anomaly, clock_add_two_pi, clock_anomaly]

end ClassicalMechanics.HohmannTransfer
