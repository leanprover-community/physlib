/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Special.ProperTime
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausallyFollows
/-!
# Twin Paradox

The twin paradox corresponds to the following scenario:

Two twins start at the same point `startPoint` in spacetime.
Twin A travels at constant speed to the spacetime point `endPoint`,
whilst twin B makes a detour through the spacetime `twinBMid` and then to `endPoint`.

In this file, we assume that both twins travel at constant speed,
and that the acceleration of Twin B is instantaneous.

The conclusion of this scenario is that Twin A will be older than Twin B when they meet at
`endPoint`. This is something we show here with an explicit example.

The origin of the twin paradox dates back to Paul Langevin in 1911.

-/

@[expose] public section

noncomputable section

namespace SpecialRelativity

open Matrix
open Real
open Lorentz
open Vector

/-- The twin paradox assuming instantaneous acceleration. -/
structure InstantaneousTwinParadox where
  /-- The starting point of both twins. -/
  startPoint : SpaceTime 3
  /-- The end point of both twins. -/
  endPoint : SpaceTime 3
  /-- The point twin B travels to between the start point and the end point. -/
  twinBMid : SpaceTime 3
  endPoint_causallyFollows_startPoint : causallyFollows startPoint endPoint
  twinBMid_causallyFollows_startPoint : causallyFollows startPoint twinBMid
  endPoint_causallyFollows_twinBMid : causallyFollows twinBMid endPoint

namespace InstantaneousTwinParadox
variable (T: InstantaneousTwinParadox)
open SpaceTime

/-- The proper time experienced by twin A travelling at constant speed
  from `T.startPoint` to `T.endPoint`. -/
def properTimeTwinA : ℝ := SpaceTime.properTime T.startPoint T.endPoint

/-- The proper time experienced by twin B travelling at constant speed
  from `T.startPoint` to `T.twinBMid`, and then from `T.twinBMid`
  to `T.endPoint`. -/
def properTimeTwinB : ℝ := SpaceTime.properTime T.startPoint T.twinBMid +
  SpaceTime.properTime T.twinBMid T.endPoint

/-- The proper time of twin A minus the proper time of twin B. -/
def ageGap : ℝ := T.properTimeTwinA - T.properTimeTwinB

/-- The age gap in terms of the two legs of Twin B, `u = twinBMid - startPoint` and
  `v = endPoint - twinBMid`: `ageGap = √⟪u + v, u + v⟫ₘ - (√⟪u, u⟫ₘ + √⟪v, v⟫ₘ)`. -/
lemma ageGap_eq :
    T.ageGap = √⟪(T.twinBMid - T.startPoint) + (T.endPoint - T.twinBMid),
      (T.twinBMid - T.startPoint) + (T.endPoint - T.twinBMid)⟫ₘ
      - (√⟪T.twinBMid - T.startPoint, T.twinBMid - T.startPoint⟫ₘ
        + √⟪T.endPoint - T.twinBMid, T.endPoint - T.twinBMid⟫ₘ) := by
  have hsum : T.endPoint - T.startPoint
      = (T.twinBMid - T.startPoint) + (T.endPoint - T.twinBMid) := by abel
  unfold ageGap properTimeTwinA properTimeTwinB properTime
  rw [hsum]

/-- The age gap vanishes if and only if the turning point of Twin B lies on the straight
  worldline of Twin A between the start and end points: Twin B does not turn. This is the
  equality case of the reverse triangle inequality (`sqrt_add_eq_iff_of_causallyFollows`,
  `minkowskiProduct_eq_iff_of_causallyFollows`).
  -/
lemma ageGap_eq_zero_iff : T.ageGap = 0 ↔
    ∃ μ ∈ Set.Icc (0 : ℝ) 1, T.twinBMid = T.startPoint + μ • (T.endPoint - T.startPoint) := by
  have hu := causallyFollows_zero_sub T.twinBMid_causallyFollows_startPoint
  have hv := causallyFollows_zero_sub T.endPoint_causallyFollows_twinBMid
  have hsum : T.endPoint - T.startPoint
      = (T.twinBMid - T.startPoint) + (T.endPoint - T.twinBMid) := by abel
  rw [ageGap_eq, sub_eq_zero, sqrt_add_eq_iff_of_causallyFollows hu hv,
    minkowskiProduct_eq_iff_of_causallyFollows hu hv]
  constructor
  · rintro ⟨l, hl, h | h⟩
    · refine ⟨1 / (1 + l), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]
        linarith
      · have hw : T.endPoint - T.startPoint = (1 + l) • (T.twinBMid - T.startPoint) := by
          rw [hsum, h, _root_.add_smul, _root_.one_smul]
        rw [hw, _root_.smul_smul, show 1 / (1 + l) * (1 + l) = 1 by field_simp, _root_.one_smul]
        abel
    · refine ⟨l / (1 + l), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]
        linarith
      · have hw : T.endPoint - T.startPoint = (1 + l) • (T.endPoint - T.twinBMid) := by
          rw [hsum, h, _root_.add_smul, _root_.one_smul]
          abel
        rw [hw, _root_.smul_smul, show l / (1 + l) * (1 + l) = l by field_simp, ← h]
        abel
  · rintro ⟨μ, ⟨h0, h1⟩, hmid⟩
    have hu' : T.twinBMid - T.startPoint = μ • (T.endPoint - T.startPoint) := by
      rw [hmid]
      abel
    have hv' : T.endPoint - T.twinBMid = (1 - μ) • (T.endPoint - T.startPoint) := by
      rw [hmid, _root_.sub_smul, _root_.one_smul]
      abel
    by_cases hμ : μ = 0
    · refine ⟨0, le_rfl, Or.inr ?_⟩
      rw [hu', hμ, _root_.zero_smul, _root_.zero_smul]
    · refine ⟨(1 - μ) / μ, div_nonneg (by linarith) (lt_of_le_of_ne h0 (Ne.symm hμ)).le, Or.inl ?_⟩
      rw [hu', hv', _root_.smul_smul, show (1 - μ) / μ * μ = 1 - μ by field_simp]

/-- In the twin paradox with instantaneous acceleration, Twin A is always at least as old as
  Twin B: the age gap is nonnegative. This is the reverse triangle inequality of Minkowski space
  (`sqrt_add_sqrt_le_sqrt_add_of_causallyFollows`) applied to the two legs of Twin B. -/
lemma ageGap_nonneg : 0 ≤ T.ageGap := by
  have hu := causallyFollows_zero_sub T.twinBMid_causallyFollows_startPoint
  have hv := causallyFollows_zero_sub T.endPoint_causallyFollows_twinBMid
  have h := sqrt_add_sqrt_le_sqrt_add_of_causallyFollows hu hv
  rw [ageGap_eq]
  linarith

/-!

## Example 1

-/

/-- The twin paradox in which:
- Twin A starts at `0` and travels at constant
  speed to `[15, 0, 0, 0]`.
- Twin B starts at `0` and travels at constant speed to
  `[7.5, 6, 0, 0]` and then at (different) constant speed to `[15, 0, 0, 0]`. -/
def example1 : InstantaneousTwinParadox where
  startPoint := 0
  endPoint := (fun
    | Sum.inl 0 => 15
    | Sum.inr i => 0)
  twinBMid := (fun
    | Sum.inl 0 => 7.5
    | Sum.inr 0 => 6
    | Sum.inr i => 0)
  endPoint_causallyFollows_startPoint := by
    simp [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_ofPred_eq, Nat.ofNat_pos,
      and_true]
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp
  twinBMid_causallyFollows_startPoint := by
    simp only [causallyFollows]
    left
    simp only [interiorFutureLightCone, sub_zero, Fin.isValue, Set.mem_ofPred_eq]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num
  endPoint_causallyFollows_twinBMid := by
    simp [causallyFollows]
    left
    simp [interiorFutureLightCone]
    norm_num
    refine (timeLike_iff_norm_sq_pos _).mpr ?_
    rw [minkowskiProduct_toCoord]
    simp [Fin.sum_univ_three]
    norm_num

@[simp]
lemma example1_properTimeTwinA : example1.properTimeTwinA = 15 := by
  simp [properTimeTwinA, example1, properTime, minkowskiProduct_toCoord]

@[simp]
lemma example1_properTimeTwinB : example1.properTimeTwinB = 9 := by
  simp [properTimeTwinB, properTime, example1, minkowskiProduct_toCoord, Fin.sum_univ_three]
  norm_num [show √81 = 9 from sqrt_eq_cases.mpr (by norm_num),
    show √4 = 2 from sqrt_eq_cases.mpr (by norm_num)]

lemma example1_ageGap : example1.ageGap = 6 := by
  norm_num [ageGap]

/-- The example above has a nonzero age gap. -/
lemma example1_ageGap_ne_zero : example1.ageGap ≠ 0 := by
  rw [example1_ageGap]
  norm_num

end InstantaneousTwinParadox

TODO "Do the twin paradox with a non-instantaneous acceleration. This should be done
  in a different module."

end SpecialRelativity

end
