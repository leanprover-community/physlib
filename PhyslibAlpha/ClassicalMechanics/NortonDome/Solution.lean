/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import PhyslibAlpha.ClassicalMechanics.NortonDome.Basic
public import PhyslibAlpha.ClassicalMechanics.NortonDome.PosPartPow
/-!

# The motions of the Norton dome and the failure of uniqueness

## i. Overview

A particle at rest on the apex of the Norton dome satisfies `r̈ = √r` by staying there forever,
and also by staying until an arbitrary instant `T ≥ 0` and then sliding off along
`r(t) = (t - T)⁴ / 144`: that curve is `C²`, vanishes with its derivative at `T`, and its
second derivative `(t - T)² / 12` is `√r`. All these motions have the same initial position and
velocity, so the initial data do not determine the motion. This is Norton's observation.

For contrast, the pendulum's phase-space vector field is Lipschitz and Mathlib's
`ODE_solution_unique_univ` gives `SimplePendulum.equationOfMotion_unique`; the force of the
dome is not Lipschitz at the apex, `NortonDome.not_lipschitzOnWith_force`. Energy conservation
does not help either, since every motion in the family has zero energy (`energy_solution`).
Read backwards in time, in section E, a particle sliding up the dome may arrive at the apex at
rest in finite time and stay there.

## ii. Key results

- `NortonDome.delayedQuartic` is the real function `τ ↦ max (τ - T) 0 ⁴ / 144`, with its
  derivatives `hasDerivAt_delayedQuartic` and `hasDerivAt_deriv_delayedQuartic`, its `C²`
  regularity `contDiff_delayedQuartic`, and the identity `sqrt_delayedQuartic`.
- `NortonDome.solution T` is the motion leaving the apex at the instant `T`. It is a solution,
  `solution_isSolution`, starts from rest at the apex when `0 ≤ T`, `solution_zero` and
  `deriv_solution_zero`, and is injective in `T`, `solution_injective`.
- `NortonDome.rest_isSolution` is the motion staying at the apex.
- `NortonDome.exists_isSolution_ne` is the failure of uniqueness: two distinct solutions with
  the same initial position and velocity; `NortonDome.not_isSolution_unique` restates it as
  the negation of the uniqueness property of the pendulum. All these motions have zero energy,
  `NortonDome.energy_rest` and `NortonDome.energy_solution`.
- `NortonDome.IsSolution.comp_neg` is the time-reversal symmetry of the dome, and
  `NortonDome.arrival T` the time-reversed motion, off the apex before the instant `-T`,
  `arrival_apply_pos`, and at rest on it from then on, `arrival_of_le`.

## iii. Table of contents

- A. The delayed quartic
  - A.1. Definition and sign
  - A.2. Derivatives and regularity
- B. The motions leaving the apex
  - B.1. The definition and its values
  - B.2. Derivatives and regularity
  - B.3. The equation of motion
  - B.4. Distinct instants give distinct motions
- C. The motion staying at the apex
- D. The failure of uniqueness
- E. Time reversal and arrival at the apex

## iv. References

- Norton, J. D., *The dome: an unexpectedly simple failure of determinism*, Philosophy of
  Science 75 (2008), 786–798.
- `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Solution` (uniqueness for a Lipschitz
  force, for contrast).

-/

@[expose] public section

namespace ClassicalMechanics.NortonDome
open Real InnerProductSpace Time

variable (S : NortonDome)

/-!

## A. The delayed quartic

As a function of the real time `τ`, the motion leaving the apex at the instant `T` is
`max (τ - T) 0 ⁴ / 144`; its calculus is that of the positive-part powers of
`NortonDome.PosPartPow`.

-/

/-!

### A.1. Definition and sign

-/

/-- The delayed quartic `τ ↦ max (τ - T) 0 ⁴ / 144`: zero up to the instant `T`, and
  `(τ - T)⁴ / 144` afterwards. -/
noncomputable def delayedQuartic (T τ : ℝ) : ℝ := max (τ - T) 0 ^ 4 / 144

/-- The delayed quartic, written out. -/
lemma delayedQuartic_eq (T τ : ℝ) : delayedQuartic T τ = max (τ - T) 0 ^ 4 / 144 := rfl

/-- The delayed quartic is non-negative. -/
lemma delayedQuartic_nonneg (T τ : ℝ) : 0 ≤ delayedQuartic T τ := by
  rw [delayedQuartic_eq]
  positivity

/-- The delayed quartic vanishes up to the instant `T`. -/
lemma delayedQuartic_of_le (T : ℝ) {τ : ℝ} (h : τ ≤ T) : delayedQuartic T τ = 0 := by
  rw [delayedQuartic_eq, max_eq_right (sub_nonpos.mpr h)]
  simp

/-- The delayed quartic is positive after the instant `T`. -/
lemma delayedQuartic_pos (T : ℝ) {τ : ℝ} (h : T < τ) : 0 < delayedQuartic T τ := by
  rw [delayedQuartic_eq, max_eq_left (sub_nonneg.mpr h.le)]
  have := sub_pos.mpr h
  positivity

/-- The square root of the delayed quartic is `max (τ - T) 0 ² / 12`, which is its second
  derivative: this is the equation of motion `r̈ = √r` of the dome along it. -/
lemma sqrt_delayedQuartic (T τ : ℝ) : √(delayedQuartic T τ) = max (τ - T) 0 ^ 2 / 12 := by
  rw [delayedQuartic_eq, show max (τ - T) 0 ^ 4 / 144 = (max (τ - T) 0 ^ 2 / 12) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-!

### A.2. Derivatives and regularity

-/

/-- The derivative of the delayed quartic is `max (τ - T) 0 ³ / 36`. -/
lemma hasDerivAt_delayedQuartic (T τ : ℝ) :
    HasDerivAt (delayedQuartic T) (max (τ - T) 0 ^ 3 / 36) τ := by
  refine ((hasDerivAt_max_sub_pow T 2 τ).div_const 144).congr_deriv ?_
  push_cast
  ring

/-- The derivative of the delayed quartic, as a function. -/
lemma deriv_delayedQuartic (T : ℝ) :
    deriv (delayedQuartic T) = fun τ => max (τ - T) 0 ^ 3 / 36 :=
  funext fun τ => (hasDerivAt_delayedQuartic T τ).deriv

/-- The second derivative of the delayed quartic is `max (τ - T) 0 ² / 12`. -/
lemma hasDerivAt_deriv_delayedQuartic (T τ : ℝ) :
    HasDerivAt (deriv (delayedQuartic T)) (max (τ - T) 0 ^ 2 / 12) τ := by
  rw [deriv_delayedQuartic]
  refine ((hasDerivAt_max_sub_pow T 1 τ).div_const 36).congr_deriv ?_
  push_cast
  ring

/-- The delayed quartic is `C²`. It is in fact `C³` and not `C⁴`, which is not needed here. -/
@[fun_prop]
lemma contDiff_delayedQuartic (T : ℝ) : ContDiff ℝ 2 (delayedQuartic T) :=
  ((contDiff_max_sub_pow T 2).div_const 144).of_le (by exact_mod_cast Nat.le_succ 2)

/-!

## B. The motions leaving the apex

The motion leaving the apex at the instant `T` is the delayed quartic read on `Time`, times the
unit vector of the arc-length coordinate.

-/

/-!

### B.1. The definition and its values

-/

/-- The motion of the particle on the dome leaving the apex at the instant `T`: at rest at the
  apex up to `T`, and at arc length `(t - T)⁴ / 144` from the apex afterwards. -/
noncomputable def solution (T : ℝ) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  delayedQuartic T t.val • EuclideanSpace.single 0 1

/-- The arc length along the motion leaving the apex at the instant `T` is the delayed
  quartic. -/
lemma solution_apply (T : ℝ) (t : Time) : solution T t 0 = delayedQuartic T t.val := by
  simp [solution]

/-- The motion leaving the apex at the instant `T` is at the apex up to `T`. -/
lemma solution_of_le (T : ℝ) {t : Time} (h : t.val ≤ T) : solution T t = 0 := by
  simp [solution, delayedQuartic_of_le T h]

/-- The motion leaving the apex at the instant `T ≥ 0` starts at the apex. -/
lemma solution_zero {T : ℝ} (hT : 0 ≤ T) : solution T 0 = 0 :=
  solution_of_le T (by rw [Time.zero_val]; exact hT)

/-- The motion leaving the apex at the instant `T` is off the apex after `T`. -/
lemma solution_apply_pos (T : ℝ) {t : Time} (h : T < t.val) : 0 < solution T t 0 := by
  rw [solution_apply]
  exact delayedQuartic_pos T h

/-!

### B.2. Derivatives and regularity

-/

/-- The motion leaving the apex at the instant `T` is `C²`. -/
@[fun_prop]
lemma solution_contDiff (T : ℝ) : ContDiff ℝ 2 (solution T) := by
  unfold solution
  fun_prop

/-- The velocity along the motion leaving the apex at the instant `T` is
  `max (t - T) 0 ³ / 36`. -/
lemma deriv_solution (T : ℝ) :
    ∂ₜ (solution T) = fun t => (max (t.val - T) 0 ^ 3 / 36) • EuclideanSpace.single 0 1 := by
  funext t
  unfold solution
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt
    (fun τ : ℝ => delayedQuartic T τ • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) t _
    ((hasDerivAt_delayedQuartic T t.val).smul_const _)

/-- The acceleration along the motion leaving the apex at the instant `T` is
  `max (t - T) 0 ² / 12`. -/
lemma deriv_deriv_solution (T : ℝ) :
    ∂ₜ (∂ₜ (solution T)) =
      fun t => (max (t.val - T) 0 ^ 2 / 12) • EuclideanSpace.single 0 1 := by
  funext t
  rw [deriv_solution]
  have h := hasDerivAt_deriv_delayedQuartic T t.val
  rw [deriv_delayedQuartic] at h
  exact Time.deriv_comp_toRealCLE_of_hasDerivAt
    (fun τ : ℝ => (max (τ - T) 0 ^ 3 / 36) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) t _
    (h.smul_const _)

/-- The motion leaving the apex at the instant `T ≥ 0` starts from rest. -/
lemma deriv_solution_zero {T : ℝ} (hT : 0 ≤ T) : ∂ₜ (solution T) 0 = 0 := by
  rw [deriv_solution]
  simp [hT]

/-!

### B.3. The equation of motion

-/

/-- The motion leaving the apex at the instant `T` satisfies the equation of motion of the
  dome: its acceleration `max (t - T) 0 ² / 12` is the square root of its arc length. -/
lemma solution_equationOfMotion (T : ℝ) : S.EquationOfMotion (solution T) := by
  rw [equationOfMotion_iff_scalar]
  intro t
  rw [deriv_deriv_solution, solution_apply, sqrt_delayedQuartic]
  simp

/-- The motion leaving the apex at the instant `T` is a solution of the dome. -/
lemma solution_isSolution (T : ℝ) : S.IsSolution (solution T) :=
  ⟨(solution_contDiff T).differentiable (by simp),
    Time.deriv_differentiable_of_contDiff_two _ (solution_contDiff T),
    S.solution_equationOfMotion T⟩

/-!

### B.4. Distinct instants give distinct motions

-/

/-- Motions leaving the apex at distinct instants are distinct: at the later instant one is
  still at the apex and the other is not. -/
lemma solution_ne_of_lt {T T' : ℝ} (h : T < T') : solution T ≠ solution T' := by
  intro heq
  have h1 := solution_apply_pos T (t := (T' : Time)) (by rw [Time.realCast_val]; exact h)
  rw [heq, solution_apply, delayedQuartic_of_le T' (by rw [Time.realCast_val])] at h1
  exact lt_irrefl _ h1

/-- The family of motions leaving the apex is injective in the instant of departure. -/
lemma solution_injective : Function.Injective solution := by
  intro T T' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact solution_ne_of_lt hlt h
  · exact solution_ne_of_lt hlt h.symm

/-- No motion leaving the apex is the motion staying at it. -/
lemma solution_ne_zero (T : ℝ) : solution T ≠ 0 := by
  intro h
  have := solution_apply_pos T (t := ((T + 1 : ℝ) : Time)) (by rw [Time.realCast_val]; linarith)
  rw [h] at this
  simp at this

/-!

## C. The motion staying at the apex

The force vanishes at the apex, so the constant curve there satisfies the equation of motion.

-/

/-- The motion staying at rest at the apex is a solution of the dome. -/
lemma rest_isSolution : S.IsSolution 0 := by
  have h : ∂ₜ (0 : Time → EuclideanSpace ℝ (Fin 1)) = 0 := funext fun _ => Time.deriv_const 0
  refine ⟨differentiable_const 0, by rw [h]; exact differentiable_const 0, fun t => ?_⟩
  simp [h, force_zero]

/-- The motion staying at the apex has zero energy. -/
lemma energy_rest (t : Time) : S.energy 0 t = 0 := by
  have h : ∂ₜ (0 : Time → EuclideanSpace ℝ (Fin 1)) = 0 := funext fun _ => Time.deriv_const 0
  simp [energy_eq, kineticEnergy_eq, potentialEnergy_eq, h]

/-!

## D. The failure of uniqueness

Rest at the apex and departure at any instant `T ≥ 0` are distinct solutions with the same
initial data. So the uniqueness property `SimplePendulum.IsSolution.eq_of_initial` of the
pendulum fails for the dome, whose force violates the Picard–Lindelöf hypothesis
(`not_lipschitzOnWith_force`).

-/

/-- Failure of uniqueness for the Norton dome: there are two distinct solutions of the
  dome with the same initial position and the same initial velocity. The witnesses are the
  motion staying at the apex and the motion leaving it at the instant `0`. -/
lemma exists_isSolution_ne :
    ∃ x y : Time → EuclideanSpace ℝ (Fin 1), S.IsSolution x ∧ S.IsSolution y ∧
      x 0 = y 0 ∧ ∂ₜ x 0 = ∂ₜ y 0 ∧ x ≠ y :=
  ⟨0, solution 0, S.rest_isSolution, S.solution_isSolution 0, by simp [solution_zero le_rfl],
    by rw [deriv_solution_zero le_rfl]; exact Time.deriv_const 0,
    (solution_ne_zero 0).symm⟩

/-- The solutions of the Norton dome are not determined by their initial position and
  velocity: the uniqueness property that the simple pendulum has,
  `SimplePendulum.IsSolution.eq_of_initial`, fails for the dome. -/
lemma not_isSolution_unique :
    ¬ ∀ x y : Time → EuclideanSpace ℝ (Fin 1), S.IsSolution x → S.IsSolution y →
      x 0 = y 0 → ∂ₜ x 0 = ∂ₜ y 0 → x = y := by
  intro h
  obtain ⟨x, y, hx, hy, h0, hv, hne⟩ := S.exists_isSolution_ne
  exact hne (h x y hx hy h0 hv)

/-- For every instant `T ≥ 0` there is a solution of the dome starting from rest at the apex
  which is at the apex up to `T` and off it afterwards: the motions from rest at the apex form
  a one-parameter family. -/
lemma exists_isSolution_of_nonneg {T : ℝ} (hT : 0 ≤ T) :
    ∃ r : Time → EuclideanSpace ℝ (Fin 1), S.IsSolution r ∧ r 0 = 0 ∧ ∂ₜ r 0 = 0 ∧
      (∀ t : Time, t.val ≤ T → r t = 0) ∧ (∀ t : Time, T < t.val → 0 < r t 0) :=
  ⟨solution T, S.solution_isSolution T, solution_zero hT, deriv_solution_zero hT,
    fun _ ht => solution_of_le T ht, fun _ ht => solution_apply_pos T ht⟩

/-- Every motion leaving the apex has zero energy: before the instant `T` it is at rest at the
  apex, and the energy is conserved. Energy conservation therefore does not single out the
  motion staying at the apex. -/
lemma energy_solution (T : ℝ) (t : Time) : S.energy (solution T) t = 0 := by
  have hs : ((T - 1 : ℝ) : Time).val ≤ T := by rw [Time.realCast_val]; linarith
  rw [(S.solution_isSolution T).energy_eq t,
    ← (S.solution_isSolution T).energy_eq ((T - 1 : ℝ) : Time)]
  simp [energy_eq, kineticEnergy_eq, potentialEnergy_eq, deriv_solution, solution_of_le T hs]

/-!

## E. Time reversal and arrival at the apex

The equation of motion has no velocity term, so time reversal maps solutions to solutions.
Reversing the departure at the instant `T` gives a motion sliding up the dome, arriving at the
apex at the instant `-T` with zero velocity, and staying there. For a locally Lipschitz force
this is impossible; for the dome it is the non-uniqueness read backwards.

-/

/-- The second derivative is unchanged by the reversal of time, for a curve whose position and
  velocity are differentiable. This is `Time.deriv_deriv_comp_neg` with its `C²` hypothesis
  weakened to the regularity of a solution. -/
lemma deriv_deriv_comp_neg_of_differentiable {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (f : Time → M) (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (∂ₜ f))
    (t : Time) : ∂ₜ (∂ₜ (fun s => f (-s))) t = ∂ₜ (∂ₜ f) (-t) := by
  rw [← neg_neg (∂ₜ (∂ₜ f) (-t)), ← Time.deriv_comp_neg _ _ (hf' _), ← Time.deriv_neg]
  congr
  ext
  exact Time.deriv_comp_neg f _ (hf _)

/-- The time reversal of a twice differentiable curve satisfying the equation of motion of the
  dome satisfies it too: the equation has no velocity term. -/
lemma equationOfMotion_comp_neg {r : Time → EuclideanSpace ℝ (Fin 1)} (hr : Differentiable ℝ r)
    (hr' : Differentiable ℝ (∂ₜ r)) (h : S.EquationOfMotion r) :
    S.EquationOfMotion (fun t => r (-t)) := by
  intro t
  rw [deriv_deriv_comp_neg_of_differentiable r hr hr' t]
  exact h (-t)

/-- The time reversal of a solution of the dome is a solution. -/
lemma IsSolution.comp_neg {S : NortonDome} {r : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution r) : S.IsSolution (fun t => r (-t)) := by
  have hneg : Differentiable ℝ (fun t : Time => -t) := by fun_prop
  refine ⟨h.differentiable.comp hneg, ?_,
    S.equationOfMotion_comp_neg h.differentiable h.deriv_differentiable h.equationOfMotion⟩
  have hv : ∂ₜ (fun t => r (-t)) = fun t => -∂ₜ r (-t) :=
    funext fun t => Time.deriv_comp_neg r t (h.differentiable _)
  rw [hv]
  exact (h.deriv_differentiable.comp hneg).neg

/-- The motion of the particle on the dome arriving at the apex at the instant `-T`: the time
  reversal of the motion leaving the apex at the instant `T`. -/
noncomputable def arrival (T : ℝ) : Time → EuclideanSpace ℝ (Fin 1) := fun t => solution T (-t)

/-- The motion arriving at the apex at the instant `-T` is a solution of the dome. -/
lemma arrival_isSolution (T : ℝ) : S.IsSolution (arrival T) :=
  (S.solution_isSolution T).comp_neg

/-- The motion arriving at the apex at the instant `-T` is off the apex before that
  instant. -/
lemma arrival_apply_pos (T : ℝ) {t : Time} (h : t.val < -T) : 0 < arrival T t 0 :=
  solution_apply_pos T (by rw [Time.neg_val]; linarith)

/-- The motion arriving at the apex at the instant `-T` is at the apex from that instant on:
  it reaches the apex in finite time and stays there. -/
lemma arrival_of_le (T : ℝ) {t : Time} (h : -T ≤ t.val) : arrival T t = 0 :=
  solution_of_le T (by rw [Time.neg_val]; linarith)

/-- The motion arriving at the apex at the instant `-T` arrives with zero velocity. -/
lemma deriv_arrival_of_le (T : ℝ) {t : Time} (h : -T ≤ t.val) : ∂ₜ (arrival T) t = 0 := by
  unfold arrival
  rw [Time.deriv_comp_neg _ _ ((solution_contDiff T).differentiable (by simp) _),
    deriv_solution]
  have h' : max ((-t).val - T) 0 = 0 := max_eq_right (by rw [Time.neg_val]; linarith)
  simp only [h']
  simp

end ClassicalMechanics.NortonDome

end
