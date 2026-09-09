/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import Mathlib.Analysis.Convex.StdSimplex

/-!

# Finite-outcome measurements

A finite-outcome measurement is a finite family of effects whose total is the order unit. The
outcome *type* `ι` need not itself be finite — only finitely many outcomes need actually occur,
recorded by an explicit `Finset ι` of outcomes — so a measurement can, for instance, be labeled by
all of `ℕ` or `ℝ` while only ever registering finitely many of those labels. Evaluating a
measurement in a state gives a probability distribution on its (finite) outcome set, directly in
`ℝ`: a state is already a genuine linear functional, so its values on the (bounded) effects of a
measurement are already finite nonnegative reals summing to `1`, with no detour through `Weight`'s
`[0, ∞]`-valued arithmetic needed.

This sits outside `OrderUnit/`: it is a derived notion built *from* `Effect` and `State`, not part
of the order-unit algebra itself, the same way `Traciality.lean` sits outside `OrderUnit/` despite
being built from `Weight`. `FiniteOutcome.lean` gives the equivalent, order-unit-level presentation
of the same data: a measurement is exactly a channel out of the classical `ι`-outcome system.

## Main definitions

- `Measurement E ι`
- `Measurement.outcomeDistribution`

-/

@[expose] public section

open scoped BigOperators

variable {E ι : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

/-- A measurement with outcomes in `ι`: an effect for each outcome in the finite set `outcomes`,
totaling `1`. `ι` itself need not be finite. -/
structure Measurement (E : Type*) [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
    [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E] (ι : Type*) where
  /-- The finitely many outcomes this measurement can actually produce. -/
  outcomes : Finset ι
  /-- The effect associated to each possible outcome. -/
  effects : ι → Effect E
  /-- The effects exhaust the certain event. -/
  sum_eq_one : ∑ i ∈ outcomes, (effects i : E) = 1

namespace Measurement

/-- Measurements are equivalently a finite set of outcomes together with an effect for each,
summing to `1` over that set. -/
def outcomesEffectsEquiv :
    Measurement E ι ≃ {p : Finset ι × (ι → Effect E) // ∑ i ∈ p.1, (p.2 i : E) = 1} where
  toFun m := ⟨(m.outcomes, m.effects), m.sum_eq_one⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The probability distribution a measurement induces in a state, on its (finite) outcome set:
nonnegative since a state is positive, summing to `1` since the effects exhaust the certain event
and a state is linear and unital. -/
noncomputable def outcomeDistribution (m : Measurement E ι) (s : 𝓢[ℝ, E]) :
    stdSimplex ℝ m.outcomes :=
  ⟨fun i => s (m.effects i : E), fun i => s.map_nonneg (m.effects i).2.1, by
    classical
    rw [Finset.sum_coe_sort m.outcomes (fun i => s (m.effects i : E)), ← _root_.map_sum,
      m.sum_eq_one, _root_.map_one]⟩

@[simp]
lemma outcomeDistribution_apply (m : Measurement E ι) (s : 𝓢[ℝ, E]) (i : m.outcomes) :
    m.outcomeDistribution s i = s (m.effects i : E) :=
  rfl

/-- A measurement as its map from states to the probability simplex on its outcomes. -/
noncomputable abbrev outcomeMap (m : Measurement E ι) : 𝓢[ℝ, E] → stdSimplex ℝ m.outcomes :=
  m.outcomeDistribution

end Measurement
