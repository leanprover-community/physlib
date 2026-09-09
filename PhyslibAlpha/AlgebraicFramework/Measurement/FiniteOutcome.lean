/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Measurement.Basic
public import PhyslibAlpha.AlgebraicFramework.Measurement.ClassicalSystem
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!

# Finite-outcome measurements, as channels

A finite-outcome measurement is already presented in `Measurement/Basic.lean` as a finite family
of effects summing to `1`. This file gives the *other* presentation, promised as future work in
`OrderUnit/Channel/Basic.lean`: a finite-outcome measurement with outcome type `ι` (`ι` itself
finite, every label actually occurring) is the same thing as a channel out of the classical
`ι`-outcome system `ι → ℝ` (`ClassicalSystem.lean`) — a positive unital linear map
`(ι → ℝ) →ₚ₁[ℝ] E` — and `channelEquiv` is the equivalence witnessing this.

The correspondence is the standard basis expansion for `ι → ℝ`: the point mass `Pi.single i 1` at
outcome `i` plays the role of the classical indicator function `𝟙_{i}`, `toChannel` sends a family
of effects to the (unique, by linearity) channel matching it on every point mass, and
`outcomeEffect` reads the family back off a channel by evaluating it at each point mass.

## Main definitions

- `Measurement.toChannel`, `Measurement.outcomeEffect`
- `Measurement.channelEquiv` : channels out of the classical `ι`-outcome system correspond to
  finite families of effects on `ι` summing to `1`.
- `Measurement.ofChannel` : the induced `Measurement E ι`, with every outcome occurring.

-/

@[expose] public section

variable {E ι : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E] [Fintype ι] [DecidableEq ι]

namespace Measurement

/-- The channel matching a given family of effects on every point mass: the (unique, by
linearity) positive unital extension of `i ↦ e i` from the point masses to all of `ι → ℝ`. -/
noncomputable def toChannel (e : ι → Effect E) (he : ∑ i, (e i : E) = 1) :
    (ι → ℝ) →ₚ₁[ℝ] E :=
  UnitalPositiveLinearMap.ofLinearMap (Fintype.linearCombination ℝ (fun i => (e i : E)))
    (fun f hf => Finset.sum_nonneg fun i _ => smul_nonneg (hf i) (e i).2.1)
    (by
      show ∑ i, (1 : ι → ℝ) i • (e i : E) = 1
      simpa using he)

omit [IsOrderUnit E] [DecidableEq ι] in
@[simp]
lemma toChannel_apply (e : ι → Effect E) (he : ∑ i, (e i : E) = 1) (f : ι → ℝ) :
    toChannel e he f = ∑ i, f i • (e i : E) :=
  Fintype.linearCombination_apply ℝ (fun i => (e i : E)) f

omit [IsOrderUnit E] in
/-- The channel matching a family of effects agrees with that family on each point mass. -/
lemma toChannel_single (e : ι → Effect E) (he : ∑ i, (e i : E) = 1) (i : ι) :
    toChannel e he (Pi.single i (1 : ℝ)) = (e i : E) := by
  rw [toChannel_apply,
    Finset.sum_eq_single i
      (fun j _ hji => by rw [Pi.single_apply, if_neg hji, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h)]
  simp

/-- The effect a channel out of the classical `ι`-outcome system assigns to outcome `i`: its value
at the point mass `Pi.single i 1`. `0 ≤` it since the point mass is a possible (classical) outcome,
and `≤ 1` since the point mass is bounded by the certain event and the channel is monotone. -/
def outcomeEffect (M : (ι → ℝ) →ₚ₁[ℝ] E) (i : ι) : Effect E :=
  ⟨M (Pi.single i (1 : ℝ)), M.map_nonneg (Pi.single_nonneg.mpr zero_le_one),
    (M.monotone' fun j => by rw [Pi.single_apply]; split_ifs <;> norm_num).trans_eq (map_one M)⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [Fintype ι] in
@[simp]
lemma coe_outcomeEffect (M : (ι → ℝ) →ₚ₁[ℝ] E) (i : ι) :
    (outcomeEffect M i : E) = M (Pi.single i (1 : ℝ)) :=
  rfl

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- The effects a channel assigns to the outcomes of the classical system it comes from sum to the
certain event: the point masses sum to the order unit, and the channel is linear and unital. -/
lemma outcomeEffect_sum (M : (ι → ℝ) →ₚ₁[ℝ] E) : ∑ i, (outcomeEffect M i : E) = 1 := by
  simp only [coe_outcomeEffect]
  calc ∑ i, M (Pi.single i (1 : ℝ)) = ∑ i, (1 : ι → ℝ) i • M (Pi.single i (1 : ℝ)) := by
        simp
    _ = M (∑ i, (1 : ι → ℝ) i • Pi.single i (1 : ℝ)) := by
        rw [_root_.map_sum]
        simp
    _ = M 1 := by rw [← pi_eq_sum_univ']
    _ = 1 := map_one M

/-- Channels out of the classical `ι`-outcome system correspond exactly to finite families of
effects on `ι`, all of whose labels occur, summing to `1`: `toChannel` and `outcomeEffect` are
mutually inverse, by the standard basis expansion of `ι → ℝ` along the point masses. -/
noncomputable def channelEquiv :
    ((ι → ℝ) →ₚ₁[ℝ] E) ≃ {e : ι → Effect E // ∑ i, (e i : E) = 1} where
  toFun M := ⟨outcomeEffect M, outcomeEffect_sum M⟩
  invFun p := toChannel p.1 p.2
  left_inv M := by
    apply UnitalPositiveLinearMap.toLinearMap_injective
    apply LinearMap.pi_ext
    intro i x
    show toChannel (outcomeEffect M) (outcomeEffect_sum M) (Pi.single i x) = M (Pi.single i x)
    have hx : Pi.single i x = x • Pi.single i (1 : ℝ) := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> ring
    rw [hx, map_smul, toChannel_apply]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [Pi.single_apply, if_neg hji, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [coe_outcomeEffect]
  right_inv p := by
    refine Subtype.ext (funext fun i => Subtype.ext ?_)
    simp

/-- Reading a channel's outcome effects off as a `Measurement E ι`, with every label of `ι`
actually occurring as an outcome. -/
noncomputable def ofChannel (M : (ι → ℝ) →ₚ₁[ℝ] E) : Measurement E ι where
  outcomes := Finset.univ
  effects := outcomeEffect M
  sum_eq_one := outcomeEffect_sum M

/-- The Born rule closes the loop between the two presentations: the outcome probability a state
assigns to `i`, computed from the channel `M` via `ofChannel`, is just that state pulled back
through `M` and evaluated at the point mass for `i` — the classical state `ω ∘ M` on the point
mass, exactly as if `i` had been measured directly on the classical system. -/
lemma ofChannel_outcomeDistribution_apply (M : (ι → ℝ) →ₚ₁[ℝ] E) (ω : 𝓢[ℝ, E])
    (i : (ofChannel M).outcomes) :
    (ofChannel M).outcomeDistribution ω i = ω (M (Pi.single (i : ι) (1 : ℝ))) := by
  rw [Measurement.outcomeDistribution_apply]
  rfl

end Measurement
