/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Normal
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Integral
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic

/-!

# Measurable-outcome measurements, pushed forward along a normal channel

An `EffectValuedMeasure Ω C` is already exactly a measurable-outcome measurement with classical
output `C`: the general definition promised in `OrderUnit/Channel/Basic.lean` — a channel out of
bounded measurable functions `B_b(Ω, ℝ)` — restricts on indicator functions to precisely this data,
`countably_additive'` being the trace of the channel's order-continuity on indicators alone. This
file gives the other half: pushing such a measure forward along a further, genuinely normal
channel `C →ₚ₁[ℝ] E` keeps it an effect-valued measure — countable additivity survives because the
channel is linear (so it commutes with finite partial sums) and normal (so it commutes with their
supremum).

## Main definitions

- `EffectValuedMeasure.map`
- `EffectValuedMeasure.scalarize`

-/

@[expose] public section

variable {Ω C E : Type*} [MeasurableSpace Ω]
  [AddCommGroup C] [PartialOrder C] [IsOrderedAddMonoid C] [Module ℝ C] [PosSMulMono ℝ C] [One C]
  [IsOrderUnit C]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E] [One E]
  [IsOrderUnit E]

namespace EffectValuedMeasure

omit [Module ℝ C] [PosSMulMono ℝ C] [One C] [IsOrderUnit C] in
/-- Nonnegative partial sums are monotone in how many terms are included: adding more
nonnegative terms never decreases the sum. -/
private lemma monotone_partialSums {f : ℕ → C} (hf : ∀ n, 0 ≤ f n) :
    Monotone (fun N => ∑ n ∈ Finset.range N, f n) := fun _ _ hNM =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM) fun i _ _ => hf i

/-- Pushing an effect-valued measure forward along a normal channel: composing each assigned
effect with the channel. -/
noncomputable def map (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) (hφ : φ.IsNormal) :
    EffectValuedMeasure Ω E where
  toFun s hs := ⟨φ (μ s hs : C), φ.map_nonneg (μ s hs).2.1,
    (φ.monotone' (μ s hs).2.2).trans_eq (map_one φ)⟩
  map_empty' := by
    refine Subtype.ext ?_
    show φ (μ ∅ MeasurableSet.empty : C) = 0
    rw [μ.map_empty]; exact map_zero φ
  map_univ' := by
    refine Subtype.ext ?_
    show φ (μ Set.univ MeasurableSet.univ : C) = 1
    rw [μ.map_univ]; exact map_one φ
  countably_additive' s hsm hs' := by
    set D : Set C := Set.range fun N => ∑ n ∈ Finset.range N, (μ (s n) (hsm n) : C) with hD
    have hmono : Monotone (fun N => ∑ n ∈ Finset.range N, (μ (s n) (hsm n) : C)) :=
      monotone_partialSums fun n => (μ (s n) (hsm n)).2.1
    have hdirected : DirectedOn (· ≤ ·) D := hmono.directed_le.directedOn_range
    have hnonempty : D.Nonempty := ⟨_, ⟨0, rfl⟩⟩
    have hlub : IsLUB D (μ (⋃ n, s n) (MeasurableSet.iUnion hsm) : C) :=
      μ.countably_additive s hsm hs'
    have hpush := hφ D _ hnonempty hdirected hlub
    change IsLUB (φ '' D) (φ (μ (⋃ n, s n) (MeasurableSet.iUnion hsm) : C)) at hpush
    have himage : φ '' D =
        Set.range fun N => ∑ n ∈ Finset.range N, φ (μ (s n) (hsm n) : C) := by
      rw [hD, ← Set.range_comp]
      congr 1
      funext N
      exact map_sum φ (fun n => (μ (s n) (hsm n) : C)) (Finset.range N)
    rwa [himage] at hpush

omit [PosSMulMono ℝ C] [PosSMulMono ℝ E] in
@[simp]
lemma coe_map_apply (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) (hφ : φ.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    ((μ.map φ hφ) s hs : E) = φ (μ s hs : C) := rfl

/-- Scalarizing an effect-valued measure by a normal state gives its ordinary real-valued
probability law, represented as an effect-valued measure in the classical order-unit space
`ℝ`.  For each measurable event this is precisely the abstract Born rule `ω(μ(s))`. -/
noncomputable def scalarize (μ : EffectValuedMeasure Ω C) (ω : 𝓢[ℝ, C]) (hω : ω.IsNormal) :
    EffectValuedMeasure Ω ℝ := μ.map ω hω

omit [PosSMulMono ℝ C] in
@[simp]
lemma coe_scalarize_apply (μ : EffectValuedMeasure Ω C) (ω : 𝓢[ℝ, C]) (hω : ω.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    ((μ.scalarize ω hω) s hs : ℝ) = ω (μ s hs : C) := rfl

omit [PosSMulMono ℝ C] [PosSMulMono ℝ E] in
/-- Pushing an effect-valued measure through a normal channel commutes with its finite simple
integral. This is the finite, algebraic naturality law underlying scalarization of the bounded
projection calculus; no second integration construction is introduced. -/
theorem map_simpleIntegral (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) (hφ : φ.IsNormal)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (s : ι → Set Ω)
    (hs : IsPartition s) :
    φ (simpleIntegral μ c s hs) = simpleIntegral (μ.map φ hφ) c s hs := by
  unfold simpleIntegral
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, coe_map_apply]

omit [PosSMulMono ℝ C] [PosSMulMono ℝ E] in
/-- Scalarizing a simple effect-valued integral by a normal state is the corresponding ordinary
real simple integral. -/
theorem scalarize_simpleIntegral (μ : EffectValuedMeasure Ω C) (ω : 𝓢[ℝ, C])
    (hω : ω.IsNormal) {ι : Type*} [Fintype ι] (c : ι → ℝ) (s : ι → Set Ω)
    (hs : IsPartition s) :
    ω (simpleIntegral μ c s hs) = simpleIntegral (μ.scalarize ω hω) c s hs :=
  map_simpleIntegral μ ω hω c s hs

end EffectValuedMeasure
