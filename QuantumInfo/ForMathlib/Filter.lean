/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.Peel

@[expose] public section

open Topology

--This is a stupid name for a stupid lemma
theorem Filter.Tendsto_inv_nat_mul_div_real (m : ℕ)
   : Filter.Tendsto (fun (x : ℕ) => ((↑x)⁻¹ * ↑(x / m) : ℝ)) Filter.atTop (𝓝 (1 / ↑m)) := by
  --Thanks aristotle!
  -- This simplifies to $\lim_{x \to \infty} \frac{\lfloor x / m \rfloor}{x} = \frac{1}{m}$ because the floor function grows asymptotically like $x / m$.
  have h_floor : Filter.Tendsto (fun x : ℕ => (Nat.floor (x / m : ℝ) : ℝ) / x) Filter.atTop (nhds (1 / (m : ℝ))) := by
    -- We'll use the fact that the floor function is bounded and apply the squeeze theorem.
    have h_floor_bound : ∀ x : ℕ, x > 0 → (Nat.floor (x / m : ℝ) : ℝ) / x ≥ (1 / m - 1 / x) ∧ (Nat.floor (x / m : ℝ) : ℝ) / x ≤ 1 / m := by
      cases eq_or_ne m 0
      · rename_i h
        intro x a
        subst h
        simp_all only [gt_iff_lt, CharP.cast_eq_zero, div_zero, Nat.floor_zero, zero_div, one_div, zero_sub, ge_iff_le,
          Left.neg_nonpos_iff, inv_nonneg, Nat.cast_nonneg, le_refl, and_self]
      · intro x a
        simp_all only [ne_eq, gt_iff_lt, one_div, ge_iff_le, tsub_le_iff_right]
        apply And.intro
        · rw [ inv_eq_one_div, div_add', div_le_div_iff₀ ] <;> first | positivity | nlinarith [ Nat.lt_floor_add_one ( ( x : ℝ ) / m ), show ( x : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr a, mul_div_cancel₀ ( x : ℝ ) ( show ( m : ℝ ) ≠ 0 by positivity ), inv_mul_cancel₀ ( show ( x : ℝ ) ≠ 0 by positivity ) ] ;
        · rw [ div_le_iff₀ ( by positivity ) ];
          simpa [ div_eq_inv_mul ] using Nat.floor_le ( by positivity : 0 ≤ ( x : ℝ ) / m );
    -- Apply the squeeze theorem to conclude the proof.
    have h_squeeze : Filter.Tendsto (fun x : ℕ => (1 / m : ℝ) - 1 / x) Filter.atTop (nhds (1 / m)) := by
      simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_squeeze tendsto_const_nhds ( Filter.eventually_atTop.mpr ⟨ 1, fun x hx => h_floor_bound x hx |>.1 ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 1, fun x hx => h_floor_bound x hx |>.2 ⟩ );
  -- Apply the hypothesis `h_floor` to conclude the proof.
  convert h_floor using 1;
  -- By definition of floor function, we know that ⌊(x : ℝ) / m⌋₊ is the greatest integer less than or equal to (x : ℝ) / m.
  funext x; simp [Nat.floor_div_natCast];
  ring

--Similar to `ENNReal.tendsto_toReal_iff` in `Mathlib/Topology/Instances/ENNReal/Lemmas`, but
-- instead of requiring finiteness for all values, just eventually is needed.
open Filter Topology ENNReal in
theorem ENNReal.tendsto_toReal_iff_of_eventually_ne_top
  {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ᶠ i in fi, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 x.toReal) ↔ Tendsto f fi (𝓝 x) := by
  have he₁ : f =ᶠ[fi] (fun n ↦ (f n).toNNReal) := by
    rw [EventuallyEq]
    peel hf with h
    simp [h]
  have he₂ : (fun n ↦ (f n).toReal) = (fun n ↦ ((f n).toNNReal : ℝ≥0∞).toReal) :=
    rfl
  rw [Filter.tendsto_congr' he₁, he₂]
  exact tendsto_toReal_iff (by finiteness) hx
