/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!

# Test functions are dense in the Schwartz space

A Schwartz function is the limit of its cutoffs by dilated bump functions.

## i. Overview

Let `b` be a smooth compactly supported function that equals one on the unit ball. The cutoff
`b (x / R) * f x` of a Schwartz function `f` is a test function. The derivatives of the cutoff
factor are bounded uniformly in `R ≥ 1` and vanish on the ball of radius `R`. The Schwartz
seminorms of `f - b (x / R) * f` are therefore bounded by `R⁻¹` times a seminorm of `f`.

## ii. Key results

- `exists_cutoff` : a smooth compactly supported function that equals one on the unit ball.
- `exists_bound_cutoff_sub` : the cutoff approximation estimate.
- `denseRange_ofTestFunction` : test functions are dense in the Schwartz space.

## iii. Table of contents

- A. The cutoff
- B. Density

## iv. References

None.

## A. The cutoff

- `exists_cutoff` : a smooth compactly supported function that equals one on the unit ball.
- `exists_bound_cutoff_sub` : the cutoff approximation estimate.

## B. Density

- `ofTestFunction` : a real test function is a Schwartz function.
- `cutoffTest` : the cutoff of a Schwartz function as a test function.
- `denseRange_ofTestFunction` : test functions are dense in the Schwartz space.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap ContDiff Distributions
open TopologicalSpace Topology Filter

namespace SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [HasContDiffBump V]

/-- A smooth compactly supported function that equals one on the unit ball. -/
lemma exists_cutoff : ∃ b : V → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    ∀ x : V, ‖x‖ ≤ 1 → b x = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨(b : V → ℝ), b.contDiff, b.hasCompactSupport, fun x hx => b.one_of_mem_closedBall ?_⟩
  simpa using hx

omit [FiniteDimensional ℝ V] [HasContDiffBump V] in
/-- The derivatives of the dilated cutoff minus one are bounded uniformly in the dilation. -/
lemma exists_bound_dilate {b : V → ℝ} (hb : ContDiff ℝ ∞ b) (hs : HasCompactSupport b) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : V,
      ‖iteratedFDeriv ℝ j (fun y => b (R⁻¹ • y) - 1) x‖ ≤ B := by
  have hc : Continuous fun y => ‖iteratedFDeriv ℝ j b y‖ :=
    (hb.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hsupp : HasCompactSupport fun y => ‖iteratedFDeriv ℝ j b y‖ :=
    (hs.iteratedFDeriv j).norm
  obtain ⟨B₀, hB₀⟩ := hc.bounded_above_of_compact_support hsupp
  refine ⟨max B₀ 0 + 1, by positivity, fun R hR x => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  let L : V →L[ℝ] V := R⁻¹ • ContinuousLinearMap.id ℝ V
  have hL : ‖L‖ ≤ 1 := by
    refine (norm_smul_le R⁻¹ (ContinuousLinearMap.id ℝ V)).trans ?_
    rw [norm_inv, Real.norm_of_nonneg hR0.le]
    calc R⁻¹ * ‖ContinuousLinearMap.id ℝ V‖ ≤ R⁻¹ * 1 := by
          gcongr; exact ContinuousLinearMap.norm_id_le
      _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ hR
  have hcomp : (fun y => b (R⁻¹ • y)) = b ∘ L := rfl
  have hbL : ContDiff ℝ ∞ (b ∘ L) := hb.comp L.contDiff
  rcases Nat.eq_zero_or_pos j with h0 | hj
  · subst h0
    rw [norm_iteratedFDeriv_zero]
    have : ‖b (R⁻¹ • x)‖ ≤ B₀ := by
      have := hB₀ (R⁻¹ • x)
      rwa [norm_norm, norm_iteratedFDeriv_zero] at this
    calc ‖b (R⁻¹ • x) - 1‖ ≤ ‖b (R⁻¹ • x)‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
      _ ≤ max B₀ 0 + 1 := by
        rw [norm_one]
        have := le_max_left B₀ 0
        linarith
  · have hsub : iteratedFDeriv ℝ j (fun y => b (R⁻¹ • y) - 1) x =
        iteratedFDeriv ℝ j (fun y => b (R⁻¹ • y)) x := by
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (f := fun y => b (R⁻¹ • y))
        (g := fun _ : V => (1 : ℝ)) (x := x) (hbL.contDiffAt.of_le (by exact_mod_cast le_top))
        contDiff_const.contDiffAt
      rw [show (fun y => b (R⁻¹ • y) - 1) = (fun y => b (R⁻¹ • y)) - fun _ => (1 : ℝ) from rfl,
        this, iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.1 hj)]
      simp
    rw [hsub, hcomp]
    have h1 : ‖iteratedFDeriv ℝ j (b ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j b (L x)‖ * ‖L‖ ^ j := by
      rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hb x (by exact_mod_cast le_top)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h2 : ‖iteratedFDeriv ℝ j b (L x)‖ ≤ B₀ := by
      have := hB₀ (L x)
      rwa [norm_norm] at this
    calc _ ≤ ‖iteratedFDeriv ℝ j b (L x)‖ * ‖L‖ ^ j := h1
      _ ≤ B₀ * 1 := by
        gcongr
        · exact (norm_nonneg _).trans h2
        · exact pow_le_one₀ (norm_nonneg _) hL
      _ ≤ max B₀ 0 + 1 := by
        rw [mul_one]
        have := le_max_left B₀ 0
        linarith

omit [FiniteDimensional ℝ V] [HasContDiffBump V] in
/-- The dilated cutoff minus one vanishes with all its derivatives inside the ball of radius `R`. -/
lemma iteratedFDeriv_dilate_eq_zero {b : V → ℝ} (hone : ∀ x : V, ‖x‖ ≤ 1 → b x = 1) {R : ℝ}
    (hR : 0 < R) (j : ℕ) {x : V} (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ j (fun y => b (R⁻¹ • y) - 1) x = 0 := by
  have hU : Metric.ball (0 : V) R ∈ nhds x :=
    Metric.isOpen_ball.mem_nhds (by simpa using hx)
  have h : (fun y => b (R⁻¹ • y) - 1) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [hU] with y hy
    have hy' : ‖y‖ < R := by simpa using hy
    have : ‖R⁻¹ • y‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
      rw [inv_mul_le_iff₀ hR]
      linarith
    simp [hone _ this]
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h j).self_of_nhds]
  simp

omit [FiniteDimensional ℝ V] [HasContDiffBump V] in
/-- **The cutoff approximation estimate.** The weighted derivatives of `(b (R⁻¹ x) - 1) f x` are
bounded by a constant times `R⁻¹`. -/
lemma exists_bound_cutoff_sub {b : V → ℝ} (hb : ContDiff ℝ ∞ b) (hs : HasCompactSupport b)
    (hone : ∀ x : V, ‖x‖ ≤ 1 → b x = 1) (f : 𝓢(V, ℝ)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : V,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (b (R⁻¹ • y) - 1) * f y) x‖ ≤ C / R := by
  choose B hB0 hB using fun i : ℕ => exists_bound_dilate hb hs i
  set C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i *
    SchwartzMap.seminorm ℝ (k + 1) (n - i) f with hC
  have hCnn : 0 ≤ C :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB0 i))
      (apply_nonneg _ _)
  refine ⟨C, hCnn, fun R hR x => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hcd : ContDiff ℝ ∞ (fun y => b (R⁻¹ • y) - 1) :=
    ((hb.comp (contDiff_const.smul contDiff_id)).sub contDiff_const)
  have hLeib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ∞) hcd (f.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  by_cases hx : ‖x‖ < R
  · have h0 : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y => b (R⁻¹ • y) - 1) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ = 0 :=
      fun i _ => by rw [iteratedFDeriv_dilate_eq_zero hone hR0 i hx]; simp
    rw [Finset.sum_eq_zero h0] at hLeib
    have : ‖iteratedFDeriv ℝ n (fun y => (b (R⁻¹ • y) - 1) * f y) x‖ = 0 :=
      le_antisymm hLeib (norm_nonneg _)
    rw [this, mul_zero]
    exact div_nonneg hCnn hR0.le
  · have hxR : R ≤ ‖x‖ := not_lt.1 hx
    have hxk : R * ‖x‖ ^ k ≤ ‖x‖ ^ (k + 1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (norm_nonneg x) k]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (b (R⁻¹ • y) - 1) * f y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y => b (R⁻¹ • y) - 1) x‖ *
            ‖iteratedFDeriv ℝ (n - i) f x‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y => b (R⁻¹ • y) - 1) x‖ *
            ‖iteratedFDeriv ℝ (n - i) f x‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * B i *
          SchwartzMap.seminorm ℝ (k + 1) (n - i) f) / R := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := hB i R hR x
        have h2 : ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤
            SchwartzMap.seminorm ℝ (k + 1) (n - i) f :=
          SchwartzMap.le_seminorm ℝ (k + 1) (n - i) f x
        rw [le_div_iff₀ hR0]
        have hD := norm_nonneg (iteratedFDeriv ℝ (n - i) f x)
        have hc : (0 : ℝ) ≤ n.choose i := by positivity
        calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => b (R⁻¹ • y) - 1) x‖ *
              ‖iteratedFDeriv ℝ (n - i) f x‖) * R
            ≤ ‖x‖ ^ k * ((n.choose i : ℝ) * B i * ‖iteratedFDeriv ℝ (n - i) f x‖) * R := by
              gcongr
          _ = (n.choose i : ℝ) * B i * ((R * ‖x‖ ^ k) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
              ring
          _ ≤ (n.choose i : ℝ) * B i * (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
              gcongr
              exact mul_nonneg hc (hB0 i)
          _ ≤ _ := by
              gcongr
              exact mul_nonneg hc (hB0 i)
      _ = C / R := by rw [hC, Finset.sum_div]

/-- A real test function is a Schwartz function. -/
def ofTestFunction : 𝓓((⊤ : Opens V), ℝ) →ₗ[ℝ] 𝓢(V, ℝ) where
  toFun φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

omit [FiniteDimensional ℝ V] [HasContDiffBump V] in
lemma ofTestFunction_injective : Function.Injective (ofTestFunction (V := V)) := fun φ ψ h => by
  ext x
  exact congrArg (fun f : 𝓢(V, ℝ) => f x) h

omit [FiniteDimensional ℝ V] [HasContDiffBump V] in
@[simp] lemma ofTestFunction_apply (φ : 𝓓((⊤ : Opens V), ℝ)) (x : V) :
    ofTestFunction φ x = φ x := rfl

/-- The cutoff of a Schwartz function by the dilated bump function, as a test function. -/
def cutoffTest {b : V → ℝ} (hb : ContDiff ℝ ∞ b) (hs : HasCompactSupport b) (f : 𝓢(V, ℝ))
    {R : ℝ} (hR : 0 < R) : 𝓓((⊤ : Opens V), ℝ) where
  toFun x := b (R⁻¹ • x) * f x
  contDiff' := (hb.comp (contDiff_const.smul contDiff_id)).mul (f.smooth ⊤)
  hasCompactSupport' := by
    have : HasCompactSupport fun x : V => b (R⁻¹ • x) :=
      hs.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))
    exact this.mul_right
  tsupport_subset' := fun _ _ => trivial

/-- **Test functions are dense in the Schwartz space.** -/
lemma denseRange_ofTestFunction : DenseRange (ofTestFunction (V := V)) := by
  intro f
  obtain ⟨b, hb, hs, hone⟩ := exists_cutoff (V := V)
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n : ℕ => ofTestFunction (cutoffTest hb hs f (R := (n : ℝ) + 1) (by positivity)),
    fun n => ⟨_, rfl⟩, ?_⟩
  rw [(schwartz_withSeminorms ℝ V ℝ).tendsto_nhds_atTop]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨C, hC0, hC⟩ := exists_bound_cutoff_sub hb hs hone f k n
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N, fun m hm => ?_⟩
  have hR : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hmN : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hRpos : 0 < (m : ℝ) + 1 := by linarith
  have hle : SchwartzMap.seminorm ℝ k n
      (ofTestFunction (cutoffTest hb hs f (R := (m : ℝ) + 1) hRpos) - f) ≤ C / ((m : ℝ) + 1) := by
    refine SchwartzMap.seminorm_le_bound ℝ k n _ (div_nonneg hC0 hRpos.le) fun x => ?_
    have := hC ((m : ℝ) + 1) hR x
    have heq : ⇑(ofTestFunction (cutoffTest hb hs f (R := (m : ℝ) + 1) hRpos) - f) =
        fun y => (b (((m : ℝ) + 1)⁻¹ • y) - 1) * f y := by
      funext y
      change b (((m : ℝ) + 1)⁻¹ • y) * f y - f y = (b (((m : ℝ) + 1)⁻¹ • y) - 1) * f y
      ring
    rw [heq]
    exact this
  refine lt_of_le_of_lt hle ?_
  rw [div_lt_iff₀ hRpos]
  rw [div_lt_iff₀ hε] at hN
  nlinarith

end SchwartzMap
