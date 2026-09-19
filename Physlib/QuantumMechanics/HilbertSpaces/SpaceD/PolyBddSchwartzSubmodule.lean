/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# Polynomially-bounded Schwartz submodules

## i. Overview

In this module we define polynomially-bounded Schwartz submodules of `SpaceDHilbertSpace d μ`.

For each `a : ℕ∞`, `PolyBddSchwartzSubmodule d a μ` is the submodule corresponding to Schwartz
maps `f` satisfying the polynomial growth bounds `‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` for all `(k : ℕ) ≤ a`.
In particular, for `a = ⊤` such a bound holds for all natural numbers.

These serve as a natural domain for singular unbounded operators. For example, the `1/r` Coulomb
potential operator maps `PolyBddSchwartzSubmodule d ⊤ μ` to itself. In the same way that multiplying
a Schwartz map by any polynomial in the coordinates results in a square-integrable function,
polynomially-bounded Schwartz maps may be multiplied by Laurent polynomials and remain
square-integrable (the precise condition depends on `d`, `a` and the negative degree of
the Laurent polynomial).

Note: the condition defining polynomially-bounded Schwartz maps is phrased as
`‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` rather than as `‖f x‖ ≤ Cₖ * ‖x‖ ^ k` to mirror `SchwartzMap.decay`.
These two conditions only differ at `x = 0` and are therefore equivalent for `d > 0` since
then `f 0` may be determined by continuity. For `d = 0` the former does not constrain `f 0 = 0`
(since `x = 0` is the only point and `0⁻¹ = 0`) while the latter does (and would therefore spoil
their being dense in `SpaceDHilbertSpace 0 ≅ ℂ`).

## ii. Key results

- `PolyBddSchwartzSubmodule d (a : ℕ∞) μ`: Restriction of `SchwartzSubmodule d μ` to those
  Schwartz maps which are bounded by powers of `‖x‖`.
- `PolyBddSchwartzSubmodule.dense`: These submodules are dense in `SpaceDHilbertSpace d μ`.

## iii. Table of contents

- A. Definitions
- B. Coercions
- C. (In)equalities
- D. Density

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

noncomputable section

open MeasureTheory
open InnerProductSpace
open SchwartzMap
open SchwartzSubmodule

/-!
## A. Definitions
-/

/-- A function is a bounded Schwartz map if it is both Schwartz and bounded by powers of `‖x‖`. -/
def PolyBddSchwartzMap (d : ℕ) (a : ℕ∞) : Submodule ℂ 𝓢(Space d, ℂ) where
  carrier := {f : 𝓢(Space d, ℂ) |
    ∀ k : ℕ, k ≤ a → ∃ C : ℝ, 0 < C ∧ ∀ x : Space d, ‖x‖ ^ (-k : ℤ) * ‖f x‖ ≤ C}
  add_mem' := by
    intro f g hf hg k hk
    obtain ⟨C₁, hC₁_pos, hC₁⟩ := hf k hk
    obtain ⟨C₂, hC₂_pos, hC₂⟩ := hg k hk
    refine ⟨C₁ + C₂, by positivity, fun x ↦ ?_⟩
    refine le_trans ?_ (add_le_add (hC₁ x) (hC₂ x))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le (f x) (g x)) (by positivity)
  zero_mem' := fun _ _ ↦ ⟨1, by simp⟩
  smul_mem' := by
    intro c f hf k hk
    obtain ⟨C, hC_pos, hC⟩ := hf k hk
    refine ⟨(1 + ‖c‖) * C, by positivity, fun x ↦ ?_⟩
    rw [smul_apply, norm_smul, mul_rotate', mul_comm ‖f x‖]
    exact le_trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)) (by linarith)

/-- The continuous linear map `schwartzIncl` with domain restricted to `PolyBddSchwartzMap d a`. -/
def polyBddSchwartzIncl {d : ℕ} {a : ℕ∞} (μ : Measure (Space d)) [μ.HasTemperateGrowth] :
    PolyBddSchwartzMap d a →L[ℂ] SpaceDHilbertSpace d μ :=
  ⟨(schwartzIncl μ).domRestrict (PolyBddSchwartzMap d a),
    (schwartzIncl μ).continuous_domRestrict (schwartzIncl μ).continuous _⟩

/-- The submodule of `SpaceDHilbertSpace d` corresponding to bounded Schwartz maps. -/
abbrev PolyBddSchwartzSubmodule
    (d : ℕ) (a : ℕ∞) (μ : Measure (Space d) := volume) [μ.HasTemperateGrowth] :
    Submodule ℂ (SpaceDHilbertSpace d μ) :=
  (polyBddSchwartzIncl (a := a) μ).range

lemma polyBddSchwartzIncl_injective
    {d : ℕ} (a : ℕ∞) (μ : Measure (Space d)) [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] :
    Function.Injective (polyBddSchwartzIncl (a := a) μ) :=
  LinearMap.injective_domRestrict_iff.mpr <| (schwartzIncl_ker μ).symm ▸ disjoint_bot_right

/-- The linear equivalence between polynomially-bounded Schwartz maps and the corresponding
  submodule of the Hilbert space. -/
def polyBddSchwartzEquiv
    {d : ℕ} {a : ℕ∞} (μ : Measure (Space d)) [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] :
    PolyBddSchwartzMap d a ≃ₗ[ℂ] PolyBddSchwartzSubmodule d a μ :=
  LinearEquiv.ofInjective (polyBddSchwartzIncl μ).toLinearMap (polyBddSchwartzIncl_injective a μ)

namespace PolyBddSchwartzSubmodule

variable {d : ℕ} {a : ℕ∞}
variable (μ : Measure (Space d)) [μ.HasTemperateGrowth]

/-!
## B. Coercions
-/

instance : CoeOut (PolyBddSchwartzMap d a) 𝓢(Space d, ℂ) := ⟨fun f ↦ f.val⟩

instance : CoeFun (PolyBddSchwartzMap d a) (fun _ ↦ Space d → ℂ) := ⟨fun f ↦ ⇑f.val⟩

@[simp]
lemma toFun_eq_coe (f : PolyBddSchwartzMap d a) (x : Space d) : f.val.toFun x = f.val x := rfl

lemma polyBddSchwartzEquiv_symm_apply_coe [μ.IsOpenPosMeasure]
    {ψ : SchwartzSubmodule d μ} (hψ : ↑ψ ∈ PolyBddSchwartzSubmodule d a μ) :
    ((polyBddSchwartzEquiv μ).symm ⟨ψ, hψ⟩).val = (schwartzEquiv μ).symm ψ := by
  apply (schwartzEquiv μ).injective
  apply SetLike.coe_eq_coe.mp
  obtain ⟨g, hg⟩ := (polyBddSchwartzEquiv μ).surjective ⟨ψ.val, hψ⟩
  have hg' : polyBddSchwartzIncl μ g = ψ := SetLike.coe_eq_coe.mpr hg
  rw [← hg, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, ← hg']
  rfl

variable {μ} in
lemma polyBddSchwartzEquiv_coe_ae [μ.IsOpenPosMeasure] (f : PolyBddSchwartzMap d a) :
    polyBddSchwartzEquiv μ f =ᵐ[μ] f.val :=
  schwartzEquiv_coe_ae f.val

/-!
### C. (In)equalities
-/

lemma PolyBddSchwartzMap_zero_eq_top (d : ℕ) : PolyBddSchwartzMap d 0 = ⊤ := by
  ext f
  have := f.decay 0 0
  simp_all [PolyBddSchwartzMap]

lemma PolyBddSchwartzMap_antitone (d : ℕ) {a b : ℕ∞} (h : a ≤ b) :
    PolyBddSchwartzMap d b ≤ PolyBddSchwartzMap d a := fun _ hx k hk ↦ hx k (hk.trans h)

lemma of_zero_eq : PolyBddSchwartzSubmodule d 0 μ = SchwartzSubmodule d μ := by
  simp [PolyBddSchwartzSubmodule, polyBddSchwartzIncl, PolyBddSchwartzMap_zero_eq_top]

lemma le_SchwartzSubmodule (d : ℕ) (a : ℕ∞) : PolyBddSchwartzSubmodule d a ≤ SchwartzSubmodule d :=
  LinearMap.range_domRestrict_le_range _ _

lemma antitone {a b : ℕ∞} (h : a ≤ b) :
    PolyBddSchwartzSubmodule d b μ ≤ PolyBddSchwartzSubmodule d a μ := by
  simp only [PolyBddSchwartzSubmodule, polyBddSchwartzIncl,
    ContinuousLinearMap.toLinearMap_domRestrict, LinearMap.range_domRestrict]
  exact Submodule.map_mono (PolyBddSchwartzMap_antitone d h)

/-!
### D. Density
-/

open Filter Complex

private lemma enorm_bump_mul_le_enorm {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] {c : E} (f : ContDiffBump c) (g : E → 𝕜) (x : E) :
    ‖f x * g x‖ₑ ≤ ‖g x‖ₑ := by
  nth_rw 2 [← one_mul (g x)]
  simp_rw [enorm_mul]
  refine mul_le_mul_left ?_ ‖g x‖ₑ
  apply enorm_le_iff_norm_le.mpr
  rw [norm_algebraMap', Real.norm_eq_abs, norm_one, ← abs_one]
  exact abs_le_abs_of_nonneg f.nonneg f.le_one

private lemma dense_zero_top (μ : Measure (Space 0)) [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] :
    Dense (PolyBddSchwartzSubmodule 0 ⊤ μ : Set (SpaceDHilbertSpace 0 μ)) := by
  suffices PolyBddSchwartzMap 0 ⊤ = ⊤ by
    simp [PolyBddSchwartzSubmodule, polyBddSchwartzIncl, this]
  refine Submodule.eq_top_iff'.mpr (fun f k hk ↦ ?_)
  refine ⟨1 + ‖f 0‖, by positivity, fun x ↦ ?_⟩
  simp only [Space.point_dim_zero_eq, norm_zero, zpow_neg, zpow_natCast]
  rcases k with _ | k <;> simp [add_nonneg]

TODO "Generalize density of PolyBddSchwartzSubmodule to more general measures than just μ ≤ volume."

lemma dense_top (hμ : μ ≤ volume) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] :
    Dense (PolyBddSchwartzSubmodule d ⊤ μ : Set (SpaceDHilbertSpace d μ)) := by
  rcases eq_zero_or_pos d with (rfl | hd)
  · -- `d = 0`: Every function `Space 0 ≅ {0} → ℂ` is in `PolyBddSchwartzSubmodule 0 ⊤ μ`.
    exact dense_zero_top _
  · -- `d > 0`: Construct a sequence in `PolyBddSchwartzSubmodule d ⊤ μ` which tends to `ξ`
    intro ξ
    apply mem_closure_iff_seq_limit.mpr
    -- `ψₙ = [fₙ]` is a sequence in `SchwartzSubmodule` which tends to `ξ`
    obtain ⟨ψ, hψ, hψξ⟩ := mem_closure_iff_seq_limit.mp (SchwartzSubmodule.dense d μ ξ)
    let f (n : ℕ) : 𝓢(Space d, ℂ) := (schwartzEquiv μ).symm ⟨ψ n, hψ n⟩
    -- `bₙ` is a sequence of bump functions with shrinking domain
    let b (n : ℕ) : ContDiffBump (0 : Space d) :=
      ⟨(n + 1)⁻¹, 2 * (n + 1 : ℝ)⁻¹, by positivity, lt_two_mul_self Nat.inv_pos_of_nat⟩
    -- `φₙ = [bₙfₙ]` is a sequence in `SchwartzSubmodule` which tends to `0`
    let g (n : ℕ) : 𝓢(Space d, ℂ) := smulLeftCLM ℂ (b n) (f n)
    let φ (n : ℕ) : SpaceDHilbertSpace d μ := schwartzIncl μ (g n)
    have hg (n : ℕ) (x : Space d) : g n x = b n x * f n x := by
      have := (b n).hasCompactSupport.hasTemperateGrowth (b n).contDiff
      rw [smulLeftCLM_apply_apply this, ← Complex.coe_smul, smul_eq_mul]
    use ψ - φ
    constructor
    · intro n
      rw [SetLike.mem_coe, LinearMap.mem_range, Subtype.exists]
      refine ⟨f n - g n, ?_, by simp [f, φ, polyBddSchwartzIncl, ← schwartzEquiv_apply_coe]⟩
      intro k _
      obtain ⟨C, hC_pos, hC⟩ := (f n).decay 0 0
      simp only [pow_zero, norm_iteratedFDeriv_zero, one_mul] at hC
      use (n + 1) ^ k * C
      refine ⟨by positivity, fun x ↦ ?_⟩
      rcases le_or_gt ‖x‖ (b n).rIn with (hx | hx)
      · have h_one : b n x = 1 := (b n).one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
        exact le_of_eq_of_le (b := 0) (by simp [hg, h_one]) (by positivity)
      · refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) hC_pos.le
        · rw [← inv_zpow', zpow_natCast]
          gcongr
          exact (inv_lt_of_inv_lt₀ (Nat.cast_add_one_pos n) hx).le
        · refine le_trans ?_ (hC x)
          rw [sub_apply, ← one_mul (f n x), hg, ← sub_mul, norm_mul, norm_mul, norm_one]
          gcongr
          rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
          exact abs_sub_le_of_nonneg_of_le zero_le_one le_rfl (b n).nonneg (b n).le_one
    · refine tendsto_of_sub_tendsto_zero ξ hψξ ?_
      rw [sub_sub_cancel_left, Pi.neg_def, ← neg_zero, tendsto_neg_iff]
      -- Split `φₙ = σₙ + (φₙ - σₐ)` with `σₙ ≔ [bₙξ]` a sequence in `SpaceDHilbertSpace`
      let s (n : ℕ) : Space d → ℂ := fun x ↦ b n x * ξ x
      let σ (n : ℕ) : SpaceDHilbertSpace d μ := by
        refine mk (f := s n) ?_
        refine lt_of_le_of_lt ?_ (memHS_coe ξ)
        exact eLpNorm_mono_enorm
          ((continuous_ofReal.comp (b n).continuous).aestronglyMeasurable.mul
            ξ.val.aestronglyMeasurable)
          (enorm_bump_mul_le_enorm (b n) ξ)
      have hψ_ae (n : ℕ) : ψ n =ᵐ[μ] f n := (schwartzEquiv_symm_coe_ae ⟨ψ n, hψ n⟩).symm
      have hφ_ae (n : ℕ) : φ n =ᵐ[μ] g n := schwartzEquiv_coe_ae (g n)
      have hσ_ae (n : ℕ) : σ n =ᵐ[μ] s n := coeFn_mk _
      have hφσ_ae (n : ℕ) : (φ - σ) n =ᵐ[μ] g n - s n :=
        (coeFn_sub (φ n) (σ n)).trans <| (hφ_ae n).sub (hσ_ae n)
      have hψξ_ae (n : ℕ) : ψ n - ξ =ᵐ[μ] f n - ξ :=
        (coeFn_sub (ψ n) ξ).trans <| (hψ_ae n).sub EventuallyEq.rfl
      refine tendsto_of_sub_tendsto_zero (f := σ) 0 ?_ ?_
      · -- `σ = bₙξ → 0` since the norms are bounded by the integral of `‖ξ‖²` (independent of `n`!)
        -- on a domain which tends to zero
        apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
        let B (n : ℕ) : Set (Space d) := Metric.ball 0 (b n).rOut
        have hξB : Tendsto (fun n ↦ ∫⁻ x in B n, ‖ξ x‖ₑ ^ 2 ∂μ) atTop (nhds 0) := by
          refine tendsto_setLIntegral_zero ?_ ?_
          · refine lt_top_iff_ne_top.mp ?_
            have h := L2.eLpNorm_rpow_two_norm_lt_top ξ
            have hξ2 : AEStronglyMeasurable (fun x ↦ ‖(ξ : Space d → ℂ) x‖ ^ 2) μ :=
              ξ.val.aestronglyMeasurable.norm.pow 2
            simp only [Real.rpow_ofNat] at h
            rw [eLpNorm_one_eq_lintegral_enorm hξ2] at h
            simpa [enorm_pow, enorm_norm] using h
          · have : NeZero d := ⟨hd.ne'⟩
            refine tendsto_const_nhds.squeeze ?_ zero_le (fun n ↦ hμ (B n))
            let C : ℝ := (ENNReal.ofReal (√Real.pi ^ d / Real.Gamma (d / 2 + 1))).toReal
            have hvolB : ∀ n, volume (B n) = ENNReal.ofReal (C * (b n).rOut ^ d) := by
              intro n
              simp [B, InnerProductSpace.volume_ball, C, mul_comm,
                ENNReal.ofReal_pow (b n).rOut_pos.le]
            simp_rw [hvolB, ← ENNReal.ofReal_zero, b, ← one_div, mul_pow, ← mul_assoc]
            rw [← mul_zero (C * 2 ^ d), ← zero_pow (M₀ := ℝ) hd.ne']
            refine ENNReal.tendsto_ofReal <| Tendsto.const_mul (C * 2 ^ d) ?_
            exact tendsto_one_div_add_atTop_nhds_zero_nat.pow d
        refine tendsto_const_nhds.squeeze hξB (zero_le) (fun n ↦ ?_)
        suffices ∫⁻ x, ‖σ n x‖ₑ ^ 2 ∂μ = ∫⁻ x in B n, ‖σ n x‖ₑ ^ 2 ∂μ by
          rw [this]
          refine setLIntegral_mono_ae' measurableSet_ball ?_
          filter_upwards [hσ_ae n] with x h _
          exact ENNReal.pow_le_pow_left <| h ▸ enorm_bump_mul_le_enorm (b n) ξ x
        have h (A : Set (Space d)) : ∫⁻ x in A, ‖σ n x‖ₑ ^ 2 ∂μ = ∫⁻ x in A, ‖s n x‖ₑ ^ 2 ∂μ :=
          lintegral_congr_ae ((hσ_ae n).fun_comp (fun z ↦ ‖z‖ₑ ^ 2)).restrict
        rw [← setLIntegral_univ, h, h, setLIntegral_univ]
        refine (setLIntegral_eq_of_support_subset ?_).symm
        refine Function.support_subset_iff'.mpr (fun x hx ↦ ?_)
        simp [s, (b n).zero_of_le_dist (not_lt.mp hx)]
      · -- `φₙ - σₙ = bₙ(ψₙ - ξ) → 0` since `ψₙ → ξ` (by definition) and the `bₙ` are bounded
        apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
        have hψξ : Tendsto (fun n ↦ ∫⁻ x, ‖(ψ n - ξ) x‖ₑ ^ 2 ∂μ) atTop (nhds 0) :=
          tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mp (sub_self ξ ▸ hψξ.sub_const ξ)
        refine Tendsto.squeeze tendsto_const_nhds hψξ (zero_le) (fun n ↦ ?_)
        refine lintegral_mono_ae ?_
        filter_upwards [hφσ_ae n, hψξ_ae n] with x h h'
        simp_rw [h, h', Pi.sub_apply, hg, s, ← mul_sub]
        exact ENNReal.pow_le_pow_left <| enorm_bump_mul_le_enorm (b n) (fun x ↦ f n x - ξ x) x

lemma dense (hμ : μ ≤ volume) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] :
    Dense (PolyBddSchwartzSubmodule d a μ : Set (SpaceDHilbertSpace d μ)) :=
  (dense_top μ hμ).mono (antitone μ le_top)

end PolyBddSchwartzSubmodule
end
end SpaceDHilbertSpace
end QuantumMechanics
