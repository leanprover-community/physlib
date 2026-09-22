/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Norm
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!

# States separate the order

## i. Overview

The positive cone of an Archimedean order-unit space is closed in the order-unit norm. Geometric
Hahn--Banach separation therefore produces, for every point outside that cone, a continuous linear
functional that is nonnegative on the cone and negative at that point. The order unit forces this
functional to take a strictly positive value at `1`, so it can be normalized to a state.

## ii. Key results

- `UnitalPositiveLinearMap.exists_apply_neg_of_not_nonneg`
- `UnitalPositiveLinearMap.nonneg_iff_forall_state_nonneg`
- `UnitalPositiveLinearMap.state_nonempty`
- `UnitalPositiveLinearMap.sSup_abs_apply_eq_orderUnitNorm`

-/

@[expose] public section

open IsArchimedeanOrderUnit

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]

namespace UnitalPositiveLinearMap

/-- Every element outside the positive cone is detected by a state with strictly negative value. -/
theorem exists_apply_neg_of_not_nonneg {x : E} (hx : ¬ 0 ≤ x) :
    ∃ ω : 𝓢[ℝ, E], ω x < 0 := by
  let _ : NormedAddCommGroup E := orderUnitNormedAddCommGroup (E := E)
  let _ : NormedSpace ℝ E := orderUnitNormedSpace (E := E)
  obtain ⟨f, u, hfx, hcone⟩ := geometric_hahn_banach_point_closed
    (convex_Ici (0 : E)) isClosed_nonneg_orderUnitNorm hx
  have hu : u < 0 := by simpa using hcone 0 le_rfl
  have hf_nonneg : ∀ y : E, 0 ≤ y → 0 ≤ f y := by
    intro y hy
    by_contra hfy
    have hfy' : f y < 0 := lt_of_not_ge hfy
    let t : ℝ := (u - 1) / f y
    have ht : 0 ≤ t := div_nonneg_of_nonpos (by linarith) hfy'.le
    have hty : 0 ≤ t • y := smul_nonneg ht hy
    have hsep := hcone (t • y) hty
    rw [map_smul, smul_eq_mul] at hsep
    have hcalc : t * f y = u - 1 := by
      dsimp [t]
      exact div_mul_cancel₀ (u - 1) hfy'.ne
    linarith
  let p : E →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ f.toLinearMap hf_nonneg
  have hf_one_pos : 0 < f (1 : E) := by
    have hf_one_nonneg : 0 ≤ f (1 : E) := hf_nonneg 1 IsOrderUnit.one_nonneg
    refine lt_of_le_of_ne hf_one_nonneg ?_
    intro hf_one
    have hf_one_zero : f (1 : E) = 0 := hf_one.symm
    obtain ⟨n, hn⟩ := IsOrderUnit.exists_nsmul_one_le x
    obtain ⟨m, hm⟩ := IsOrderUnit.exists_nsmul_one_le (-x)
    have hupper : f x ≤ 0 := by
      have := p.monotone' hn
      change f x ≤ f (n • (1 : E)) at this
      simpa [hf_one_zero] using this
    have hlower : 0 ≤ f x := by
      have := p.monotone' hm
      change f (-x) ≤ f (m • (1 : E)) at this
      simp [hf_one_zero] at this
      linarith
    linarith
  let ω : 𝓢[ℝ, E] := ofLinearMap ((f (1 : E))⁻¹ • f.toLinearMap)
    (fun y hy => mul_nonneg (inv_nonneg.mpr hf_one_pos.le) (hf_nonneg y hy))
    (by simp [hf_one_pos.ne'])
  refine ⟨ω, ?_⟩
  change (f (1 : E))⁻¹ * f x < 0
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hf_one_pos) (hfx.trans hu)

/-- Positivity is completely detected by states. -/
theorem nonneg_iff_forall_state_nonneg (x : E) :
    0 ≤ x ↔ ∀ ω : 𝓢[ℝ, E], 0 ≤ ω x := by
  constructor
  · exact fun hx ω => ω.map_nonneg hx
  · contrapose!
    exact exists_apply_neg_of_not_nonneg

/-- Every nontrivial Archimedean order-unit space has a state. -/
theorem state_nonempty [Nontrivial E] : Nonempty 𝓢[ℝ, E] := by
  have hone_ne : (1 : E) ≠ 0 := by
    intro hone
    apply not_subsingleton E
    constructor
    intro a b
    have hzero (y : E) : y = 0 := by
      obtain ⟨n, hn⟩ := IsOrderUnit.exists_nsmul_one_le y
      obtain ⟨m, hm⟩ := IsOrderUnit.exists_nsmul_one_le (-y)
      have hy_nonpos : y ≤ 0 := by simpa [hone] using hn
      have hy_nonneg : 0 ≤ y := neg_nonpos.mp (by simpa [hone] using hm)
      exact le_antisymm hy_nonpos hy_nonneg
    rw [hzero a, hzero b]
  have hnot : ¬ 0 ≤ -(1 : E) := by
    intro h
    have hone : (1 : E) = 0 := le_antisymm (neg_nonneg.mp h) IsOrderUnit.one_nonneg
    exact hone_ne hone
  obtain ⟨ω, _⟩ := exists_apply_neg_of_not_nonneg hnot
  exact ⟨ω⟩

/-- Every scalar strictly below the order-unit norm is exceeded by the absolute value of some
state evaluation. -/
lemma exists_state_abs_apply_gt_of_lt_orderUnitNorm [Nontrivial E] (x : E) {r : ℝ}
    (hr : r < orderUnitNorm x) : ∃ ω : 𝓢[ℝ, E], r < |ω x| := by
  by_cases hr0 : r < 0
  · obtain ⟨ω⟩ := state_nonempty (E := E)
    exact ⟨ω, hr0.trans_le (abs_nonneg _)⟩
  have hr_nonneg : 0 ≤ r := le_of_not_gt hr0
  have hnot : r ∉ orderUnitBounds x := by
    rw [mem_orderUnitBounds_iff]
    exact not_le.mpr hr
  by_cases hu : x ≤ r • (1 : E)
  · have hl : ¬ -(r • (1 : E)) ≤ x := fun hl => hnot ⟨hr_nonneg, hl, hu⟩
    have hnonneg : ¬ 0 ≤ r • (1 : E) + x := by
      simpa [neg_le_iff_add_nonneg, add_comm] using hl
    obtain ⟨ω, hω⟩ := exists_apply_neg_of_not_nonneg hnonneg
    refine ⟨ω, ?_⟩
    rw [map_add, map_smul, smul_eq_mul, map_one, mul_one] at hω
    exact lt_of_lt_of_le (by linarith) (neg_le_abs (ω x))
  · have hnonneg : ¬ 0 ≤ r • (1 : E) - x := by
      simpa [sub_nonneg] using hu
    obtain ⟨ω, hω⟩ := exists_apply_neg_of_not_nonneg hnonneg
    refine ⟨ω, ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, map_one, mul_one] at hω
    exact lt_of_lt_of_le (by linarith) (le_abs_self (ω x))

/-- The order-unit norm is the supremum of the absolute values assigned by states. -/
theorem sSup_abs_apply_eq_orderUnitNorm [Nontrivial E] (x : E) :
    sSup (Set.range fun ω : 𝓢[ℝ, E] => |ω x|) = orderUnitNorm x := by
  have hbdd : BddAbove (Set.range fun ω : 𝓢[ℝ, E] => |ω x|) :=
    ⟨orderUnitNorm x, by
      rintro _ ⟨ω, rfl⟩
      exact ω.abs_apply_le_orderUnitNorm x⟩
  obtain ⟨ω₀⟩ := state_nonempty (E := E)
  have hne : (Set.range fun ω : 𝓢[ℝ, E] => |ω x|).Nonempty :=
    ⟨|ω₀ x|, Set.mem_range_self ω₀⟩
  apply le_antisymm
  · exact csSup_le hne fun _ h => by
      obtain ⟨ω, rfl⟩ := h
      exact ω.abs_apply_le_orderUnitNorm x
  · apply le_of_forall_lt
    intro r hr
    obtain ⟨ω, hω⟩ := exists_state_abs_apply_gt_of_lt_orderUnitNorm x hr
    exact hω.trans_le (le_csSup hbdd (Set.mem_range_self ω))

/-- On a positive element, the absolute values in the norm representation can be omitted. -/
theorem sSup_apply_eq_orderUnitNorm [Nontrivial E] {x : E} (hx : 0 ≤ x) :
    sSup (Set.range fun ω : 𝓢[ℝ, E] => ω x) = orderUnitNorm x := by
  have hrange : (Set.range fun ω : 𝓢[ℝ, E] => ω x) =
      Set.range fun ω : 𝓢[ℝ, E] => |ω x| := by
    ext y
    constructor <;> rintro ⟨ω, rfl⟩
    · exact ⟨ω, abs_of_nonneg (ω.map_nonneg hx)⟩
    · exact ⟨ω, (abs_of_nonneg (ω.map_nonneg hx)).symm⟩
  rw [hrange, sSup_abs_apply_eq_orderUnitNorm]

/-- A state, regarded canonically as a continuous functional on the copy of `E` carrying the
order-unit norm. -/
noncomputable def toOrderUnitContinuousLinearMap (ω : 𝓢[ℝ, E]) :
    WithOrderUnitNorm E →L[ℝ] ℝ :=
  ω.toLinearMap.mkContinuous 1 fun x => by
    rw [one_mul, Real.norm_eq_abs, WithOrderUnitNorm.norm_eq_orderUnitNorm]
    exact ω.abs_apply_le_orderUnitNorm x

@[simp]
lemma toOrderUnitContinuousLinearMap_apply (ω : 𝓢[ℝ, E]) (x : E) :
    ω.toOrderUnitContinuousLinearMap x = ω x := rfl

/-- The continuous-dual realization of states is injective. -/
lemma toOrderUnitContinuousLinearMap_injective :
    Function.Injective
      (toOrderUnitContinuousLinearMap : 𝓢[ℝ, E] → WithOrderUnitNorm E →L[ℝ] ℝ) := by
  intro ω φ h
  ext x
  have hx := DFunLike.congr_fun h (WithOrderUnitNorm.linearEquiv x)
  change ω x = φ x at hx
  exact hx

/-- In every nontrivial Archimedean order-unit space, the distinguished order unit has norm
exactly one. -/
@[simp]
theorem orderUnitNorm_one [Nontrivial E] : orderUnitNorm (1 : E) = 1 := by
  rw [← sSup_abs_apply_eq_orderUnitNorm]
  obtain ⟨ω₀⟩ := state_nonempty (E := E)
  have hrange : (Set.range fun ω : 𝓢[ℝ, E] => |ω (1 : E)|) = {1} := by
    ext y
    constructor
    · rintro ⟨ω, rfl⟩
      simp
    · intro hy
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨ω₀, by simp⟩
  rw [hrange, csSup_singleton]

/-- The operator norm used locally for the continuous dual of the order-unit-norm copy. -/
noncomputable local instance : Norm (WithOrderUnitNorm E →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

/-- Every state has continuous-dual norm exactly one for the order-unit norm. -/
@[simp]
theorem norm_toOrderUnitContinuousLinearMap [Nontrivial E] (ω : 𝓢[ℝ, E]) :
    ‖ω.toOrderUnitContinuousLinearMap‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul, Real.norm_eq_abs, WithOrderUnitNorm.norm_eq_orderUnitNorm]
    exact ω.abs_apply_le_orderUnitNorm x
  · calc
      1 = ‖ω.toOrderUnitContinuousLinearMap (WithOrderUnitNorm.linearEquiv (1 : E))‖ := by
        change 1 = ‖ω (1 : E)‖
        rw [map_one]
        norm_num
      _ ≤ ‖ω.toOrderUnitContinuousLinearMap‖ *
          ‖WithOrderUnitNorm.linearEquiv (1 : E)‖ :=
        ω.toOrderUnitContinuousLinearMap.le_opNorm _
      _ = ‖ω.toOrderUnitContinuousLinearMap‖ := by
        rw [WithOrderUnitNorm.norm_eq_orderUnitNorm, WithOrderUnitNorm.linearEquiv_apply,
          orderUnitNorm_one, mul_one]

end UnitalPositiveLinearMap
