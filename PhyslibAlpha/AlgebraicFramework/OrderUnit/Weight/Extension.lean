/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Weight.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Basic
public import Mathlib.Tactic.Module

/-!

# Extending finite weights

## i. Overview

A finite weight on the positive cone of an order-unit space extends uniquely to a positive linear
functional on the whole space. Normalized weights therefore give states as a specialization.

The extension shifts and undoes: since `1` is an order unit, any `x : E` becomes nonnegative after
adding enough copies of `1` (`exists_real_shift_nonneg` gives `r` with `r • 1 + x ≥ 0`), so define
`toFun x := w (r • 1 + x) - r * w 1` — undo the shift after reading `w` on the cone
and check it's independent of the `r` chosen.

## ii. Key definitions and results

- `Weight.IsFinite.toFun`
- `Weight.IsFinite.toLinearMap`
- `Weight.IsFinite.toPositiveLinearMap`

## iii. Table of contents

- A. Shifting vectors into the positive cone
- B. Shift independence
- C. The additive extension
- D. The positive linear extension

-/

@[expose] public section

open scoped ENNReal NNReal

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

namespace Weight

/-! ## A. Shifting vectors into the positive cone -/

omit [PosSMulMono ℝ E] in
/-- Every element of `E` becomes nonnegative after adding enough copies of the order unit.
Internal to the shift-and-back construction of `toFun` below; not meant to be used directly. -/
lemma exists_real_shift_nonneg (x : E) : ∃ r : ℝ, 0 ≤ r • (1 : E) + x := by
  obtain ⟨n, hn⟩ := IsOrderUnit.exists_nsmul_one_le (-x)
  refine ⟨n, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℝ n (1 : E)] at hn
  rw [← sub_neg_eq_add]
  exact sub_nonneg.mpr hn

omit [One E] [IsOrderUnit E] in
/-- Once a weight is finite on the two cone elements involved, it turns cone addition into real
addition. This, and `toReal_map_nnreal_smul` below, are the only two facts about pushing `w`
through `ENNReal` arithmetic that the rest of this file needs; every additivity or homogeneity
proof below reduces to one of them plus a purely algebraic identity in `E`. -/
lemma IsFinite.toReal_map_add {w : Weight E} (hw : w.IsFinite) (c d : PosCone E) :
    (w (c + d)).toReal = (w c).toReal + (w d).toReal := by
  rw [w.map_add, ENNReal.toReal_add (hw c) (hw d)]

omit [One E] [IsOrderUnit E] in
/-- `w` turns `ℝ≥0`-scaling of the cone into real multiplication, unconditionally (no finiteness
needed: `ENNReal.toReal_mul` holds regardless). -/
lemma toReal_map_nnreal_smul (w : Weight E) (k : ℝ≥0) (c : PosCone E) :
    (w (k • c)).toReal = k * (w c).toReal := by
  rw [w.map_smul, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

variable {w : Weight E}

namespace IsFinite

/-! ## B. Shift independence -/

/-- `x` shifted into the cone by `r` copies of the order unit, minus the corresponding multiple
of the weight of the order unit. -/
noncomputable def rawValue (_hw : w.IsFinite) (x : E) (r : ℝ) (h : 0 ≤ r • (1 : E) + x) : ℝ :=
  (w ⟨r • (1 : E) + x, h⟩).toReal - r * (w Weight.unit).toReal

lemma rawValue_of_le (hw : w.IsFinite) (x : E) {r s : ℝ} (hr : 0 ≤ r • (1 : E) + x)
    (hs : 0 ≤ s • (1 : E) + x) (hrs : r ≤ s) : rawValue hw x s hs = rawValue hw x r hr := by
  set t : ℝ≥0 := (s - r).toNNReal with ht_def
  have ht : (t : ℝ) = s - r := Real.coe_toNNReal _ (by linarith)
  have hcone : (⟨s • (1 : E) + x, hs⟩ : PosCone E) = ⟨r • (1 : E) + x, hr⟩ + t • Weight.unit := by
    apply Subtype.ext
    show s • (1 : E) + x = (r • (1 : E) + x) + (t : ℝ) • (1 : E)
    rw [ht]
    module
  unfold rawValue
  rw [hcone, hw.toReal_map_add, w.toReal_map_nnreal_smul, ht]
  ring

/-- The shifted value of a finite weight does not depend on the chosen shift. -/
lemma rawValue_indep (hw : w.IsFinite) (x : E) {r s : ℝ} (hr : 0 ≤ r • (1 : E) + x)
    (hs : 0 ≤ s • (1 : E) + x) : rawValue hw x r hr = rawValue hw x s hs := by
  rcases le_total r s with hrs | hrs
  · exact (rawValue_of_le hw x hr hs hrs).symm
  · exact rawValue_of_le hw x hs hr hrs

open Classical in
/-- The linear extension of a finite weight from the positive cone to all of `E`. -/
noncomputable def toFun (hw : w.IsFinite) (x : E) : ℝ :=
  rawValue hw x (exists_real_shift_nonneg x).choose (exists_real_shift_nonneg x).choose_spec

lemma toFun_eq (hw : w.IsFinite) (x : E) {r : ℝ} (h : 0 ≤ r • (1 : E) + x) :
    toFun hw x = rawValue hw x r h :=
  rawValue_indep hw x _ h

/-! ## C. The additive extension -/

@[simp]
lemma toFun_of_nonneg (hw : w.IsFinite) (x : PosCone E) : toFun hw (x : E) = (w x).toReal := by
  have h0 : (0 : E) ≤ (0 : ℝ) • (1 : E) + (x : E) := by simpa using x.2
  rw [toFun_eq hw (x : E) h0, rawValue]
  simp

lemma toFun_zero (hw : w.IsFinite) : toFun hw (0 : E) = 0 := by
  have h := toFun_of_nonneg hw (0 : PosCone E)
  simpa using h

lemma toFun_add (hw : w.IsFinite) (x y : E) : toFun hw (x + y) = toFun hw x + toFun hw y := by
  obtain ⟨r, hr⟩ := exists_real_shift_nonneg x
  obtain ⟨s, hs⟩ := exists_real_shift_nonneg y
  have hrs : (0 : E) ≤ (r + s) • (1 : E) + (x + y) := by
    have heq : (r + s) • (1 : E) + (x + y) = (r • (1 : E) + x) + (s • (1 : E) + y) := by module
    rw [heq]; exact add_nonneg hr hs
  rw [toFun_eq hw x hr, toFun_eq hw y hs, toFun_eq hw (x + y) hrs]
  have hcone : (⟨(r + s) • (1 : E) + (x + y), hrs⟩ : PosCone E) =
      ⟨r • (1 : E) + x, hr⟩ + ⟨s • (1 : E) + y, hs⟩ := by
    apply Subtype.ext
    show (r + s) • (1 : E) + (x + y) = (r • (1 : E) + x) + (s • (1 : E) + y)
    module
  unfold rawValue
  rw [hcone, hw.toReal_map_add]
  ring

lemma toFun_neg (hw : w.IsFinite) (x : E) : toFun hw (-x) = -toFun hw x := by
  have h := toFun_add hw x (-x)
  rw [add_neg_cancel, toFun_zero] at h
  linarith

/-- Nonnegative real homogeneity of the finite-weight extension. -/
lemma toFun_real_nonneg_smul (hw : w.IsFinite) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    toFun hw (t • x) = t * toFun hw x := by
  obtain ⟨r, hr⟩ := exists_real_shift_nonneg x
  have hcr : (0 : E) ≤ (t * r) • (1 : E) + t • x := by
    have heq : (t * r) • (1 : E) + t • x = t • (r • (1 : E) + x) := by module
    rw [heq]; exact smul_nonneg ht hr
  rw [toFun_eq hw x hr, toFun_eq hw (t • x) hcr]
  have hcone : (⟨(t * r) • (1 : E) + t • x, hcr⟩ : PosCone E) =
      t.toNNReal • (⟨r • (1 : E) + x, hr⟩ : PosCone E) := by
    apply Subtype.ext
    show (t * r) • (1 : E) + t • x = (t.toNNReal : ℝ) • (r • (1 : E) + x)
    rw [Real.coe_toNNReal t ht]
    module
  unfold rawValue
  rw [hcone, w.toReal_map_nnreal_smul, Real.coe_toNNReal t ht]
  ring

/-- Full real homogeneity of the finite-weight extension. -/
lemma toFun_smul (hw : w.IsFinite) (t : ℝ) (x : E) : toFun hw (t • x) = t * toFun hw x := by
  rcases le_total (0 : ℝ) t with ht | ht
  · exact toFun_real_nonneg_smul hw ht x
  · have h1 : t • x = -((-t) • x) := by rw [neg_smul, neg_neg]
    rw [h1, toFun_neg, toFun_real_nonneg_smul hw (neg_nonneg.mpr ht) x]
    ring

/-! ## D. The positive linear extension -/

/-- The `ℝ`-linear map extending a finite weight. -/
noncomputable def toLinearMap (hw : w.IsFinite) : E →ₗ[ℝ] ℝ where
  toFun := toFun hw
  map_add' := toFun_add hw
  map_smul' := toFun_smul hw

@[simp]
lemma toLinearMap_apply (hw : w.IsFinite) (x : E) : toLinearMap hw x = toFun hw x := rfl

/-- The positive linear functional extending a finite weight. -/
noncomputable def toPositiveLinearMap (hw : w.IsFinite) : E →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (toLinearMap hw) fun x hx => by
    rw [toLinearMap_apply, toFun_of_nonneg hw ⟨x, hx⟩]
    exact ENNReal.toReal_nonneg

end IsFinite

end Weight
