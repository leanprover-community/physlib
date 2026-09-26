/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Weight.Basic

/-!
# Extending finite weights

## i. Overview

A finite weight on the positive cone of an order-unit space extends uniquely to a positive linear
functional on the whole space. Since `1` is an order unit, any `A : E` becomes nonnegative after
adding enough copies of `1`, so we set `toFun A := w (r • 1 + A) - r * w 1` for such an `r`, and
check the result does not depend on the `r` chosen.

## ii. Key results

- `Weight.IsFinite.toLinearMap` : the `ℝ`-linear map extending a finite weight to all of `E`.

## iii. Table of contents

- A. The raw shifted value
- B. The linear extension

-/

@[expose] public section

open scoped ENNReal NNReal

variable {E : Type*} [OrderUnitSpace E]

namespace Weight

variable {w : Weight E}

namespace IsFinite

/-!

## A. The raw shifted value

-/

/-- `A` shifted into the cone by `r` copies of the order unit, minus the corresponding multiple
of the weight of the order unit. -/
noncomputable def rawValue (w : Weight E) (A : E) (r : ℝ) (h : 0 ≤ r • (1 : E) + A) : ℝ :=
  (w ⟨r • (1 : E) + A, h⟩).toReal - r * (w 1).toReal

/-- Shifting by a larger `s` gives the same value as shifting by `r`. -/
lemma rawValue_of_le (hw : w.IsFinite) (A : E) {r s : ℝ} (hr : 0 ≤ r • (1 : E) + A)
    (hs : 0 ≤ s • (1 : E) + A) (hrs : r ≤ s) : rawValue w A s hs = rawValue w A r hr := by
  set t : ℝ≥0 := (s - r).toNNReal
  have ht : (t : ℝ) = s - r := Real.coe_toNNReal _ (by linarith)
  have hcone : (⟨s • (1 : E) + A, hs⟩ : PosCone E) =
      ⟨r • (1 : E) + A, hr⟩ + t • (1 : PosCone E) := by
    apply Subtype.ext
    show s • (1 : E) + A = (r • (1 : E) + A) + (t : ℝ) • (1 : E)
    rw [ht]
    module
  unfold rawValue
  rw [hcone, hw.toReal_map_add, w.toReal_map_nnreal_smul, ht]
  ring

/-- The shifted value of a finite weight does not depend on the chosen shift. -/
lemma rawValue_indep (hw : w.IsFinite) (A : E) {r s : ℝ} (hr : 0 ≤ r • (1 : E) + A)
    (hs : 0 ≤ s • (1 : E) + A) : rawValue w A r hr = rawValue w A s hs :=
  (le_total r s).elim (fun h => (rawValue_of_le hw A hr hs h).symm) (rawValue_of_le hw A hs hr)

/-!

## B. The linear extension

-/

open Classical in
/-- The linear extension of a finite weight from the positive cone to all of `E`. -/
noncomputable def toFun (w : Weight E) (A : E) : ℝ :=
  rawValue w A (OrderUnitSpace.exists_real_shift_nonneg A).choose
    (OrderUnitSpace.exists_real_shift_nonneg A).choose_spec

/-- The extension can be computed with any shift `r` making `r • 1 + A` nonnegative. -/
lemma toFun_eq (hw : w.IsFinite) (A : E) {r : ℝ} (h : 0 ≤ r • (1 : E) + A) :
    toFun w A = rawValue w A r h :=
  rawValue_indep hw A _ h

@[simp]
lemma toFun_of_nonneg (hw : w.IsFinite) (A : PosCone E) : toFun w (A : E) = (w A).toReal := by
  have h0 : (0 : E) ≤ (0 : ℝ) • (1 : E) + (A : E) := by
    rw [zero_smul, zero_add]; exact A.2
  rw [toFun_eq hw (A : E) h0, rawValue]
  simp

/-- The extension of a finite weight sends `0` to `0`. -/
lemma toFun_zero (hw : w.IsFinite) : toFun w (0 : E) = 0 := by
  simpa using toFun_of_nonneg hw (0 : PosCone E)

/-- The extension of a finite weight is additive. -/
lemma toFun_add (hw : w.IsFinite) (A B : E) : toFun w (A + B) = toFun w A + toFun w B := by
  obtain ⟨r, hr⟩ := OrderUnitSpace.exists_real_shift_nonneg A
  obtain ⟨s, hs⟩ := OrderUnitSpace.exists_real_shift_nonneg B
  have hrs : (0 : E) ≤ (r + s) • (1 : E) + (A + B) := by
    convert add_nonneg hr hs using 1; module
  rw [toFun_eq hw A hr, toFun_eq hw B hs, toFun_eq hw (A + B) hrs]
  have hcone : (⟨(r + s) • (1 : E) + (A + B), hrs⟩ : PosCone E) =
      ⟨r • (1 : E) + A, hr⟩ + ⟨s • (1 : E) + B, hs⟩ := by
    apply Subtype.ext
    show (r + s) • (1 : E) + (A + B) = (r • (1 : E) + A) + (s • (1 : E) + B)
    module
  unfold rawValue
  rw [hcone, hw.toReal_map_add]
  ring

/-- The extension of a finite weight is odd. -/
lemma toFun_neg (hw : w.IsFinite) (A : E) : toFun w (-A) = -toFun w A := by
  have h := toFun_add hw A (-A)
  rw [add_neg_cancel, toFun_zero hw] at h
  linarith

/-- Nonnegative real homogeneity of the finite-weight extension. -/
lemma toFun_real_nonneg_smul (hw : w.IsFinite) {t : ℝ} (ht : 0 ≤ t) (A : E) :
    toFun w (t • A) = t * toFun w A := by
  obtain ⟨r, hr⟩ := OrderUnitSpace.exists_real_shift_nonneg A
  have hcr : (0 : E) ≤ (t * r) • (1 : E) + t • A := by
    convert smul_nonneg ht hr using 1; module
  rw [toFun_eq hw A hr, toFun_eq hw (t • A) hcr]
  have hcone : (⟨(t * r) • (1 : E) + t • A, hcr⟩ : PosCone E) =
      t.toNNReal • (⟨r • (1 : E) + A, hr⟩ : PosCone E) := by
    apply Subtype.ext
    show (t * r) • (1 : E) + t • A = (t.toNNReal : ℝ) • (r • (1 : E) + A)
    rw [Real.coe_toNNReal t ht]
    module
  unfold rawValue
  rw [hcone, w.toReal_map_nnreal_smul, Real.coe_toNNReal t ht]
  ring

/-- Full real homogeneity of the finite-weight extension. -/
lemma toFun_smul (hw : w.IsFinite) (t : ℝ) (A : E) : toFun w (t • A) = t * toFun w A := by
  rcases le_total (0 : ℝ) t with ht | ht
  · exact toFun_real_nonneg_smul hw ht A
  · rw [← neg_neg t, neg_smul, toFun_neg hw, toFun_real_nonneg_smul hw (neg_nonneg.mpr ht)]
    ring

/-- The `ℝ`-linear map extending a finite weight. -/
noncomputable def toLinearMap (hw : w.IsFinite) : E →ₗ[ℝ] ℝ where
  toFun := toFun w
  map_add' := toFun_add hw
  map_smul' := toFun_smul hw

/-- The linear extension agrees with `toFun` by construction. -/
@[simp]
lemma toLinearMap_apply (hw : w.IsFinite) (A : E) : toLinearMap hw A = toFun w A := rfl

end IsFinite

end Weight
