/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Weight.Extension
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic

/-!

# States, independently of weights

## i. Overview

A state is, on its own terms, a normalized positive linear functional — `𝓢[ℝ, E]`, already fully
built in `State/Basic.lean`. It is not *defined* as a weight; `Weight.stateEquiv` is the genuine
theorem connecting the two independent notions, replacing what would otherwise be an inheritance
chain forcing every state-level fact through weight machinery.

## ii. Key definitions and results

- `Weight.IsState.toUnitalPositiveLinearMap` : a state weight, as a state.
- `UnitalPositiveLinearMap.toWeight` : a state, as a (finite, normalized) weight.
- `Weight.stateEquiv` : the equivalence between the two.

## iii. Table of contents

- A. From state weights to states
- B. From states to weights
- C. The equivalence

-/

@[expose] public section

open scoped ENNReal

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

namespace Weight

variable {w : Weight E}

namespace IsState

/-! ## A. From state weights to states -/

/-- The extension of a state weight is its finite-weight extension. -/
noncomputable abbrev toFun (hw : w.IsState) : E → ℝ := hw.finite.toFun

/-- The linear extension of a state weight is its finite-weight extension. -/
noncomputable abbrev toLinearMap (hw : w.IsState) : E →ₗ[ℝ] ℝ := hw.finite.toLinearMap

/-- A finite normalized weight extends to a state. -/
noncomputable def toUnitalPositiveLinearMap (hw : w.IsState) : 𝓢[ℝ, E] :=
  UnitalPositiveLinearMap.ofLinearMap (toLinearMap hw)
    (fun x hx => hw.finite.toPositiveLinearMap.map_nonneg hx)
    (calc
      toLinearMap hw (1 : E) = (w Weight.unit).toReal := by
        simpa [toLinearMap, toFun, Weight.unit] using hw.finite.toFun_of_nonneg Weight.unit
      _ = 1 := by rw [hw.normalized, ENNReal.toReal_one])

@[simp]
lemma toUnitalPositiveLinearMap_apply (hw : w.IsState) (x : E) :
    hw.toUnitalPositiveLinearMap x = hw.toFun x := rfl

end IsState

end Weight

namespace UnitalPositiveLinearMap

/-! ## B. From states to weights -/

/-- The weight induced by a state: `ENNReal.ofReal` applied to the state's values on the positive
cone, where they are automatically nonnegative — so this loses no information about `s` there
(`toReal_toWeight_apply`), even though `s` itself carries strictly more data (its values off the
cone). -/
noncomputable def toWeight (s : 𝓢[ℝ, E]) : Weight E where
  toFun x := ENNReal.ofReal (s (x : E))
  map_add' x y := by
    show ENNReal.ofReal (s ((x : E) + (y : E))) =
      ENNReal.ofReal (s (x : E)) + ENNReal.ofReal (s (y : E))
    rw [map_add, ENNReal.ofReal_add (s.map_nonneg x.2) (s.map_nonneg y.2)]
  map_smul' c x := by
    show ENNReal.ofReal (s ((c : ℝ) • (x : E))) = c • ENNReal.ofReal (s (x : E))
    have hcx : s ((c : ℝ) • (x : E)) = (c : ℝ) * s (x : E) := by rw [map_smul, smul_eq_mul]
    rw [hcx, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def,
      smul_eq_mul]

omit [IsOrderUnit E] in
@[simp]
lemma toWeight_apply (s : 𝓢[ℝ, E]) (x : PosCone E) : s.toWeight x = ENNReal.ofReal (s (x : E)) :=
  rfl

omit [IsOrderUnit E] in
/-- The weight induced by a state agrees with the state itself on the positive cone: no
information about `s` there is lost by passing through `ENNReal.ofReal` and back. -/
lemma toReal_toWeight_apply (s : 𝓢[ℝ, E]) (x : PosCone E) : (s.toWeight x).toReal = s (x : E) := by
  rw [toWeight_apply, ENNReal.toReal_ofReal (s.map_nonneg x.2)]

/-- The weight induced by a state is itself a state: finite (`ENNReal.ofReal` never reaches `⊤`)
and normalized (`s` sends the order unit to `1`). -/
lemma toWeight_isState (s : 𝓢[ℝ, E]) : s.toWeight.IsState where
  finite _ := ENNReal.ofReal_ne_top
  normalized := by
    have h1 : ((Weight.unit : PosCone E) : E) = 1 := rfl
    show ENNReal.ofReal (s ((Weight.unit : PosCone E) : E)) = 1
    rw [h1, map_one, ENNReal.ofReal_one]

end UnitalPositiveLinearMap

namespace Weight

/-! ## C. The equivalence -/

/-- Finite normalized weights correspond exactly to states. This is the representation theorem
that replaces bundling a state as a subtype of `Weight`: `Weight` and `𝓢[ℝ, E]` are independent
notions — one general and possibly infinite, the other linear and finite by definition — and this
equivalence is the (nontrivial, but genuinely separate) fact connecting them. -/
noncomputable def stateEquiv : {w : Weight E // w.IsState} ≃ 𝓢[ℝ, E] where
  toFun w := w.2.toUnitalPositiveLinearMap
  invFun s := ⟨s.toWeight, s.toWeight_isState⟩
  left_inv := by
    rintro ⟨w, hw⟩
    refine Subtype.ext (Weight.ext fun x => ?_)
    show ENNReal.ofReal (hw.toUnitalPositiveLinearMap (x : E)) = w x
    simp [hw.toUnitalPositiveLinearMap_apply, ENNReal.ofReal_toReal (hw.finite x)]
  right_inv := by
    intro s
    refine UnitalPositiveLinearMap.ext fun x => ?_
    obtain ⟨r, hr⟩ := exists_real_shift_nonneg x
    set hw := s.toWeight_isState
    show hw.finite.toFun x = s x
    rw [hw.finite.toFun_eq x hr, IsFinite.rawValue]
    simp only [UnitalPositiveLinearMap.toReal_toWeight_apply,
      show ((Weight.unit : PosCone E) : E) = 1 from rfl, _root_.map_add, _root_.map_smul,
      smul_eq_mul, _root_.map_one]
    ring

end Weight
