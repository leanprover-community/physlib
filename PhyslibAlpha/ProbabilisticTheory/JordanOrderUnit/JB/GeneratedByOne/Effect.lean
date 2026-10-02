/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JB.GeneratedByOne.CFC
public import Physlib.ProbabilisticTheory.Effect.Sharp

/-!

# Effects from the functional calculus

## i. Overview

A continuous function of an observable with values in `[0, 1]` is an effect.

## ii. Key results

- `NormedJordanAlgebra.jordanCfcEffect` : the effect of a `[0, 1]`-valued function.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace NormedJordanAlgebra

variable {E : Type*}

section

variable [IsJBOrderUnit E]

/-- The effect `f(a)` of a continuous function `f` with values in `[0, 1]`. -/
noncomputable def jordanCfcEffect [Nontrivial E] (a : E)
    (f : C(jordanSpectrum a, ℝ)) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : Effect E :=
  ⟨jordanCfc a f, jordanCfc_nonneg a f hf0, by
    have h := jordanCfc_monotone a (f := f)
      (g := ContinuousMap.const (jordanSpectrum a) 1) fun x => by simpa using hf1 x
    calc
      jordanCfc a f ≤ jordanCfc a (ContinuousMap.const (jordanSpectrum a) 1) := h
      _ = 1 := by simpa using (jordanCfc_const a 1)⟩

/-- Coercing the CFC effect forgets only its proved bounds. -/
@[simp]
lemma coe_jordanCfcEffect [Nontrivial E] (a : E)
    (f : C(jordanSpectrum a, ℝ)) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (jordanCfcEffect a f hf0 hf1 : E) = jordanCfc a f :=
  rfl

end

end NormedJordanAlgebra

end ProbabilisticTheory
