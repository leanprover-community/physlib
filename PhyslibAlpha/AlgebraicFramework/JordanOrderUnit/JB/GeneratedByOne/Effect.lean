/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.JB.GeneratedByOne.CFC
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Basic

/-!
# Continuous functional-calculus effects

A continuous `[0,1]`-valued function of one intrinsic JB observable is an effect.  This is the
continuous precursor to the bounded Borel calculus of a spectral resolution: it packages the
order consequences of the intrinsic CFC without making the CFC core depend on effects.
-/

@[expose] public section

namespace NormedJordanAlgebra

variable {E : Type*} [NormedJordanAlgebra E] [JBAlgebra E]

/-- Apply the intrinsic continuous functional calculus to a continuous effect-valued function.
The lower and upper bounds are transported by `jordanCfc_nonneg` and `jordanCfc_monotone`; no
concrete realization is used. -/
noncomputable def jordanCfcEffect [Nontrivial E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [IsJBOrderUnit E] (a : E)
    (f : C(jordanSpectrum a, ℝ)) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : Effect E :=
  ⟨jordanCfc a f, jordanCfc_nonneg a f hf0, by
    have h := jordanCfc_monotone a (f := f)
      (g := ContinuousMap.const (jordanSpectrum a) 1) fun x => by simpa using hf1 x
    calc
      jordanCfc a f ≤ jordanCfc a (ContinuousMap.const (jordanSpectrum a) 1) := h
      _ = 1 := by simpa using (jordanCfc_const a 1)⟩

/-- Coercing the CFC effect forgets only its proved bounds. -/
@[simp]
theorem coe_jordanCfcEffect [Nontrivial E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [IsJBOrderUnit E] (a : E)
    (f : C(jordanSpectrum a, ℝ)) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (jordanCfcEffect a f hf0 hf1 : E) = jordanCfc a f :=
  rfl

end NormedJordanAlgebra
