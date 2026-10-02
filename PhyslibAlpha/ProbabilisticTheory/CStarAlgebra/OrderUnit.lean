/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Algebra.Star.SelfAdjoint

/-!

# The observables of a C⋆-algebra

## i. Overview

The self-adjoint elements of a unital C⋆-algebra form an Archimedean order-unit space with unit `1`.
Every self-adjoint `a` lies below `‖a‖ • 1`, and the positive cone is closed.

## ii. Key results

- `selfAdjoint.instIsOrderUnit` : the order-unit space of observables.
- `selfAdjoint.instIsArchimedeanOrderUnit` : it is Archimedean.

-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace selfAdjoint
open ProbabilisticTheory

/-- Nonnegative real scalars preserve the order on self-adjoint elements: scaling by a
nonnegative real is the same as multiplying by a nonnegative (central) algebra element, and a
nonnegative element times a nonnegative element that commutes with it stays nonnegative. -/
instance instPosSMulMono : PosSMulMono ℝ (selfAdjoint A) where
  smul_le_smul_of_nonneg_left c hc a b hab := by
    show (c : ℝ) • (a : A) ≤ (c : ℝ) • (b : A)
    have hab' : (a : A) ≤ (b : A) := hab
    gcongr

noncomputable instance instIsOrderUnit : OrderUnitSpace (selfAdjoint A) where
  one_nonneg := by
    show (0 : A) ≤ (1 : A)
    exact zero_le_one
  exists_nsmul_one_le x := by
    refine ⟨⌈‖(x : A)‖⌉₊, ?_⟩
    have hcast : ((⌈‖(x : A)‖⌉₊ • (1 : selfAdjoint A) : selfAdjoint A) : A) =
        (⌈‖(x : A)‖⌉₊ : ℝ) • (1 : A) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      rfl
    show (x : A) ≤ ((⌈‖(x : A)‖⌉₊ • (1 : selfAdjoint A) : selfAdjoint A) : A)
    rw [hcast]
    calc (x : A) ≤ algebraMap ℝ A ‖(x : A)‖ := x.2.le_algebraMap_norm_self
      _ = ‖(x : A)‖ • (1 : A) := Algebra.algebraMap_eq_smul_one _
      _ ≤ (⌈‖(x : A)‖⌉₊ : ℝ) • (1 : A) := by gcongr; exact Nat.le_ceil _

noncomputable instance instIsArchimedeanOrderUnit : ArchimedeanOrderUnitSpace (selfAdjoint A) where
  le_zero_of_forall_pos_smul_one_le x h := by
    show (x : A) ≤ (0 : A)
    have hg : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • (1 : A)) Filter.atTop
        (nhds 0) := by
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h0.smul_const (1 : A)
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hg fun n => ?_
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hle : x ≤ (1 / ((n : ℝ) + 1)) • (1 : selfAdjoint A) := h (1 / ((n : ℝ) + 1)) hε
    have hcast : (((1 / ((n : ℝ) + 1)) • (1 : selfAdjoint A) : selfAdjoint A) : A) =
        (1 / ((n : ℝ) + 1)) • (1 : A) := rfl
    have hle' : (x : A) ≤ (((1 / ((n : ℝ) + 1)) • (1 : selfAdjoint A) : selfAdjoint A) : A) :=
      Subtype.coe_le_coe.mpr hle
    rwa [hcast] at hle'

end selfAdjoint

