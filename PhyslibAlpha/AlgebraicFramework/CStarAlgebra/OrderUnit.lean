/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Algebra.Star.SelfAdjoint

/-!

# The self-adjoint part of a C⋆-algebra is an order-unit space

`selfAdjoint A`, for a unital C⋆-algebra `A`, is the physically meaningful home for the whole
`OrderUnit`/`Effect`/`Weight`/`Channel`/`Measurement` framework built on top of it: the algebra `A`
itself is *not* an order-unit space in that sense, since `x ≤ n • 1` forces `x` self-adjoint
(`StarOrderedRing.le_iff`), so only the self-adjoint elements can ever be compared to `1` at all.

`1` bounds every self-adjoint element by `IsSelfAdjoint.le_algebraMap_norm_self`, giving
`IsOrderUnit`. Archimedeanity is the one genuinely analytic fact: if `x ≤ ε • 1` for every `ε > 0`,
then `x` is a limit of `ε • 1` as `ε → 0`, and `≤` is a closed relation
(`OrderClosedTopology`, itself from the norm-closedness of the nonnegative cone,
`isClosed_nonneg`), so the limit inequality `x ≤ 0` survives.

## Main definitions

- `selfAdjoint.instIsOrderUnit`, `selfAdjoint.instIsArchimedeanOrderUnit`

-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace selfAdjoint

/-- Nonnegative real scalars preserve the order on self-adjoint elements: scaling by a
nonnegative real is the same as multiplying by a nonnegative (central) algebra element, and a
nonnegative element times a nonnegative element that commutes with it stays nonnegative. -/
instance instPosSMulMono : PosSMulMono ℝ (selfAdjoint A) where
  smul_le_smul_of_nonneg_left c hc a b hab := by
    show (c : ℝ) • (a : A) ≤ (c : ℝ) • (b : A)
    have hab' : (a : A) ≤ (b : A) := hab
    gcongr

instance instIsOrderUnit : IsOrderUnit (selfAdjoint A) where
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

instance instIsArchimedeanOrderUnit : IsArchimedeanOrderUnit (selfAdjoint A) where
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
