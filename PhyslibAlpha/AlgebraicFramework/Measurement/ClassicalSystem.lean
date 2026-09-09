/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Pi

/-!

# The classical system with finitely many outcomes

For a finite outcome type `ι`, `ι → ℝ` is the order-unit space of a classical system that can show
one of the outcomes in `ι`: the order is pointwise, and the order unit `1` is the function
constantly `1`, i.e. the "certain event". This is the domain a finite-outcome measurement is a
channel *from*, in the sense of `Measurement` (`FiniteOutcome.lean`): an outcome `i` corresponds to
the indicator function `Pi.single i 1`, and a positive unital map out of `ι → ℝ` is exactly a
choice of effect for each outcome, summing to the certain event.

Everything but `IsOrderUnit`/`IsArchimedeanOrderUnit` is already provided by the generic `Pi`
instances for an ordered `ℝ`-vector space; what is special to a *finite* index type is that `1` is
already the biggest thing around, since a finite set of reals is bounded.

## Main definitions

- `Pi.instIsOrderUnit`, `Pi.instIsArchimedeanOrderUnit` : instances for `ι → ℝ` with `ι` finite.

-/

@[expose] public section

variable {ι : Type*} [Fintype ι]

namespace Pi

instance instIsOrderUnit : IsOrderUnit (ι → ℝ) where
  one_nonneg := fun _ => zero_le_one
  exists_nsmul_one_le x := by
    classical
    refine ⟨Finset.univ.sup fun i => ⌈x i⌉₊, fun i => ?_⟩
    have h : x i ≤ (Finset.univ.sup fun i => ⌈x i⌉₊ : ℕ) :=
      (Nat.le_ceil (x i)).trans
        (Nat.cast_le.mpr (Finset.le_sup (f := fun i => ⌈x i⌉₊) (Finset.mem_univ i)))
    simpa using h

instance instIsArchimedeanOrderUnit : IsArchimedeanOrderUnit (ι → ℝ) where
  le_zero_of_forall_pos_smul_one_le x h i := by
    show x i ≤ (0 : ℝ)
    by_contra hlt
    push Not at hlt
    have hx := h (x i / 2) (by linarith) i
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hx
    linarith

end Pi
