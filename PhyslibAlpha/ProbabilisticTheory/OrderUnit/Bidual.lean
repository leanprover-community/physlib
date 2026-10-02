/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.PositiveDual.BidualLattice
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.Lattice

/-!
# The bidual of a system

## i. Overview

An element of the bidual of a system assigns to every positive functional a value, additively and
positively homogeneously, dominated by some observable. With the unit `φ ↦ φ 1`, the total weight,
the bidual is again an Archimedean order-unit space: a system whose observables contain those of
the original one. When the system is classical, so that the positive functionals form a lattice,
the observables of the bidual form a lattice.

## ii. Key results

- `Bidual.instOrderUnitSpace` : the bidual of a system, with the total weight as unit.
- `Bidual.instArchimedeanOrderUnitSpace` : the bidual is Archimedean.
- `Bidual.instOrderUnitLattice` : the bidual of a classical system is an order-unit lattice.

## iii. Table of contents

- A. The unit of the bidual
- B. The bidual of a classical system

-/

@[expose] public section

namespace Bidual
open ProbabilisticTheory

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. The unit of the bidual -/

/-- The unit of the bidual: the total weight of a positive functional. -/
instance : One (Bidual E) := ⟨ofE 1⟩

@[simp] lemma coe_one (φ : E →ₚ[ℝ] ℝ) : (1 : Bidual E) φ = φ 1 := rfl

@[simp] lemma ofE_one : ofE (1 : E) = 1 := rfl

/-- An element of the bidual is bounded by a multiple of the total weight. -/
lemma exists_bound_one (x : Bidual E) : ∃ n : ℕ, ∀ φ, |x φ| ≤ n * φ 1 := by
  obtain ⟨f, hf⟩ := x.exists_bound
  obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le f
  refine ⟨n, fun φ => (hf φ).trans ?_⟩
  have := OrderHomClass.mono φ hn
  rwa [map_nsmul, nsmul_eq_mul] at this

instance instOrderUnitSpace : OrderUnitSpace (Bidual E) where
  one_nonneg φ := map_nonneg φ OrderUnitSpace.one_nonneg
  exists_nsmul_one_le x := by
    obtain ⟨n, hn⟩ := x.exists_bound_one
    refine ⟨n, fun φ => ?_⟩
    change x φ ≤ ((n • (1 : Bidual E) : Bidual E) : (E →ₚ[ℝ] ℝ) → ℝ) φ
    rw [← Nat.cast_smul_eq_nsmul ℝ, coe_smul, coe_one]
    exact (le_abs_self _).trans (hn φ)

instance instArchimedeanOrderUnitSpace : ArchimedeanOrderUnitSpace (Bidual E) where
  le_zero_of_forall_pos_smul_one_le x h φ := le_of_forall_pos_le_add fun ε hε => by
    have h1 := map_nonneg φ OrderUnitSpace.one_nonneg
    have := h (ε / (φ 1 + 1)) (by positivity) φ
    simp only [coe_smul, coe_one, coe_zero] at this ⊢
    have : ε / (φ 1 + 1) * φ 1 ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith

/-- A positive functional's value on an element of the bidual below the unit is at most its total
weight. -/
lemma apply_le_of_le_one {x : Bidual E} (hx : x ≤ 1) (φ : E →ₚ[ℝ] ℝ) : x φ ≤ φ 1 :=
  hx φ

/-! ## B. The bidual of a classical system -/

/-- The bidual of a classical system is an order-unit lattice. -/
noncomputable instance instOrderUnitLattice [Fact (HasLatticeDualCone E)] :
    OrderUnitLattice (Bidual E) where

end Bidual

