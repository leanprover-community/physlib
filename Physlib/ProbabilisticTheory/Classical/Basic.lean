/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import Physlib.ProbabilisticTheory.StarAlgebra.State

/-!
# Bounded classical observables

Classical observables are functions on a configuration space. Their bounded real-valued functions
form an Archimedean order-unit space.

## i. Overview

A classical system has a space `X` of possible configurations. Physical quantities such as
position, energy or magnetization are functions on this space. A choice of function algebra
specifies the admitted observables. One may require continuity, measurability or smoothness.

A star subalgebra `S` of the complex-valued functions on `X` is such a choice. Its self-adjoint
elements are its real-valued functions. These are the observables of `S`. Unlike quantum
observables they commute. Their order is pointwise.

The constant function `1` is an order unit when every function in `S` is bounded. The observables
then form an Archimedean order-unit space. Its order-unit norm is the supremum norm. It is the
supremum of `‖f x‖` over all configurations `x`. So classical function algebras fit the same
order-unit framework as quantum systems.

## ii. Key results

- `ProbabilisticTheory.Classical.bounded` : the star algebra of bounded functions.
- `ProbabilisticTheory.Classical.IsBounded` : a star subalgebra of bounded functions.
- `ProbabilisticTheory.Classical.star_apply` : classical observables are real-valued.
- `ProbabilisticTheory.Classical.instArchimedeanOrderUnitSpace` : bounded classical observables
  form an Archimedean order-unit space.
- `ProbabilisticTheory.Classical.orderUnitNorm_eq_iSup` : the order-unit norm is the supremum norm.

## iii. Table of contents

- A. Bounded function algebras
- B. Classical observables
- C. Order-unit structure

## iv. References

* None.

-/

@[expose] public section

open scoped ComplexOrder

namespace ProbabilisticTheory

open ArchimedeanOrderUnitSpace

namespace Classical

variable {X : Type*} {S : StarSubalgebra ℂ (X → ℂ)}

/-! ## A. Bounded function algebras -/

/-- The star subalgebra of bounded complex-valued functions on `X`. -/
noncomputable def bounded (X : Type*) : StarSubalgebra ℂ (X → ℂ) where
  __ := Filter.boundedFilterSubalgebra ℂ ⊤
  star_mem' {f} hf := by
    have h : Filter.BoundedAtFilter ⊤ f := hf
    change Filter.BoundedAtFilter ⊤ (star f)
    unfold Filter.BoundedAtFilter at h ⊢
    rw [← Asymptotics.isBigO_norm_left] at h ⊢
    simpa only [Pi.star_apply, norm_star] using h

/-- A function is bounded exactly when its absolute values have a uniform upper bound. -/
lemma mem_bounded_iff {f : X → ℂ} : f ∈ bounded X ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by
  change Filter.BoundedAtFilter ⊤ f ↔ _
  rw [Filter.BoundedAtFilter, Asymptotics.isBigO_top]
  simp

/-- A star subalgebra of bounded functions. Its observables form an order-unit space. -/
class IsBounded (S : StarSubalgebra ℂ (X → ℂ)) : Prop where
  /-- Every admissible function is bounded. -/
  le_bounded : S ≤ bounded X

instance : IsBounded (bounded X) := ⟨le_rfl⟩

/-! ## B. Classical observables -/

/-- Observables are real-valued. Complex conjugation fixes their values. -/
lemma star_apply (f : Observable S) (x : X) :
    star (((f : S) : X → ℂ) x) = ((f : S) : X → ℂ) x :=
  congrFun (congrArg Subtype.val f.2) x

/-- The order on classical observables is pointwise. -/
lemma le_iff_apply_le {f g : Observable S} :
    f ≤ g ↔ ∀ x, ((f : S) : X → ℂ) x ≤ ((g : S) : X → ℂ) x := by
  rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe, Pi.le_def]

/-- A scalar multiple of the unit is a constant function. -/
lemma smul_one_apply (r : ℝ) (x : X) : (((r • 1 : Observable S) : S) : X → ℂ) x = r := by
  simp

/-- Multiplication by nonnegative scalars preserves the order. -/
instance instPosSMulMono : PosSMulMono ℝ (Observable S) where
  smul_le_smul_of_nonneg_left r hr f g hfg := by
    rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe] at hfg ⊢
    change r • ((f : S) : X → ℂ) ≤ r • ((g : S) : X → ℂ)
    exact smul_le_smul_of_nonneg_left hfg hr

/-- Order bounds by the unit are uniform bounds on the absolute values. -/
lemma mem_Icc_smul_one_iff {f : Observable S} {r : ℝ} :
    -(r • 1) ≤ f ∧ f ≤ r • 1 ↔ ∀ x, ‖((f : S) : X → ℂ) x‖ ≤ r := by
  rw [← neg_smul r (1 : Observable S), le_iff_apply_le, le_iff_apply_le, ← forall_and]
  refine forall_congr' ?_
  intro x
  obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.mp (star_apply f x)
  rw [smul_one_apply, smul_one_apply, ht, Complex.real_le_real, Complex.real_le_real,
    Complex.norm_real, Real.norm_eq_abs, abs_le]

/-! ## C. Order-unit structure -/

/-- Bounded classical observables form an order-unit space. -/
noncomputable instance instOrderUnitSpace [IsBounded S] : OrderUnitSpace (Observable S) where
  one_nonneg := zero_le_one (α := X → ℂ)
  exists_nsmul_one_le f := by
    obtain ⟨C, hC⟩ := mem_bounded_iff.mp (IsBounded.le_bounded (f : S).2)
    refine ⟨⌈C⌉₊, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    exact (mem_Icc_smul_one_iff.mpr fun x ↦ (hC x).trans (Nat.le_ceil C)).2

/-- Bounded classical observables form an Archimedean order-unit space. -/
noncomputable instance instArchimedeanOrderUnitSpace [IsBounded S] :
    ArchimedeanOrderUnitSpace (Observable S) where
  le_zero_of_forall_pos_smul_one_le f hf := by
    refine le_iff_apply_le.mpr ?_
    intro x
    obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.mp (star_apply f x)
    have h : t ≤ 0 := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hx := le_iff_apply_le.mp (hf ε hε) x
      rw [zero_add]
      rwa [smul_one_apply, ht, Complex.real_le_real] at hx
    simp only [ht, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact_mod_cast h

/-- The order-unit norm is at most `r` exactly when every value is at most `r` in absolute value. -/
lemma orderUnitNorm_le_iff_norm_le [IsBounded S] {f : Observable S} {r : ℝ} (hr : 0 ≤ r) :
    orderUnitNorm f ≤ r ↔ ∀ x, ‖((f : S) : X → ℂ) x‖ ≤ r := by
  rw [orderUnitNorm_le_iff, ← mem_Icc_smul_one_iff]
  exact and_iff_right hr

/-- The order-unit norm is the supremum norm. It is the supremum of `‖f x‖` over all
configurations `x`. -/
lemma orderUnitNorm_eq_iSup [IsBounded S] (f : Observable S) :
    orderUnitNorm f = ⨆ x, ‖((f : S) : X → ℂ) x‖ := by
  have h := (orderUnitNorm_le_iff_norm_le (orderUnitNorm_nonneg f)).mp le_rfl
  refine le_antisymm ?_ (Real.iSup_le h (orderUnitNorm_nonneg f))
  refine (orderUnitNorm_le_iff_norm_le (Real.iSup_nonneg fun _ ↦ norm_nonneg _)).mpr ?_
  intro x
  exact le_ciSup ⟨orderUnitNorm f, Set.forall_mem_range.mpr h⟩ x

/-- A self-adjoint function of a bounded subalgebra is a difference of nonnegative functions. -/
instance instSelfAdjointDecompose [IsBounded S] : SelfAdjointDecompose S where
  exists_nonneg_sub_nonneg {a} ha := by
    obtain ⟨b, c, hb, hc, h⟩ := OrderUnitSpace.exists_eq_sub_nonneg (⟨a, ha⟩ : Observable S)
    exact ⟨b, c, hb, hc, congrArg Subtype.val h⟩

end Classical

end ProbabilisticTheory
