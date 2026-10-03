/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.PositiveDual.Bidual
public import PhyslibAlpha.Mathematics.Order.PositiveDual.Interpolation

/-!
# The bidual as a lattice

Least upper bounds in the bidual by the Riesz–Kantorovich formula; the bidual is a lattice.

## i. Overview

When the positive functionals on `E` form a lattice, any two elements `x` and `y` of the bidual have
a least upper bound. Its value on a positive functional `φ` is the best split of `φ` between `x`
and `y`: the supremum of `x φ₁ + y φ₂` over `φ = φ₁ + φ₂`. This is the Riesz–Kantorovich formula
with the roles of elements and functionals exchanged. The bidual then is a lattice.

## ii. Key results

- `Bidual.dsup` : the least upper bound of two elements of the bidual.
- `Bidual.isLUB_dsup` : it is the least upper bound.
- `Bidual.instLattice` : when the positive functionals form a lattice, the bidual is a lattice.

## iii. Table of contents

- A. Best splits of a positive functional
- B. The least upper bound
- C. The lattice structure

## iv. References

* None.

-/

@[expose] public section

open scoped NNReal

namespace Bidual

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [IsDirectedOrder E]

/-! ## A. Best splits of a positive functional -/

/-- The values `x φ₁ + y φ₂` over the splittings `φ = φ₁ + φ₂`. -/
def splitValues (x y : Bidual E) (φ : E →ₚ[ℝ] ℝ) : Set ℝ :=
  {r | ∃ φ₁ φ₂ : E →ₚ[ℝ] ℝ, φ₁ + φ₂ = φ ∧ r = x φ₁ + y φ₂}

omit [IsDirectedOrder E] in
lemma splitValues_nonempty (x y : Bidual E) (φ : E →ₚ[ℝ] ℝ) : (splitValues x y φ).Nonempty :=
  ⟨_, φ, 0, add_zero φ, rfl⟩

omit [IsDirectedOrder E] in
/-- A split of `φ` evaluates to at most `φ (f + g)` when `f` dominates `x` and `g` dominates `y`. -/
lemma add_le_of_bound {x y : Bidual E} {f g : E} (hf : ∀ φ, |x φ| ≤ φ f) (hg : ∀ φ, |y φ| ≤ φ g)
    {φ φ₁ φ₂ : E →ₚ[ℝ] ℝ} (h : φ₁ + φ₂ = φ) : x φ₁ + y φ₂ ≤ φ (f + g) := by
  have h₁ := (abs_le.1 (hf φ₁)).2
  have h₂ := (abs_le.1 (hg φ₂)).2
  have e₁ := apply_nonneg_of_bound hg φ₁
  have e₂ := apply_nonneg_of_bound hf φ₂
  rw [← h, add_apply, _root_.map_add, _root_.map_add]
  linarith

omit [IsDirectedOrder E] in
lemma bddAbove_splitValues (x y : Bidual E) (φ : E →ₚ[ℝ] ℝ) : BddAbove (splitValues x y φ) := by
  obtain ⟨f, hf⟩ := x.exists_bound
  obtain ⟨g, hg⟩ := y.exists_bound
  exact ⟨φ (f + g), fun _ ⟨φ₁, φ₂, h, e⟩ => e ▸ add_le_of_bound hf hg h⟩

/-- The best split of `φ` between `x` and `y`. -/
noncomputable def dsupFun (x y : Bidual E) (φ : E →ₚ[ℝ] ℝ) : ℝ := sSup (splitValues x y φ)

omit [IsDirectedOrder E] in
lemma le_dsupFun {x y : Bidual E} {φ φ₁ φ₂ : E →ₚ[ℝ] ℝ} (h : φ₁ + φ₂ = φ) :
    x φ₁ + y φ₂ ≤ dsupFun x y φ :=
  le_csSup (bddAbove_splitValues x y φ) ⟨φ₁, φ₂, h, rfl⟩

omit [IsDirectedOrder E] in
lemma dsupFun_le {x y : Bidual E} {φ : E →ₚ[ℝ] ℝ} {r : ℝ}
    (h : ∀ φ₁ φ₂ : E →ₚ[ℝ] ℝ, φ₁ + φ₂ = φ → x φ₁ + y φ₂ ≤ r) : dsupFun x y φ ≤ r :=
  csSup_le (splitValues_nonempty x y φ) fun _ ⟨φ₁, φ₂, hφ, hr⟩ => hr ▸ h φ₁ φ₂ hφ

omit [IsDirectedOrder E] in
lemma dsupFun_add_le (x y : Bidual E) (φ ψ : E →ₚ[ℝ] ℝ) :
    dsupFun x y φ + dsupFun x y ψ ≤ dsupFun x y (φ + ψ) := by
  have h₁ : ∀ r ∈ splitValues x y ψ, dsupFun x y (φ + ψ) - r ≥ dsupFun x y φ := by
    rintro _ ⟨ψ₁, ψ₂, hψ, rfl⟩
    show dsupFun x y φ ≤ _
    refine dsupFun_le fun φ₁ φ₂ hφ => ?_
    have := le_dsupFun (x := x) (y := y) (φ := φ + ψ) (φ₁ := φ₁ + ψ₁) (φ₂ := φ₂ + ψ₂)
      (by rw [← hφ, ← hψ]; abel)
    rw [x.map_add, y.map_add] at this
    linarith
  have h₂ : dsupFun x y (φ + ψ) - dsupFun x y φ ≥ dsupFun x y ψ :=
    csSup_le (splitValues_nonempty x y ψ) fun r hr => by linarith [h₁ r hr]
  linarith

variable (hE : HasLatticeDualCone E)
include hE

lemma dsupFun_add (x y : Bidual E) (φ ψ : E →ₚ[ℝ] ℝ) :
    dsupFun x y (φ + ψ) = dsupFun x y φ + dsupFun x y ψ := by
  refine le_antisymm (dsupFun_le fun χ₁ χ₂ hχ => ?_) (dsupFun_add_le x y φ ψ)
  obtain ⟨τ, hτ₁, hτ₂⟩ := hE.exists_table ![χ₁, χ₂] ![φ, ψ] (by simpa using hχ)
  have r₀ := hτ₁ 0; have r₁ := hτ₁ 1; have c₀ := hτ₂ 0; have c₁ := hτ₂ 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at r₀ r₁ c₀ c₁
  have := add_le_add (le_dsupFun (x := x) (y := y) c₀) (le_dsupFun (x := x) (y := y) c₁)
  rw [← r₀, ← r₁, x.map_add, y.map_add]
  linarith

omit hE in
lemma dsupFun_zero (x y : Bidual E) : dsupFun x y 0 = 0 := by
  refine le_antisymm (dsupFun_le fun φ₁ φ₂ h => ?_) ?_
  · obtain rfl := PositiveLinearMap.eq_zero_of_add_eq_zero h
    obtain rfl : φ₂ = 0 := PositiveLinearMap.eq_zero_of_add_eq_zero ((add_comm φ₂ _).trans h)
    simp [x.map_zero, y.map_zero]
  · simpa [x.map_zero, y.map_zero] using le_dsupFun (x := x) (y := y) (add_zero (0 : E →ₚ[ℝ] ℝ))

omit hE in
lemma dsupFun_nnsmul (x y : Bidual E) (c : ℝ≥0) (φ : E →ₚ[ℝ] ℝ) :
    dsupFun x y (c • φ) = c * dsupFun x y φ := by
  rcases eq_or_ne c 0 with rfl | hc
  · have : (0 : ℝ≥0) • φ = 0 := PositiveLinearMap.ext fun _ => by simp
    rw [this, dsupFun_zero]; simp
  have hc' : (0 : ℝ) < c := by positivity
  have hinv (ψ : E →ₚ[ℝ] ℝ) : c⁻¹ • c • ψ = ψ := PositiveLinearMap.ext fun _ => by
    simp [← mul_assoc, inv_mul_cancel₀ hc'.ne']
  have hsplit {φ₁ φ₂ ψ : E →ₚ[ℝ] ℝ} (h : φ₁ + φ₂ = ψ) (d : ℝ≥0) : d • φ₁ + d • φ₂ = d • ψ :=
    PositiveLinearMap.ext fun a => by simp [← h, mul_add]
  refine le_antisymm (dsupFun_le fun φ₁ φ₂ h => ?_) ?_
  · have := le_dsupFun (x := x) (y := y) (hsplit h c⁻¹)
    rw [hinv, x.map_nnsmul, y.map_nnsmul] at this
    have h2 := mul_le_mul_of_nonneg_left this hc'.le
    rw [mul_add, ← mul_assoc, ← mul_assoc, NNReal.coe_inv, mul_inv_cancel₀ hc'.ne', one_mul,
      one_mul] at h2
    exact h2
  · rw [← le_div_iff₀' hc']
    refine dsupFun_le fun φ₁ φ₂ h => ?_
    rw [le_div_iff₀' hc']
    have := le_dsupFun (x := x) (y := y) (hsplit h c)
    rwa [x.map_nnsmul, y.map_nnsmul, ← mul_add] at this

/-! ## B. The least upper bound -/

/-- The least upper bound of two elements of the bidual: the best split of each positive
functional. -/
noncomputable def dsup (x y : Bidual E) : Bidual E :=
  mk (dsupFun x y) (dsupFun_add hE x y) (dsupFun_nnsmul x y) (by
    obtain ⟨f, hf⟩ := x.exists_bound
    obtain ⟨g, hg⟩ := y.exists_bound
    refine ⟨f + g, fun φ => abs_le.2 ⟨?_, dsupFun_le fun φ₁ φ₂ h => add_le_of_bound hf hg h⟩⟩
    have := le_dsupFun (x := x) (y := y) (add_zero φ)
    have h₁ := (abs_le.1 (hf φ)).1
    have h₀ := apply_nonneg_of_bound hg φ
    simp only [y.map_zero, add_zero] at this
    rw [_root_.map_add]
    linarith)

lemma dsup_apply (x y : Bidual E) (φ : E →ₚ[ℝ] ℝ) : dsup hE x y φ = dsupFun x y φ := rfl

/-- The best split is the least upper bound. -/
lemma isLUB_dsup (x y : Bidual E) : IsLUB {x, y} (dsup hE x y) := by
  refine ⟨?_, fun u hu φ => dsupFun_le fun φ₁ φ₂ h => ?_⟩
  · intro z hz φ
    rcases hz with hz | hz
    · rw [hz]
      show x φ ≤ dsupFun x y φ
      simpa [y.map_zero] using le_dsupFun (x := x) (y := y) (add_zero φ)
    · rw [Set.mem_singleton_iff.1 hz]
      show y φ ≤ dsupFun x y φ
      simpa [x.map_zero] using le_dsupFun (x := x) (y := y) (zero_add φ)
  · show x φ₁ + y φ₂ ≤ u φ
    rw [← h, u.map_add]
    exact add_le_add (hu (Set.mem_insert _ _) φ₁) (hu (Set.mem_insert_of_mem _ rfl) φ₂)

end Bidual

/-! ## C. The lattice structure -/

namespace Bidual

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [IsDirectedOrder E] [hE : Fact (HasLatticeDualCone E)]

/-- When the positive functionals form a lattice, the bidual is a lattice. -/
noncomputable instance instLattice : Lattice (Bidual E) where
  sup := dsup hE.out
  le_sup_left x y := (isLUB_dsup hE.out x y).1 (Set.mem_insert _ _)
  le_sup_right x y := (isLUB_dsup hE.out x y).1 (Set.mem_insert_of_mem _ rfl)
  sup_le x y _ hx hy := (isLUB_dsup hE.out x y).2 fun _ h => h.elim (· ▸ hx) (· ▸ hy)
  inf x y := -dsup hE.out (-x) (-y)
  inf_le_left _ _ := neg_le.1 ((isLUB_dsup hE.out _ _).1 (Set.mem_insert _ _))
  inf_le_right _ _ := neg_le.1 ((isLUB_dsup hE.out _ _).1 (Set.mem_insert_of_mem _ rfl))
  le_inf _ _ _ hx hy := le_neg.1 ((isLUB_dsup hE.out _ _).2 fun _ h =>
    h.elim (· ▸ neg_le_neg hx) (· ▸ neg_le_neg hy))

end Bidual
