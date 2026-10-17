/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.PositiveDual.Basic
public import PhyslibAlpha.Mathematics.Order.VectorLattice
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The Riesz–Kantorovich formula

Riesz decomposition makes positive functionals a lattice via the Riesz–Kantorovich formula.

## i. Overview

An ordered real vector space has the Riesz decomposition when a nonnegative element below a sum of
two nonnegative elements splits into pieces below the summands. Vector lattices have it. Then any
two positive functionals have a least upper bound, given by the Riesz–Kantorovich formula
`(φ ⊔ ψ) f = sup {φ g + ψ (f - g) | 0 ≤ g ≤ f}`: the positive functionals form a lattice.

In a lattice of positive functionals, a positive functional below a sum splits into pieces below
the summands, and finite families with the same sum have common refinements.

## ii. Key results

- `HasRieszDecomposition E` : the Riesz decomposition.
- `PositiveLinearMap.isLUB_rkSup` : the Riesz–Kantorovich formula gives the least upper bound.
- `HasLatticeDualCone E` : the positive functionals form a lattice.
- `HasRieszDecomposition.hasLatticeDualCone` : the Riesz decomposition makes the positive
  functionals a lattice.
- `VectorLattice.hasLatticeDualCone` : the positive functionals on a vector lattice form a lattice.
- `HasLatticeDualCone.exists_refinement` : positive functionals refine.
- `PositiveLinearMap.HasRefinement` : finite families with the same sum have a common refinement.

## iii. Table of contents

- A. The Riesz–Kantorovich supremum
- B. The lattice dual cone
- C. Riesz decomposition of positive functionals
- D. Finite refinement of positive functionals

## iv. References

- C. D. Aliprantis and O. Burkinshaw, *Positive Operators*, Springer, 2006, ch. 1.
- E. M. Alfsen, *Compact Convex Sets and Boundary Integrals*, Springer, 1971, ch. II.

-/

@[expose] public section

open scoped NNReal

/-!

## A. The Riesz–Kantorovich supremum

-/

/-- Riesz decomposition: a nonnegative observable below a sum of two nonnegative observables splits
into two pieces, each below one summand. -/
def HasRieszDecomposition (E : Type*) [AddCommGroup E] [PartialOrder E] : Prop :=
  ∀ ⦃f₁ f₂ g : E⦄, 0 ≤ f₁ → 0 ≤ f₂ → g ∈ Set.Icc 0 (f₁ + f₂) →
    ∃ g₁ ∈ Set.Icc 0 f₁, g - g₁ ∈ Set.Icc 0 f₂

/-- A real vector lattice has the Riesz decomposition. -/
lemma VectorLattice.hasRieszDecomposition (E : Type*) [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] : HasRieszDecomposition E :=
  fun _ _ g h₁ h₂ hg =>
  have h := VectorLattice.riesz_decomposition h₁ h₂ hg.1 hg.2
  ⟨g ⊓ _, ⟨h.1, h.2.1⟩, h.2.2⟩

namespace PositiveLinearMap

section RieszDecomposition

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  (φ ψ : E →ₚ[ℝ] ℝ)

/-- The best split of `f` between `φ` and `ψ`: the supremum of `φ g + ψ (f - g)` over
`0 ≤ g ≤ f`. -/
noncomputable def rkSup (f : E) : ℝ := sSup ((fun g => φ g + ψ (f - g)) '' Set.Icc 0 f)

variable {φ ψ}

lemma bddAbove_rkSup (f : E) : BddAbove ((fun g => φ g + ψ (f - g)) '' Set.Icc 0 f) :=
  ⟨φ f + ψ f, Set.forall_mem_image.2 fun _ hg => add_le_add (φ.monotone' hg.2)
    (ψ.monotone' (sub_le_self _ hg.1))⟩

lemma le_rkSup {f g : E} (hg : g ∈ Set.Icc 0 f) : φ g + ψ (f - g) ≤ rkSup φ ψ f :=
  le_csSup (bddAbove_rkSup f) ⟨g, hg, rfl⟩

omit [IsOrderedAddMonoid E] in
lemma rkSup_le {f : E} (hf : 0 ≤ f) {r : ℝ} (h : ∀ g ∈ Set.Icc 0 f, φ g + ψ (f - g) ≤ r) :
    rkSup φ ψ f ≤ r :=
  csSup_le ⟨_, 0, ⟨le_rfl, hf⟩, rfl⟩ (Set.forall_mem_image.2 h)

lemma rkSup_nonneg {f : E} (hf : 0 ≤ f) : 0 ≤ rkSup φ ψ f := by
  simpa using (map_nonneg ψ hf).trans_eq (by simp) |>.trans (le_rkSup ⟨le_rfl, hf⟩)

lemma rkSup_add_rkSup_le {f₁ f₂ : E} (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) :
    rkSup φ ψ f₁ + rkSup φ ψ f₂ ≤ rkSup φ ψ (f₁ + f₂) := by
  have key : ∀ g₁ ∈ Set.Icc 0 f₁, ∀ g₂ ∈ Set.Icc 0 f₂,
      φ g₁ + ψ (f₁ - g₁) + (φ g₂ + ψ (f₂ - g₂)) ≤ rkSup φ ψ (f₁ + f₂) := fun g₁ hg₁ g₂ hg₂ => by
    have := le_rkSup (φ := φ) (ψ := ψ) (f := f₁ + f₂)
      ⟨add_nonneg hg₁.1 hg₂.1, add_le_add hg₁.2 hg₂.2⟩
    simp only [map_add, map_sub] at this ⊢
    linarith
  have hn₁ := (Set.nonempty_Icc.2 h₁).image fun g => φ g + ψ (f₁ - g)
  have hn₂ := (Set.nonempty_Icc.2 h₂).image fun g => φ g + ψ (f₂ - g)
  rw [rkSup, rkSup, ← csSup_add hn₁ (bddAbove_rkSup f₁) hn₂ (bddAbove_rkSup f₂)]
  exact csSup_le (hn₁.add hn₂) fun _ ⟨_, ⟨g₁, hg₁, e₁⟩, _, ⟨g₂, hg₂, e₂⟩, e⟩ =>
    e ▸ e₁ ▸ e₂ ▸ key g₁ hg₁ g₂ hg₂

lemma rkSup_add (hE : HasRieszDecomposition E) {f₁ f₂ : E} (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) :
    rkSup φ ψ (f₁ + f₂) = rkSup φ ψ f₁ + rkSup φ ψ f₂ := by
  refine le_antisymm (rkSup_le (add_nonneg h₁ h₂) fun g hg => ?_) (rkSup_add_rkSup_le h₁ h₂)
  obtain ⟨g₁, hg₁, hg₂⟩ := hE h₁ h₂ hg
  have := add_le_add (le_rkSup (φ := φ) (ψ := ψ) hg₁) (le_rkSup (φ := φ) (ψ := ψ) hg₂)
  simp only [map_add, map_sub] at this ⊢
  linarith

lemma rkSup_smul [PosSMulMono ℝ E] {c : ℝ} (hc : 0 < c) {f : E} (hf : 0 ≤ f) :
    rkSup φ ψ (c • f) = c * rkSup φ ψ f := by
  refine le_antisymm (rkSup_le (smul_nonneg hc.le hf) fun g hg => ?_) ?_
  · have hg' : c⁻¹ • g ∈ Set.Icc 0 f := ⟨smul_nonneg (inv_nonneg.2 hc.le) hg.1, by
      simpa [inv_smul_le_iff_of_pos hc] using hg.2⟩
    have := mul_le_mul_of_nonneg_left (le_rkSup (φ := φ) (ψ := ψ) hg') hc.le
    simpa [map_sub, mul_add, mul_sub, ← mul_assoc, hc.ne', smul_sub] using this
  · rw [← le_inv_mul_iff₀ hc]
    refine rkSup_le hf fun g hg => (le_inv_mul_iff₀ hc).2 ?_
    have := le_rkSup (φ := φ) (ψ := ψ) (f := c • f)
      ⟨smul_nonneg hc.le hg.1, smul_le_smul_of_nonneg_left hg.2 hc.le⟩
    simpa [map_sub, mul_add, mul_sub, ← smul_sub] using this

variable (φ ψ)

variable [PosSMulMono ℝ E] [IsDirectedOrder E] (hE : HasRieszDecomposition E)

/-- The Riesz–Kantorovich supremum of two positive functionals. -/
noncomputable def rkSupMap : E →ₚ[ℝ] ℝ :=
  ofCone (rkSup φ ψ) (fun _ hf => rkSup_nonneg hf) (fun _ _ => rkSup_add hE)
    (fun _ _ hc hf => rkSup_smul hc hf)

variable {φ ψ}

lemma rkSupMap_apply {f : E} (hf : 0 ≤ f) : rkSupMap φ ψ hE f = rkSup φ ψ f :=
  ofCone_apply _ _ _ _ hf

variable (φ ψ)

/-- **Riesz–Kantorovich**: the least upper bound of two positive functionals, when the space has
the Riesz decomposition. -/
lemma isLUB_rkSup : IsLUB {φ, ψ} (rkSupMap φ ψ hE) := by
  refine ⟨?_, fun θ hθ f hf => ?_⟩
  · intro χ hχ f hf
    rw [rkSupMap_apply hE hf]
    rcases hχ with h | h
    · rw [h]
      simpa using le_rkSup (φ := φ) (ψ := ψ) ⟨hf, le_rfl⟩
    · rw [Set.mem_singleton_iff.1 h]
      simpa using le_rkSup (φ := φ) (ψ := ψ) ⟨le_rfl, hf⟩
  rw [rkSupMap_apply hE hf]
  refine rkSup_le hf fun g hg => ?_
  have h₁ := hθ (Set.mem_insert _ _) g hg.1
  have h₂ := hθ (Set.mem_insert_of_mem _ rfl) (f - g) (sub_nonneg.2 hg.2)
  have h₃ : θ g + θ (f - g) = θ f := by rw [← map_add, add_sub_cancel]
  linarith

end RieszDecomposition

end PositiveLinearMap

/-!

## B. The lattice dual cone

-/

/-- The positive functionals on `E` form a lattice: any two have a least upper bound. -/
def HasLatticeDualCone (E : Type*) [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
    [Module ℝ E] [IsDirectedOrder E] : Prop :=
  ∀ φ ψ : E →ₚ[ℝ] ℝ, ∃ χ, IsLUB {φ, ψ} χ

/-- **Riesz–Kantorovich**: when the space has the Riesz decomposition, the positive functionals
form a lattice. -/
lemma HasRieszDecomposition.hasLatticeDualCone {E : Type*} [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E] [IsDirectedOrder E]
    (hE : HasRieszDecomposition E) : HasLatticeDualCone E :=
  fun φ ψ => ⟨_, PositiveLinearMap.isLUB_rkSup φ ψ hE⟩

/-- **Riesz–Kantorovich**: the positive functionals on a real vector lattice form a lattice. -/
lemma VectorLattice.hasLatticeDualCone (E : Type*) [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E] : HasLatticeDualCone E :=
  (VectorLattice.hasRieszDecomposition E).hasLatticeDualCone

/-!

## C. Riesz decomposition of positive functionals

-/

namespace HasLatticeDualCone

open PositiveLinearMap

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [IsDirectedOrder E] (hE : HasLatticeDualCone E)
include hE

/-- **Riesz decomposition**: a positive functional below `α + β` splits into pieces below `α`,
resp. `β`. -/
lemma exists_add_eq_of_le_add {θ α β : E →ₚ[ℝ] ℝ} (h : θ ≤ α + β) :
    ∃ θ₁ θ₂, θ₁ ≤ α ∧ θ₂ ≤ β ∧ θ = θ₁ + θ₂ := by
  obtain ⟨σ, hσ⟩ := hE θ α
  have hθ : θ ≤ σ := hσ.1 (Set.mem_insert _ _)
  have hα : α ≤ σ := hσ.1 (Set.mem_insert_of_mem _ rfl)
  have h₁ : σ ≤ θ + α := hσ.2 fun χ hχ => by
    rcases hχ with rfl | rfl
    exacts [le_add_right _ _, add_comm χ θ ▸ le_add_right _ _]
  have h₂ : σ ≤ α + β := hσ.2 fun χ hχ => by
    rcases hχ with rfl | rfl
    exacts [h, le_add_right _ _]
  refine ⟨subOfLE (θ + α) σ h₁, subOfLE σ α hα, fun f hf => ?_, fun f hf => ?_, ext fun f => ?_⟩
  · simp only [subOfLE_apply, add_apply]
    linarith [hθ f hf]
  · simp only [subOfLE_apply]
    linarith [h₂ f hf, add_apply α β f]
  · simp only [add_apply, subOfLE_apply]
    ring

/-- **Riesz refinement**: a finite family of positive functionals summing to `α + β` splits into
two families summing to `α`, resp. `β`. -/
lemma exists_refinement {m : ℕ} (ψ : Fin m → E →ₚ[ℝ] ℝ) {α β : E →ₚ[ℝ] ℝ}
    (h : ∑ i, ψ i = α + β) : ∃ ψ₁ ψ₂ : Fin m → E →ₚ[ℝ] ℝ,
      (∀ i, ψ i = ψ₁ i + ψ₂ i) ∧ ∑ i, ψ₁ i = α ∧ ∑ i, ψ₂ i = β := by
  induction m generalizing α β with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
    exact ⟨0, 0, fun i => i.elim0, by simp [eq_zero_of_add_eq_zero h.symm],
      by simp [eq_zero_of_add_eq_zero ((add_comm α β) ▸ h.symm)]⟩
  | succ m ih =>
    rw [Fin.sum_univ_succ] at h
    obtain ⟨θ₁, θ₂, h₁, h₂, e⟩ := exists_add_eq_of_le_add hE (h ▸ le_add_right (ψ 0) _)
    obtain ⟨ψ₁, ψ₂, hψ, s₁, s₂⟩ := ih (fun i => ψ i.succ) (eq_subOfLE_add_subOfLE h e h₁ h₂)
    refine ⟨Fin.cons θ₁ ψ₁, Fin.cons θ₂ ψ₂,
      fun i => Fin.cases (by simpa using e) (fun i => by simpa using hψ i) i, ?_, ?_⟩
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, s₁, add_subOfLE]
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, s₂, add_subOfLE]

end HasLatticeDualCone

/-!

## D. Finite refinement of positive functionals

-/

namespace PositiveLinearMap

variable (E : Type*) [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]

/-- Positive functionals have finite refinement when any two finite families with the same sum
are the row and column sums of a common table of positive functionals. -/
def HasRefinement : Prop :=
  ∀ (m n : ℕ) (α : Fin m → E →ₚ[ℝ] ℝ) (β : Fin n → E →ₚ[ℝ] ℝ), ∑ i, α i = ∑ j, β j →
    ∃ γ : Fin m → Fin n → E →ₚ[ℝ] ℝ, (∀ i, ∑ j, γ i j = α i) ∧ ∀ j, ∑ i, γ i j = β j

variable {E}

/-- A lattice dual cone gives finite refinement of positive functionals. -/
lemma HasLatticeDualCone.hasRefinement [IsDirectedOrder E] (hE : HasLatticeDualCone E) :
    HasRefinement E := by
  classical
  intro m n
  induction n with
  | zero =>
    intro α β h
    refine ⟨fun _ j => j.elim0, fun i => ?_, fun j => j.elim0⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    exact (le_antisymm (h ▸ le_sum α (Finset.mem_univ i)) (zero_le _)).symm
  | succ n ih =>
    intro α β h
    rw [Fin.sum_univ_succ] at h
    obtain ⟨ψ₁, ψ₂, hψ, s₁, s₂⟩ := hE.exists_refinement α h
    obtain ⟨γ, hr, hc⟩ := ih ψ₂ (fun j => β j.succ) s₂
    refine ⟨fun i => Fin.cons (ψ₁ i) (γ i), fun i => ?_,
      fun j => Fin.cases (by simpa using s₁) (fun j => by simpa using hc j) j⟩
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [hr i]
    exact (hψ i).symm

omit [IsOrderedAddMonoid E] in
/-- Finite refinement, indexed by arbitrary finite types. -/
lemma HasRefinement.exists_table (hE : HasRefinement E) {I K : Type*} [Fintype I] [Fintype K]
    (α : I → E →ₚ[ℝ] ℝ) (β : K → E →ₚ[ℝ] ℝ) (h : ∑ i, α i = ∑ j, β j) :
    ∃ γ : I → K → E →ₚ[ℝ] ℝ, (∀ i, ∑ j, γ i j = α i) ∧ ∀ j, ∑ i, γ i j = β j := by
  set e := Fintype.equivFin I
  set e' := Fintype.equivFin K
  obtain ⟨γ, hr, hc⟩ := hE _ _ (α ∘ e.symm) (β ∘ e'.symm)
    ((e.symm.sum_comp α).trans (h.trans (e'.symm.sum_comp β).symm))
  refine ⟨fun i j => γ (e i) (e' j), fun i => ?_, fun j => ?_⟩
  · simpa using (e'.sum_comp (γ (e i))).trans (hr (e i))
  · simpa using (e.sum_comp fun k => γ k (e' j)).trans (hc (e' j))

end PositiveLinearMap
