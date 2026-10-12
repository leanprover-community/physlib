/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Irreducible
/-!

# Dual right handed Weyl fermions

Dual right-handed Weyl fermions and the irreducible representation of `SL(2, ℂ)` they carry.

## i. Overview

Dual right-handed Weyl fermions sit in the dual-conjugate representation of `SL(2,ℂ)`,
and we consider them to have down indices `ψ_{dot α}` with `α = 1,2`.

In this file we define the type `DualRightHandedWeyl`, equip it with the structure of a
two-dimensional complex vector space with a standard basis, define the representation `rep` of
`SL(2, ℂ)` on it by `M ↦ (M⁻¹)^†`, and show that `rep` is irreducible (C.1).

## ii. Key results

- `DualRightHandedWeyl` : the type of dual right-handed Weyl fermions.
- `DualRightHandedWeyl.basis` : the standard basis, indexed by `Fin 2`.
- `DualRightHandedWeyl.rep` : the representation of `SL(2, ℂ)`.
- `DualRightHandedWeyl.eq_zero_of_rep_eq_smul` : `rep` has no common eigenvector.
- `DualRightHandedWeyl.end_eq_smul_id_of_commute_rep` : Schur's lemma for `rep`.

## iii. Table of contents

- A. The definition of the type
  - A.1. Underlying module structure
- B. Basis
- C. Representation
  - C.1. Irreducibility

## iv. References

* Dreiner, Haber and Martin, Two-component spinor techniques and Feynman rules for quantum
  field theory and supersymmetry, Phys. Rept. 494 (2010) 1-196. [ref: Dreiner:2008tw]

-/

@[expose] public section

namespace Fermion
noncomputable section

/-!

## A. The definition of the type

-/

/-- The module in which dual-right handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure DualRightHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace DualRightHandedWeyl
open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

### A.1. Underlying module structure

-/

/-- The equivalence between `DualRightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : DualRightHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid DualRightHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup DualRightHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The additive equivalence between `DualRightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂAddEquiv : DualRightHandedWeyl ≃+ (Fin 2 → ℂ) :=
  { toFin2ℂFun with map_add' _ _ := rfl }

/-- The instance of `Module` on `DualRightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ DualRightHandedWeyl := AddEquiv.module ℂ toFin2ℂAddEquiv

/-- The linear equivalence between `DualRightHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : DualRightHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `DualRightHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : DualRightHandedWeyl) := toFin2ℂEquiv ψ

lemma toFin2ℂ_eq_val (ψ : DualRightHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl

instance : Nontrivial DualRightHandedWeyl := toFin2ℂEquiv.toEquiv.nontrivial

/-!

## B. Basis

-/

/-- The standard basis on dual-right-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ DualRightHandedWeyl := Basis.ofEquivFun
  (AddEquiv.linearEquiv ℂ DualRightHandedWeyl.toFin2ℂAddEquiv)

lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, AddEquiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : DualRightHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

instance : FiniteDimensional ℂ DualRightHandedWeyl := Module.Finite.of_basis basis

/-- Dual right-handed Weyl fermions form a two-dimensional complex vector space. -/
@[simp]
lemma finrank_eq_two : Module.finrank ℂ DualRightHandedWeyl = 2 := by
  rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]

/-!

## C. Representation

-/


/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)^†.
    In index notation this corresponds to a Weyl fermion with index `ψ_{dot a}`. -/
def rep : Representation ℂ SL(2,ℂ) DualRightHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : DualRightHandedWeyl) =>
      DualRightHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹).conjTranspose *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact conjTranspose_mul _ _

lemma rep_apply (M : SL(2,ℂ)) (ψ : DualRightHandedWeyl) :
    rep M ψ = ⟨(M.1⁻¹).conjTranspose *ᵥ ψ.1⟩ := rfl

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : DualRightHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, (M.1⁻¹).conjTranspose i j * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, (M.1⁻¹).conjTranspose j i • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) :
    (LinearMap.toMatrix basis basis) (rep M) = (M.1⁻¹).conjTranspose := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change ((M.1⁻¹).conjTranspose *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = star (M.1⁻¹ i j) := by
  fin_cases j <;> simp [rep_apply_basis]

/-!

### C.1. Irreducibility

-/

/-- The representation `rep` has no common eigenvector: a dual right-handed Weyl fermion which
  is an eigenvector of `rep M` for every `M` in `SL(2, ℂ)` is zero. Equivalently, `rep` leaves
  no line in `DualRightHandedWeyl` invariant. -/
lemma eq_zero_of_rep_eq_smul (ψ : DualRightHandedWeyl)
    (h : ∀ M : SL(2,ℂ), ∃ c : ℂ, rep M ψ = c • ψ) : ψ = 0 := by
  -- the hypothesis, read off componentwise
  have key : ∀ M : SL(2,ℂ), ∃ c : ℂ, ∀ i, ((M.1⁻¹).conjTranspose *ᵥ ψ.1) i = c * ψ.1 i := by
    intro M
    obtain ⟨c, hc⟩ := h M
    rw [rep_apply] at hc
    exact ⟨c, fun i => congrFun (congrArg DualRightHandedWeyl.val hc) i⟩
  -- the matrices `(M⁻¹)^†` through which the two elements `M` below act are the transvections
  -- `!![1, 1; 0, 1]` and `!![1, 0; 1, 1]`, whose fixed lines are distinct
  have e₁ : ((!![(1 : ℂ), 0; -1, 1])⁻¹).conjTranspose = !![1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
  have e₂ : ((!![(1 : ℂ), -1; 0, 1])⁻¹).conjTranspose = !![1, 0; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
  obtain ⟨c₁, hc₁⟩ := key ⟨!![1, 0; -1, 1], by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨c₂, hc₂⟩ := key ⟨!![1, -1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have h₁₀ := hc₁ 0
  have h₁₁ := hc₁ 1
  have h₂₁ := hc₂ 1
  simp only [e₁] at h₁₀ h₁₁
  simp only [e₂] at h₂₁
  simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] at h₁₀ h₁₁ h₂₁
  -- the first transvection scales `ψ` only if its second component vanishes
  have hb : ψ.val 1 = 0 := by
    rcases eq_or_ne c₁ 1 with rfl | hc
    · linear_combination h₁₀
    · exact (mul_eq_zero.1 (show ψ.val 1 * (1 - c₁) = 0 by
        linear_combination h₁₁)).resolve_right (sub_ne_zero_of_ne (Ne.symm hc))
  -- the second transvection then kills the first component as well
  have ha : ψ.val 0 = 0 := by linear_combination h₂₁ + (c₂ - 1) * hb
  apply toFin2ℂEquiv.injective
  rw [map_zero]
  funext i
  fin_cases i
  · exact ha
  · exact hb

/-- A submodule of `DualRightHandedWeyl` stable under `rep` is either `⊥` or everything. -/
lemma eq_bot_or_eq_top_of_rep_mem (p : Submodule ℂ DualRightHandedWeyl)
    (h : ∀ (M : SL(2,ℂ)) (ψ : DualRightHandedWeyl), ψ ∈ p → rep M ψ ∈ p) :
    p = ⊥ ∨ p = ⊤ := by
  rcases eq_or_ne p ⊥ with hp | hp
  · exact Or.inl hp
  refine Or.inr ?_
  obtain ⟨ψ, hψp, hψ⟩ := (Submodule.ne_bot_iff p).1 hp
  rcases eq_or_lt_of_le ((Submodule.span_singleton_le_iff_mem ψ p).2 hψp) with heq | hlt
  · -- `p` is the line through `ψ`, so `ψ` is a common eigenvector of `rep`: contradiction
    refine absurd (eq_zero_of_rep_eq_smul ψ fun M => ?_) hψ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (show rep M ψ ∈ ℂ ∙ ψ by rw [heq]; exact h M ψ hψp)
    exact ⟨c, hc.symm⟩
  · -- `p` strictly contains a line, so has rank two, so is everything
    have h₁ := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_span_singleton hψ] at h₁
    have h₂ : Module.finrank ℂ p ≤ 2 := by simpa using Submodule.finrank_le p
    exact Submodule.eq_top_of_finrank_eq (by rw [finrank_eq_two]; omega)

/-- The representation `rep` of `SL(2, ℂ)` is irreducible. -/
instance : Representation.IsIrreducible rep where
  exists_pair_ne := ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  eq_bot_or_eq_top p :=
    (eq_bot_or_eq_top_of_rep_mem p.toSubmodule
      fun M _ hψ => p.apply_mem_toSubmodule M hψ).imp
      (fun h => Subrepresentation.toSubmodule_injective h)
      fun h => Subrepresentation.toSubmodule_injective h

/-- Schur's lemma for dual right-handed Weyl fermions: every endomorphism of
  `DualRightHandedWeyl` commuting with the action of `SL(2, ℂ)` is a multiple of the
  identity. -/
lemma end_eq_smul_id_of_commute_rep {T : Module.End ℂ DualRightHandedWeyl}
    (hT : ∀ M : SL(2,ℂ), T ∘ₗ rep M = rep M ∘ₗ T) : ∃ μ : ℂ, T = μ • LinearMap.id := by
  obtain ⟨μ, hμ⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := rep)).2 ⟨T, hT⟩
  refine ⟨μ, LinearMap.ext fun ψ => ?_⟩
  simpa [Representation.IntertwiningMap.algebraMap_apply] using (DFunLike.congr_fun hμ ψ).symm

end DualRightHandedWeyl
end
end Fermion
