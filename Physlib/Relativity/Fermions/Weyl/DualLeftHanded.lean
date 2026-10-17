/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Physlib.Meta.TODO.Basic
/-!

# Dual left handed Weyl fermions

Dual left-handed Weyl fermions and the irreducible representation of `SL(2, ℂ)` they carry.

## i. Overview

Dual left-handed Weyl fermions sit in the dual of the fundamental representation of `SL(2,ℂ)`,
and we consider them to have down indices `ψ_α` with `α = 1,2`.

In this file we define the type `DualLeftHandedWeyl`, equip it with the structure of a
two-dimensional complex vector space with a standard basis, define the representation `rep` of
`SL(2, ℂ)` on it by `M ↦ (M⁻¹)ᵀ`, and show that `rep` is irreducible (C.1).

## ii. Key results

- `DualLeftHandedWeyl` : the type of dual left-handed Weyl fermions.
- `DualLeftHandedWeyl.basis` : the standard basis, indexed by `Fin 2`.
- `DualLeftHandedWeyl.rep` : the representation of `SL(2, ℂ)`.
- `DualLeftHandedWeyl.eq_zero_of_rep_eq_smul` : `rep` has no common eigenvector.
- `DualLeftHandedWeyl.end_eq_smul_id_of_commute_rep` : Schur's lemma for `rep`.

## iii. Table of contents

- A. The definition of the type
  - A.1. Underlying module structure
- B. Basis
- C. Representation
  - C.1. Irreducibility

## iv. References

* A good reference for the material in this file, although it uses a different
  index convention: https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf. [ref: ucdavis_spinorfeynrules]

-/

@[expose] public section

namespace Fermion
noncomputable section

/-!

## A. The definition of the type

-/

/-- The module in which dual-left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure DualLeftHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace DualLeftHandedWeyl
open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

### A.1. Underlying module structure

-/

/-- The equivalence between `DualLeftHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : DualLeftHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid DualLeftHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup DualLeftHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The additive equivalence between `DualLeftHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂAddEquiv : DualLeftHandedWeyl ≃+ (Fin 2 → ℂ) :=
  { toFin2ℂFun with map_add' _ _ := rfl }

/-- The instance of `Module` on `DualLeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ DualLeftHandedWeyl := AddEquiv.module ℂ toFin2ℂAddEquiv

/-- The linear equivalence between `DualLeftHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : DualLeftHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `DualLeftHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : DualLeftHandedWeyl) := toFin2ℂEquiv ψ

lemma toFin2ℂ_eq_val (ψ : DualLeftHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl

instance : Nontrivial DualLeftHandedWeyl := toFin2ℂEquiv.toEquiv.nontrivial

/-!

## B. Basis

-/

/-- The standard basis on dual-left-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ DualLeftHandedWeyl := Basis.ofEquivFun
  (AddEquiv.linearEquiv ℂ DualLeftHandedWeyl.toFin2ℂAddEquiv)

lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, AddEquiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : DualLeftHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

instance : FiniteDimensional ℂ DualLeftHandedWeyl := Module.Finite.of_basis basis

/-- Dual left-handed Weyl fermions form a two-dimensional complex vector space. -/
@[simp]
lemma finrank_eq_two : Module.finrank ℂ DualLeftHandedWeyl = 2 := by
  rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]

/-!

## C. Representation

-/

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ. In index notation corresponds to a left-handed Weyl fermion with indices ψ_a. -/
def rep : Representation ℂ SL(2,ℂ) DualLeftHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : DualLeftHandedWeyl) =>
      DualLeftHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ ψ.toFin2ℂ),
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
    exact transpose_mul _ _

lemma rep_apply (M : SL(2,ℂ)) (ψ : DualLeftHandedWeyl) : rep M ψ = ⟨(M.1⁻¹)ᵀ *ᵥ ψ.1⟩ := rfl

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : DualLeftHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, M.1⁻¹ j i * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, M.1⁻¹ i j • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) : (LinearMap.toMatrix basis basis) (rep M) = (M.1⁻¹)ᵀ := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change ((M.1⁻¹)ᵀ *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = M.1⁻¹ i j := by
  fin_cases j <;> simp [rep_apply_basis]

/-!

### C.1. Irreducibility

-/

TODO "Explore whether the duality between left-handed and dual left-handed Weyl fermions can be
  leveraged to simplify the proof of irreducibility."

/-- The representation `rep` has no common eigenvector. -/
lemma eq_zero_of_rep_eq_smul (ψ : DualLeftHandedWeyl)
    (h : ∀ M : SL(2,ℂ), ∃ c : ℂ, rep M ψ = c • ψ) : ψ = 0 := by
  have h : ∀ M : SL(2,ℂ), ∃ c : ℂ, ∀ i, ((M.1⁻¹)ᵀ *ᵥ ψ.1) i = c * ψ.1 i := by
    intro M
    obtain ⟨c, hc⟩ := h M
    rw [rep_apply] at hc
    exact ⟨c, fun i => congrFun (congrArg DualLeftHandedWeyl.val hc) i⟩
  obtain ⟨c₁, hc₁⟩ := h ⟨!![1, 0; -1, 1], by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨c₂, hc₂⟩ := h ⟨!![1, -1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have h₁₀ := hc₁ 0
  have h₁₁ := hc₁ 1
  have h₂₁ := hc₂ 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.inv_def, Matrix.det_fin_two_of,
    Matrix.adjugate_fin_two_of] at h₁₀ h₁₁ h₂₁
  have hb : ψ.val 1 = 0 := sq_eq_zero_iff.1 (by linear_combination ψ.val 1 * h₁₀ - ψ.val 0 * h₁₁)
  have ha : ψ.val 0 = 0 := by linear_combination h₂₁ + (c₂ - 1) * hb
  refine toFin2ℂEquiv.injective (funext fun i => ?_)
  fin_cases i <;> assumption

/-- A submodule of `DualLeftHandedWeyl` stable under `rep` is either `⊥` or everything. -/
lemma eq_bot_or_eq_top_of_rep_mem (p : Submodule ℂ DualLeftHandedWeyl)
    (h : ∀ (M : SL(2,ℂ)) (ψ : DualLeftHandedWeyl), ψ ∈ p → rep M ψ ∈ p) :
    p = ⊥ ∨ p = ⊤ := by
  refine (eq_or_ne p ⊥).imp id fun hp => ?_
  obtain ⟨ψ, hψp, hψ⟩ := (Submodule.ne_bot_iff p).1 hp
  rcases eq_or_lt_of_le ((Submodule.span_singleton_le_iff_mem ψ p).2 hψp) with heq | hlt
  · exact absurd (eq_zero_of_rep_eq_smul ψ fun M =>
      (Submodule.mem_span_singleton.1 (heq.symm ▸ h M ψ hψp)).imp fun c hc => hc.symm) hψ
  · have h₁ := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_span_singleton hψ] at h₁
    have h₂ : Module.finrank ℂ p ≤ 2 := by simpa using Submodule.finrank_le p
    exact Submodule.eq_top_of_finrank_eq (by rw [finrank_eq_two]; omega)

/-- The representation `rep` of `SL(2, ℂ)` is irreducible. -/
instance : rep.IsIrreducible where
  exists_pair_ne := ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  eq_bot_or_eq_top p :=
    (eq_bot_or_eq_top_of_rep_mem p.toSubmodule
      fun M _ hψ => p.apply_mem_toSubmodule M hψ).imp
      (fun h => Subrepresentation.toSubmodule_injective h)
      fun h => Subrepresentation.toSubmodule_injective h

/-- Schur's lemma for dual left-handed Weyl fermions. -/
lemma end_eq_smul_id_of_commute_rep {T : Module.End ℂ DualLeftHandedWeyl}
    (hT : ∀ M : SL(2,ℂ), T ∘ₗ rep M = rep M ∘ₗ T) : ∃ μ : ℂ, T = μ • LinearMap.id := by
  obtain ⟨μ, hμ⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := rep)).2 ⟨T, hT⟩
  exact ⟨μ, congrArg Representation.IntertwiningMap.toLinearMap hμ.symm⟩

end DualLeftHandedWeyl

end
end Fermion
