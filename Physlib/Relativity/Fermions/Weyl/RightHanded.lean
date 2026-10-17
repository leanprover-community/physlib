/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Irreducible
/-!

# Right handed Weyl fermions

Right-handed Weyl fermions and the irreducible representation of `SL(2, ℂ)` they carry.

## i. Overview

Right-handed Weyl fermions sit in the conjugate representation of `SL(2,ℂ)`,
and we consider them to have up indices `ψ^{dot α}` with `α = 1,2`.

In this file we define the type `RightHandedWeyl`, equip it with the structure of a
two-dimensional complex vector space with a standard basis, define the representation `rep` of
`SL(2, ℂ)` on it by `M ↦ M̅`, and show that `rep` is irreducible (C.1).

## ii. Key results

- `RightHandedWeyl` : the type of right-handed Weyl fermions.
- `RightHandedWeyl.basis` : the standard basis, indexed by `Fin 2`.
- `RightHandedWeyl.rep` : the representation of `SL(2, ℂ)`.
- `RightHandedWeyl.eq_zero_of_rep_eq_smul` : `rep` has no common eigenvector.
- `RightHandedWeyl.end_eq_smul_id_of_commute_rep` : Schur's lemma for `rep`.

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

/-- The module in which right handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure RightHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ

namespace RightHandedWeyl
open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

### A.1. Underlying module structure

-/

/-- The equivalence between `RightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : RightHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid RightHandedWeyl := Equiv.addCommMonoid toFin2ℂFun

/-- The instance of `AddCommGroup` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup RightHandedWeyl := Equiv.addCommGroup toFin2ℂFun

/-- The additive equivalence between `RightHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂAddEquiv : RightHandedWeyl ≃+ (Fin 2 → ℂ) :=
  { toFin2ℂFun with map_add' _ _ := rfl }

/-- The instance of `Module` on `RightHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ RightHandedWeyl := AddEquiv.module ℂ toFin2ℂAddEquiv

/-- The linear equivalence between `RightHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : RightHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 2 → ℂ` of a element in `RightHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : RightHandedWeyl) := toFin2ℂEquiv ψ

lemma toFin2ℂ_eq_val (ψ : RightHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl

instance : Nontrivial RightHandedWeyl := toFin2ℂEquiv.toEquiv.nontrivial

/-!

## B. Basis

-/

/-- The standard basis on right-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ RightHandedWeyl := Basis.ofEquivFun
  (AddEquiv.linearEquiv ℂ RightHandedWeyl.toFin2ℂAddEquiv)

lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, AddEquiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]

lemma eq_sum_basis (ψ : RightHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl

lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]

instance : FiniteDimensional ℂ RightHandedWeyl := Module.Finite.of_basis basis

/-- Right-handed Weyl fermions form a two-dimensional complex vector space. -/
@[simp]
lemma finrank_eq_two : Module.finrank ℂ RightHandedWeyl = 2 := by
  rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]

/-!

## C. Representation

-/

/-- The vector space ℂ^2 carrying the conjugate representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^{dot a}. -/
def rep : Representation ℂ SL(2,ℂ) RightHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : RightHandedWeyl) =>
      RightHandedWeyl.toFin2ℂEquiv.symm (M.1.map star *ᵥ ψ.toFin2ℂ),
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
    simp only [SpecialLinearGroup.coe_mul, RCLike.star_def, Matrix.map_mul, LinearMap.coe_mk,
      AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec]

lemma rep_apply (M : SL(2,ℂ)) (ψ : RightHandedWeyl) : rep M ψ = ⟨M.1.map star *ᵥ ψ.1⟩ := rfl

lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : RightHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, M.1.map star i j * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl

lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, M.1.map star j i • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]

lemma rep_toMatrix (M : SL(2,ℂ)) : (LinearMap.toMatrix basis basis) (rep M) = M.1.map star := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1.map star *ᵥ (Pi.single j 1)) i = _
  simp

lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = star (M.1 j i) := by
  fin_cases j <;> simp [rep_apply_basis]

/-!

### C.1. Irreducibility

-/

/-- The representation `rep` has no common eigenvector. -/
lemma eq_zero_of_rep_eq_smul (ψ : RightHandedWeyl)
    (h : ∀ M : SL(2,ℂ), ∃ c : ℂ, rep M ψ = c • ψ) : ψ = 0 := by
  have h : ∀ M : SL(2,ℂ), ∃ c : ℂ, ∀ i, (M.1.map star *ᵥ ψ.1) i = c * ψ.1 i := by
    intro M
    obtain ⟨c, hc⟩ := h M
    rw [rep_apply] at hc
    exact ⟨c, fun i => congrFun (congrArg RightHandedWeyl.val hc) i⟩
  obtain ⟨c₁, hc₁⟩ := h ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨c₂, hc₂⟩ := h ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have h₁₀ := hc₁ 0
  have h₁₁ := hc₁ 1
  have h₂₁ := hc₂ 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₁₀ h₁₁ h₂₁
  have hb : ψ.val 1 = 0 := sq_eq_zero_iff.1 (by linear_combination ψ.val 1 * h₁₀ - ψ.val 0 * h₁₁)
  have ha : ψ.val 0 = 0 := by linear_combination h₂₁ + (c₂ - 1) * hb
  refine toFin2ℂEquiv.injective (funext fun i => ?_)
  fin_cases i <;> assumption

/-- A submodule of `RightHandedWeyl` stable under `rep` is either `⊥` or everything. -/
lemma eq_bot_or_eq_top_of_rep_mem (p : Submodule ℂ RightHandedWeyl)
    (h : ∀ (M : SL(2,ℂ)) (ψ : RightHandedWeyl), ψ ∈ p → rep M ψ ∈ p) :
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

/-- Schur's lemma for right-handed Weyl fermions. -/
lemma end_eq_smul_id_of_commute_rep {T : Module.End ℂ RightHandedWeyl}
    (hT : ∀ M : SL(2,ℂ), T ∘ₗ rep M = rep M ∘ₗ T) : ∃ μ : ℂ, T = μ • LinearMap.id := by
  obtain ⟨μ, hμ⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := rep)).2 ⟨T, hT⟩
  exact ⟨μ, congrArg Representation.IntertwiningMap.toLinearMap hμ.symm⟩

end RightHandedWeyl

end
end Fermion
