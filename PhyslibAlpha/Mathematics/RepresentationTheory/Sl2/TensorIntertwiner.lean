/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Schur
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorDecomposition

/-!

# Intertwiners out of a tensor product of standard sl₂ modules

Linear maps `V(m) ⊗ V(n) → V(p)` compatible with the diagonal `sl₂` action.

## i. Overview

A tensor intertwiner is a linear map `φ : V(m) ⊗ V(n) → V(p)` that carries the diagonal raising,
lowering and weight operators of `V(m) ⊗ V(n)` to those of `V(p)`. Composing with the inverse of
the Clebsch–Gordan isomorphism `cgEquiv : V(m) ⊗ V(n) ≃ ⨁_j V(m + n - 2j)` gives, on each summand,
an intertwiner `V(m + n - 2j) → V(p)`. By Schur's lemma these vanish unless `m + n - 2j = p`, and
the summand with `m + n - 2j = p` contributes a scalar multiple of the identity. Hence:

- if `p` is not of the form `m + n - 2j` with `j ≤ min m n`, every tensor intertwiner is zero;
- if `p = m + n - 2j`, every tensor intertwiner is a scalar multiple of the projection `cgProj`
  onto the summand `V(m + n - 2j)`, and this projection is not zero.

In physics notation (`m = 2j₁`, `n = 2j₂`, `p = 2J`) the condition is the triangle rule
`|j₁ - j₂| ≤ J ≤ j₁ + j₂` together with `j₁ + j₂ - J ∈ ℕ`.

## ii. Key results

- `IsTensorIntertwiner` is the predicate for tensor intertwiners.
- `cgProj` is the projection onto a summand of the Clebsch–Gordan decomposition, and
  `cgProj_isTensorIntertwiner` shows that it is a tensor intertwiner.
- `IsTensorIntertwiner.eq_zero_of_forall_ne` is the selection rule.
- `IsTensorIntertwiner.exists_eq_smul_cgProj` shows that a tensor intertwiner onto
  `V(m + n - 2j)` is a multiple of `cgProj`.

## iii. Table of contents

- A. Tensor intertwiners
  - A.1. Definition and closure properties
  - A.2. The Clebsch–Gordan projections
  - A.3. Restriction to the summands
  - A.4. Selection rule and uniqueness

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Tensor intertwiners

### A.1. Definition and closure properties

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct DirectSum

open StandardSl2Module

variable {K : Type*} [Field K] {m n p : ℕ}

/-- A linear map `V(m) ⊗ V(n) → V(p)` is a tensor intertwiner if it carries the diagonal raising,
lowering and weight operators on `V(m) ⊗ V(n)` to those on `V(p)`. -/
structure IsTensorIntertwiner
    (φ : StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K] StandardSl2Module K p) : Prop where
  comm_E : φ ∘ₗ tensorE m n = ρE ∘ₗ φ
  comm_F : φ ∘ₗ tensorF m n = ρF ∘ₗ φ
  comm_H : φ ∘ₗ tensorH m n = ρH ∘ₗ φ

namespace IsTensorIntertwiner

variable {φ ψ : StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K] StandardSl2Module K p}

/-- Scalar multiples of tensor intertwiners are tensor intertwiners. -/
lemma smul (hφ : IsTensorIntertwiner φ) (c : K) : IsTensorIntertwiner (c • φ) where
  comm_E := by rw [LinearMap.smul_comp, hφ.comm_E, LinearMap.comp_smul]
  comm_F := by rw [LinearMap.smul_comp, hφ.comm_F, LinearMap.comp_smul]
  comm_H := by rw [LinearMap.smul_comp, hφ.comm_H, LinearMap.comp_smul]

/-- Sums of tensor intertwiners are tensor intertwiners. -/
lemma add (hφ : IsTensorIntertwiner φ) (hψ : IsTensorIntertwiner ψ) :
    IsTensorIntertwiner (φ + ψ) where
  comm_E := by rw [LinearMap.add_comp, hφ.comm_E, hψ.comm_E, LinearMap.comp_add]
  comm_F := by rw [LinearMap.add_comp, hφ.comm_F, hψ.comm_F, LinearMap.comp_add]
  comm_H := by rw [LinearMap.add_comp, hφ.comm_H, hψ.comm_H, LinearMap.comp_add]

end IsTensorIntertwiner

/-!

### A.2. The Clebsch–Gordan projections

-/

/-- The component of a direct sum commutes with a summand-wise endomorphism. -/
lemma component_sumEnd (A : ∀ j, Module.End K (CGSummand K m n j)) (j : Fin (min m n + 1))
    (y : CGSum K m n) :
    DirectSum.component K _ (CGSummand K m n) j (sumEnd A y) =
      A j (DirectSum.component K _ (CGSummand K m n) j y) := by
  rw [← DirectSum.apply_eq_component, ← DirectSum.apply_eq_component]
  exact DFinsupp.mapRange_apply _ (fun i => map_zero (A i)) y j

variable [CharZero K]

/-- The projection of `V(m) ⊗ V(n)` onto the summand `V(m + n - 2j)` of the Clebsch–Gordan
decomposition. -/
def cgProj (hmn : 0 < m + n) (j : Fin (min m n + 1)) :
    StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K]
      StandardSl2Module K (m + n - 2 * (j : ℕ)) :=
  DirectSum.component K _ (CGSummand K m n) j ∘ₗ (cgEquiv (K := K) hmn).toLinearMap

lemma cgProj_apply (hmn : 0 < m + n) (j : Fin (min m n + 1))
    (x : StandardSl2Module K m ⊗[K] StandardSl2Module K n) :
    cgProj hmn j x = DirectSum.component K _ (CGSummand K m n) j (cgEquiv hmn x) := rfl

/-- The projections are tensor intertwiners. -/
lemma cgProj_isTensorIntertwiner (hmn : 0 < m + n) (j : Fin (min m n + 1)) :
    IsTensorIntertwiner (cgProj (K := K) hmn j) where
  comm_E := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, cgProj_apply, cgEquiv_tensorE, component_sumEnd]
  comm_F := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, cgProj_apply, cgEquiv_tensorF, component_sumEnd]
  comm_H := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, cgProj_apply, cgEquiv_tensorH, component_sumEnd]

/-- The projection sends the preimage of the highest-weight vector of the `j`-th summand to that
vector; in particular it is not zero. -/
lemma cgProj_cgEquiv_symm_lof (hmn : 0 < m + n) (j : Fin (min m n + 1))
    (z : CGSummand K m n j) :
    cgProj hmn j ((cgEquiv hmn).symm (DirectSum.lof K _ (CGSummand K m n) j z)) = z := by
  rw [cgProj_apply, LinearEquiv.apply_symm_apply, DirectSum.component.lof_self]

lemma cgProj_ne_zero (hmn : 0 < m + n) (j : Fin (min m n + 1)) :
    cgProj (K := K) hmn j ≠ 0 := by
  intro h
  have := cgProj_cgEquiv_symm_lof (K := K) hmn j (vNat _ 0)
  rw [h, LinearMap.zero_apply, vNat_eq_v (Nat.zero_le _)] at this
  have h0 := congrFun this ⟨0, Nat.succ_pos _⟩
  simp [StandardSl2Module.v] at h0

/-!

### A.3. Restriction to the summands

-/

section Restrict

variable (hmn : 0 < m + n)

lemma cgEquiv_symm_sumEnd_E (y : CGSum K m n) :
    (cgEquiv hmn).symm (sumEnd (fun _ => ρE) y) = tensorE m n ((cgEquiv hmn).symm y) := by
  rw [LinearEquiv.symm_apply_eq, cgEquiv_tensorE, LinearEquiv.apply_symm_apply]

lemma cgEquiv_symm_sumEnd_F (y : CGSum K m n) :
    (cgEquiv hmn).symm (sumEnd (fun _ => ρF) y) = tensorF m n ((cgEquiv hmn).symm y) := by
  rw [LinearEquiv.symm_apply_eq, cgEquiv_tensorF, LinearEquiv.apply_symm_apply]

lemma cgEquiv_symm_sumEnd_H (y : CGSum K m n) :
    (cgEquiv hmn).symm (sumEnd (fun _ => ρH) y) = tensorH m n ((cgEquiv hmn).symm y) := by
  rw [LinearEquiv.symm_apply_eq, cgEquiv_tensorH, LinearEquiv.apply_symm_apply]

/-- The restriction of a linear map on `V(m) ⊗ V(n)` to the `j`-th summand of the
Clebsch–Gordan decomposition. -/
def cgRestrict
    (φ : StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K] StandardSl2Module K p)
    (j : Fin (min m n + 1)) : CGSummand K m n j →ₗ[K] StandardSl2Module K p :=
  φ ∘ₗ (cgEquiv hmn).symm.toLinearMap ∘ₗ DirectSum.lof K _ (CGSummand K m n) j

namespace IsTensorIntertwiner

variable {φ : StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K] StandardSl2Module K p}

/-- The restriction of a tensor intertwiner to a summand is an intertwiner. -/
lemma cgRestrict_isIntertwiner (hφ : IsTensorIntertwiner φ) (j : Fin (min m n + 1)) :
    IsIntertwiner (cgRestrict hmn φ j) where
  comm_ρE := LinearMap.ext fun z => by
    have h := sumEnd_lof (K := K) (m := m) (n := n) (fun _ => ρE) j z
    simp only [cgRestrict, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h, cgEquiv_symm_sumEnd_E, ← LinearMap.comp_apply φ (tensorE m n), hφ.comm_E,
      LinearMap.comp_apply]
  comm_ρF := LinearMap.ext fun z => by
    have h := sumEnd_lof (K := K) (m := m) (n := n) (fun _ => ρF) j z
    simp only [cgRestrict, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h, cgEquiv_symm_sumEnd_F, ← LinearMap.comp_apply φ (tensorF m n), hφ.comm_F,
      LinearMap.comp_apply]
  comm_ρH := LinearMap.ext fun z => by
    have h := sumEnd_lof (K := K) (m := m) (n := n) (fun _ => ρH) j z
    simp only [cgRestrict, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h, cgEquiv_symm_sumEnd_H, ← LinearMap.comp_apply φ (tensorH m n), hφ.comm_H,
      LinearMap.comp_apply]

end IsTensorIntertwiner

end Restrict

/-!

### A.4. Selection rule and uniqueness

-/

namespace IsTensorIntertwiner

/-- A linear map on `V(m) ⊗ V(n)` is determined by its restrictions to the summands. -/
lemma eq_of_cgRestrict_eq (hmn : 0 < m + n) {M : Type*} [AddCommGroup M] [Module K M]
    {α β : StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K] M}
    (h : ∀ j, α ∘ₗ (cgEquiv hmn).symm.toLinearMap ∘ₗ DirectSum.lof K _ (CGSummand K m n) j =
      β ∘ₗ (cgEquiv hmn).symm.toLinearMap ∘ₗ DirectSum.lof K _ (CGSummand K m n) j) :
    α = β := by
  have h' : α ∘ₗ (cgEquiv hmn).symm.toLinearMap = β ∘ₗ (cgEquiv hmn).symm.toLinearMap :=
    DirectSum.linearMap_ext K fun j => by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
      exact h j
  refine LinearMap.ext fun x => ?_
  have := LinearMap.congr_fun h' (cgEquiv hmn x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using this

/-- **Selection rule.** If `p` is not of the form `m + n - 2j` with `j ≤ min m n`, every tensor
intertwiner `V(m) ⊗ V(n) → V(p)` is zero. -/
lemma eq_zero_of_forall_ne (hmn : 0 < m + n)
    {φ : StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K] StandardSl2Module K p}
    (hφ : IsTensorIntertwiner φ) (hp : ∀ j : Fin (min m n + 1), m + n - 2 * (j : ℕ) ≠ p) :
    φ = 0 :=
  eq_of_cgRestrict_eq hmn fun j => by
    rw [LinearMap.zero_comp]
    exact (hφ.cgRestrict_isIntertwiner hmn j).eq_zero_of_ne (hp j)

/-- Every tensor intertwiner onto the summand `V(m + n - 2j)` is a scalar multiple of the
projection `cgProj`. -/
lemma exists_eq_smul_cgProj (hmn : 0 < m + n) {j : Fin (min m n + 1)}
    {φ : StandardSl2Module K m ⊗[K] StandardSl2Module K n →ₗ[K]
      StandardSl2Module K (m + n - 2 * (j : ℕ))}
    (hφ : IsTensorIntertwiner φ) : ∃ c : K, φ = c • cgProj hmn j := by
  obtain h := (hφ.cgRestrict_isIntertwiner hmn j).eq_smul_id
  refine ⟨cgRestrict hmn φ j (vNat _ 0) ⟨0, Nat.succ_pos _⟩,
    eq_of_cgRestrict_eq hmn fun i => ?_⟩
  by_cases hij : i = j
  · subst hij
    refine LinearMap.ext fun z => ?_
    have hz := LinearMap.congr_fun h z
    simp only [cgRestrict, LinearMap.comp_apply, LinearEquiv.coe_coe] at hz
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      cgProj_cgEquiv_symm_lof, hz, LinearMap.id_apply]
    rfl
  · have hne : m + n - 2 * (i : ℕ) ≠ m + n - 2 * (j : ℕ) := by
      have hi := i.isLt
      have hj := j.isLt
      have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
      omega
    have h0 := (hφ.cgRestrict_isIntertwiner hmn i).eq_zero_of_ne hne
    refine LinearMap.ext fun z => ?_
    have hz := LinearMap.congr_fun h0 z
    simp only [cgRestrict, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at hz
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply, hz,
      cgProj_apply, LinearEquiv.apply_symm_apply, DirectSum.component.of, hij, dite_false,
      smul_zero]

end IsTensorIntertwiner

end PhyslibAlpha.Sl2
