/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.TensorSpecies.Basic
/-!

# Species whose bases at dual colors are dual bases

## i. Overview

This file defines `HasContrDualBases`: species whose basis at `S.τ c` is dual to the basis at `c`
under the pairing `S.contr c`.

A matching `e : basisIdx (S.τ c) ≃ basisIdx c` satisfies the δ law (`IsContrDualMatching`) if
`S.contr c (b c x₁ ⊗ₜ b (S.τ c) x₂) = if x₁ = e x₂ then 1 else 0`. The class asks for one such
matching at every color, so the label types need only be in bijection.

Over a nontrivial ring the matching is unique (`IsContrDualMatching.unique`). Hence
`contrDualIdxEquiv`, although picked by choice, is the only matching, so nothing depends on the
choice. A concrete species identifies it through `contrDualIdxEquiv_eq_of_isContrDualMatching`,
and the double-dual law `contrDualIdxEquiv_tau` is a theorem.

The contraction functionals are the dual basis of `b c` (`contr_tmul_basis_eq_dualBasis`).
Contracted basis vectors have δ coefficients (`Pure.contrPCoeff_basisVector`), and components of a
contraction are single sums (`contrT_basis_repr_apply_eq_sum_dual`).

## ii. Key results

- `TensorSpecies.IsContrDualMatching.unique` : the δ law determines the matching.
- `TensorSpecies.HasContrDualBases` : the class.
- `TensorSpecies.HasContrDualBases.contrDualIdxEquiv` : the matching of the labels at `S.τ c`
    with those at `c`.
- `TensorSpecies.HasContrDualBases.contr_basis_eq_ite` : the δ law for `contrDualIdxEquiv`.
- `TensorSpecies.HasContrDualBases.contrDualIdxEquiv_eq_of_isContrDualMatching` : any matching
    satisfying the δ law is `contrDualIdxEquiv`.
- `TensorSpecies.HasContrDualBases.contrDualIdxEquiv_tau` : the matching at `S.τ c` is the
    inverse of the one at `c`, through `S.τ (S.τ c) = c`.
- `TensorSpecies.HasContrDualBases.contr_tmul_basis_eq_dualBasis` : contracting with a basis vector
    at `S.τ c` is an element of `Module.Basis.dualBasis`.

## iii. Table of contents

- A. Matchings satisfying the δ law
- B. The class
- C. The matching
- D. The double dual
- E. The dual basis

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open Module
open scoped TensorProduct

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}

/-!

## A. Matchings satisfying the δ law

-/

/-- A matching `e` of the basis labels at `S.τ c` with those at `c` satisfies the δ law:
  contracting a basis vector at `c` with one at `S.τ c` gives `1` if `e` matches their labels and
  `0` otherwise. -/
def IsContrDualMatching (S : TensorSpecies k C G V basisIdx rep b) (c : C)
    (e : basisIdx (S.τ c) ≃ basisIdx c) : Prop :=
  ∀ x₁ x₂, S.contr c (b c x₁ ⊗ₜ[k] b (S.τ c) x₂) = if x₁ = e x₂ then 1 else 0

/-- Over a nontrivial ring the δ law determines the matching: the label matched with `x₂` is the
  one whose basis vector pairs with `b (S.τ c) x₂` to `1`. -/
lemma IsContrDualMatching.unique [Nontrivial k] {S : TensorSpecies k C G V basisIdx rep b}
    {c : C} {e e' : basisIdx (S.τ c) ≃ basisIdx c}
    (he : IsContrDualMatching S c e) (he' : IsContrDualMatching S c e') : e = e' := by
  ext x₂
  have h := (he (e x₂) x₂).symm.trans (he' (e x₂) x₂)
  by_contra hne
  simp [hne] at h

/-!

## B. The class

-/

/-- A tensor species whose basis at `S.τ c` is dual to its basis at `c` under the pairing
  `S.contr c`: for every color some matching of the labels satisfies the δ law. -/
class HasContrDualBases (S : TensorSpecies k C G V basisIdx rep b) : Prop where
  /-- At every color, some matching of the labels at `S.τ c` with those at `c` satisfies the δ
    law. -/
  exists_matching : ∀ c, ∃ e, IsContrDualMatching S c e

namespace HasContrDualBases

variable {S : TensorSpecies k C G V basisIdx rep b} [HasContrDualBases S]

/-!

## C. The matching

-/

variable (S) in
/-- A matching of the basis labels at `S.τ c` with those at `c` satisfying the δ law, chosen by
  `Classical.choose`. Over a nontrivial ring it is the only one
  (`contrDualIdxEquiv_eq_of_isContrDualMatching`). -/
noncomputable def contrDualIdxEquiv (c : C) : basisIdx (S.τ c) ≃ basisIdx c :=
  Classical.choose (exists_matching (S := S) c)

/-- The δ law for `contrDualIdxEquiv`. -/
lemma contr_basis_eq_ite (c : C) (x₁ : basisIdx c) (x₂ : basisIdx (S.τ c)) :
    S.contr c (b c x₁ ⊗ₜ[k] b (S.τ c) x₂) =
      if x₁ = contrDualIdxEquiv S c x₂ then 1 else 0 :=
  Classical.choose_spec (exists_matching (S := S) c) x₁ x₂

/-- Any matching satisfying the δ law is `contrDualIdxEquiv`. This is how a concrete species
  identifies its matching. -/
lemma contrDualIdxEquiv_eq_of_isContrDualMatching [Nontrivial k] {c : C}
    {e : basisIdx (S.τ c) ≃ basisIdx c} (he : IsContrDualMatching S c e) :
    contrDualIdxEquiv S c = e :=
  IsContrDualMatching.unique (contr_basis_eq_ite c) he

/-!

## D. The double dual

-/

/-- The matching at `S.τ c` is the inverse of the one at `c`, once `S.τ (S.τ c)` is identified
  with `c` by `S.τ_τ_apply`. The inverse matching satisfies the δ law at `S.τ c` by
  `contr_tmul_symm`, so uniqueness identifies the two. -/
lemma contrDualIdxEquiv_tau [Nontrivial k] (c : C) (x : basisIdx (S.τ (S.τ c))) :
    contrDualIdxEquiv S (S.τ c) x =
      (contrDualIdxEquiv S c).symm (basisIdxCongr (S.τ_τ_apply c) x) := by
  suffices h : IsContrDualMatching S (S.τ c)
      ((basisIdxCongr (S.τ_τ_apply c)).trans (contrDualIdxEquiv S c).symm) by
    rw [contrDualIdxEquiv_eq_of_isContrDualMatching h]
    rfl
  intro y x
  have key := S.contr_tmul_symm c (b c (basisIdxCongr (S.τ_τ_apply c) x)) (b (S.τ c) y)
  rw [equivCast_basis (S.τ_τ_apply c).symm, basisIdxCongr_apply_apply, basisIdxCongr_rfl,
    contr_basis_eq_ite] at key
  rw [← key, Equiv.trans_apply]
  exact if_congr (by rw [Equiv.eq_symm_apply, eq_comm]) rfl rfl

/-!

## E. The dual basis

-/

/-- The functional `v ↦ S.contr c (v ⊗ₜ b (S.τ c) x)` is the element of `(b c).dualBasis` at the
  label matched with `x`. -/
lemma contr_tmul_basis_eq_dualBasis (c : C) (x : basisIdx (S.τ c)) (v : V c) :
    S.contr c (v ⊗ₜ[k] b (S.τ c) x) = (b c).dualBasis (contrDualIdxEquiv S c x) v := by
  have h : (S.contr c).toLinearMap ∘ₗ (TensorProduct.mk k (V c) (V (S.τ c))).flip (b (S.τ c) x) =
      (b c).dualBasis (contrDualIdxEquiv S c x) := by
    refine (b c).ext fun j => ?_
    simp [contr_basis_eq_ite, Finsupp.single_apply]
  exact LinearMap.congr_fun h v

end HasContrDualBases

end TensorSpecies
