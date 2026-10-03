/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.AdjointClosed
/-!
# Equivariant maps out of tensors with four-vector indices

## i. Overview

A family of vectors of a complex module `B`, indexed by `n` spacetime directions and moved by a
representation `repLorentz` of `SL(2,ℂ)` with one factor of the Lorentz matrix per index, is
packaged as a linear map `f` out of the complex Lorentz tensors with `n` contravariant indices,
and `IsLorentzCovariant n B repLorentz f` says that `f` is equivariant (A). The rank-specific
files of this folder classify the Lorentz invariants in the range of such a map.

The components of a tensor, relabelled by `Fin 1 ⊕ Fin 3` in each slot, are a coefficient tensor,
`coeffEquiv` (B), on which `SL(2,ℂ)` acts by `Invariants.act`. An invariant tensor therefore has
an invariant coefficient tensor, `Invariants.IsInvariantCoeff`, and a classification of the
invariant coefficient tensors is a classification of the invariants in the range of `f` (C).

A family `T` of vectors indexed by `n` directions is the map `ofComponents T`, sending each basis
tensor to the matching vector, and it is equivariant exactly when the vectors obey the
transformation law of the components of a tensor (D),

`repLorentz g (T l) = ∑_a (∏ i, Λ(g)_{a i, l i}) • T a`,

with `l` free and `a` summed, and the summed index first in each factor of the Lorentz matrix
`Λ(g)` of `g`.

## ii. Key results

- `Lorentz.IsLorentzCovariant` : equivariant maps out of tensors with `n` four-vector indices.
- `Lorentz.coeffEquiv` : the components of such a tensor, as a coefficient tensor.
- `Lorentz.invariant_iff_isInvariantCoeff` : a tensor is invariant exactly when its coefficient
  tensor is.
- `Lorentz.IsLorentzCovariant.reducesInvariantsTo_span` : a spanning set of the invariant
  coefficient tensors gives a reduction of the invariants of the range.
- `Lorentz.isLorentzCovariant_ofComponents_iff` : the map of a family is equivariant exactly when
  the family obeys the transformation law.

## iii. Table of contents

- A. Equivariant maps
- B. Coefficient tensors
- C. The reduction to invariant coefficient tensors
- D. Maps from components

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. Equivariant maps

-/

/-- A family with `n` four-vector indices `T^{μ₁ ⋯ μₙ}` in a representation `repLorentz` of
  `SL(2,ℂ)`: an equivariant linear map out of the complex Lorentz tensors with `n` contravariant
  indices. -/
abbrev IsLorentzCovariant (n : ℕ) (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (f : ℂT(fun _ : Fin n => Color.up) →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant (fun _ => .up) repLorentz f

/-- A sum over families of two four-vector indices is a double sum. -/
lemma sum_pi_fin_two {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, f ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 1 ⊕ Fin 3, f d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3), f ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 1 ⊕ Fin 3) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-!

## B. Coefficient tensors

-/

section Coefficients

variable {n : ℕ}

/-- The component indices of a tensor with `n` contravariant indices, relabelled by
  `Fin 1 ⊕ Fin 3` in each slot. -/
def vectorIdx (n : ℕ) :
    ComponentIdx (S := complexLorentzTensor) (fun _ : Fin n => Color.up)
      ≃ (Fin n → Fin 1 ⊕ Fin 3) :=
  Equiv.piCongrRight fun _ => (finSumFinEquiv (m := 1) (n := 3)).symm

lemma vectorIdx_symm_apply (d : Fin n → Fin 1 ⊕ Fin 3) (i : Fin n) :
    (vectorIdx n).symm d i = finSumFinEquiv (m := 1) (n := 3) (d i) := rfl

/-- The components of a tensor with `n` contravariant indices, as a coefficient tensor. -/
noncomputable def coeffEquiv (n : ℕ) :
    ℂT(fun _ : Fin n => Color.up) ≃ₗ[ℂ] ((Fin n → Fin 1 ⊕ Fin 3) → ℂ) :=
  (Tensor.basis _).equivFun.trans (LinearEquiv.funCongrLeft ℂ ℂ (vectorIdx n).symm)

lemma coeffEquiv_apply (t : ℂT(fun _ : Fin n => Color.up)) (d : Fin n → Fin 1 ⊕ Fin 3) :
    coeffEquiv n t d = (Tensor.basis _).repr t ((vectorIdx n).symm d) := rfl

/-- The tensor with coefficient tensor `c` is the combination of the basis tensors with those
  coefficients. -/
lemma coeffEquiv_symm_apply (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    (coeffEquiv n).symm c = ∑ d, c d • Tensor.basis _ ((vectorIdx n).symm d) := by
  refine (coeffEquiv n).injective (funext fun d => ?_)
  rw [LinearEquiv.apply_symm_apply, coeffEquiv_apply, map_sum, Finset.sum_apply']
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    EmbeddingLike.apply_eq_iff_eq, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The action of `g` on tensors is the action `act` of its Lorentz matrix on coefficient
  tensors. -/
lemma coeffEquiv_smul (g : SL(2,ℂ)) (t : ℂT(fun _ : Fin n => Color.up)) :
    coeffEquiv n (g • t) = act (SL2C.toLorentzGroup g).1 (coeffEquiv n t) := by
  funext a
  rw [coeffEquiv_apply, basis_repr_smul, act, ← (vectorIdx n).symm.sum_comp]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_comm, coeffEquiv_apply]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [vectorIdx_symm_apply, vectorIdx_symm_apply]
  exact toMatrix_rep_up_apply g (a i) (d i)

/-- A tensor is invariant exactly when its coefficient tensor is an invariant coefficient
  tensor. -/
lemma invariant_iff_isInvariantCoeff (t : ℂT(fun _ : Fin n => Color.up)) :
    (∀ g : SL(2,ℂ), g • t = t) ↔ IsInvariantCoeff (coeffEquiv n t) := by
  refine forall_congr' fun g => ?_
  rw [← coeffEquiv_smul, (coeffEquiv n).injective.eq_iff]

end Coefficients

/-!

## C. The reduction to invariant coefficient tensors

-/

namespace IsLorentzCovariant

variable {n : ℕ} {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT(fun _ : Fin n => Color.up) →ₗ[ℂ] B}

/-- When the invariant coefficient tensors lie in the span of the coefficient tensors `K j`, the
  invariants of the range of `f` reduce to the span of the images of the tensors with those
  coefficients. -/
lemma reducesInvariantsTo_span (hf : IsLorentzCovariant n B repLorentz f) {ι : Type*}
    (K : ι → (Fin n → Fin 1 ⊕ Fin 3) → ℂ)
    (hK : ∀ c, IsInvariantCoeff c → c ∈ Submodule.span ℂ (Set.range K)) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f)
      (Submodule.span ℂ (Set.range fun j => f ((coeffEquiv n).symm (K j)))) := by
  have h := hf.reducesInvariantsTo_map (complexLorentzTensor.isAdjointClosed _)
    ((Submodule.span ℂ (Set.range K)).map (coeffEquiv n).symm.toLinearMap) fun t ht => by
      rw [← (coeffEquiv n).symm_apply_apply t]
      exact Submodule.mem_map_of_mem (hK _ ((invariant_iff_isInvariantCoeff t).1 ht))
  rwa [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp] at h

/-- When the only invariant coefficient tensor is zero, the range of `f` reduces to `⊥`. -/
lemma reducesInvariantsTo_bot_of_isInvariantCoeff (hf : IsLorentzCovariant n B repLorentz f)
    (hK : ∀ c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ, IsInvariantCoeff c → c = 0) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ :=
  hf.reducesInvariantsTo_bot (complexLorentzTensor.isAdjointClosed _) fun t ht =>
    (coeffEquiv n).injective (by rw [hK _ ((invariant_iff_isInvariantCoeff t).1 ht), map_zero])

/-- When the only invariant coefficient tensor is zero, so is every Lorentz invariant in the
  range of `f`. -/
lemma eq_zero_of_isInvariantCoeff (hf : IsLorentzCovariant n B repLorentz f)
    (hK : ∀ c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ, IsInvariantCoeff c → c = 0) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  hf.eq_zero_of_invariant (complexLorentzTensor.isAdjointClosed _) (fun t ht =>
    (coeffEquiv n).injective (by rw [hK _ ((invariant_iff_isInvariantCoeff t).1 ht), map_zero]))
    hx hinv

end IsLorentzCovariant

/-!

## D. Maps from components

-/

section Components

variable {n : ℕ} {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The linear map out of the tensors with `n` contravariant indices sending the basis tensor
  with components `d` to `T d`. -/
noncomputable def ofComponents (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    ℂT(fun _ : Fin n => Color.up) →ₗ[ℂ] B :=
  (Tensor.basis _).constr ℂ fun φ => T (vectorIdx n φ)

/-- `ofComponents T` contracts the coefficient tensor of its argument with `T`. -/
lemma ofComponents_coeffEquiv_symm (T : (Fin n → Fin 1 ⊕ Fin 3) → B)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    ofComponents T ((coeffEquiv n).symm c) = ∑ d, c d • T d := by
  rw [coeffEquiv_symm_apply, map_sum]
  simp [ofComponents]

/-- The range of `ofComponents T` is the span of the vectors `T d`. -/
lemma range_ofComponents (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    LinearMap.range (ofComponents T) = Submodule.span ℂ (Set.range T) := by
  rw [ofComponents, Module.Basis.constr_range]
  exact congrArg _ ((vectorIdx n).surjective.range_comp T)

/-- `ofComponents` of a sum of families is the sum of the maps. -/
lemma ofComponents_sum {ι : Type*} (s : Finset ι) (T : ι → (Fin n → Fin 1 ⊕ Fin 3) → B) :
    ofComponents (fun d => ∑ i ∈ s, T i d) = ∑ i ∈ s, ofComponents (T i) :=
  (Tensor.basis _).ext fun φ => by simp [ofComponents, LinearMap.sum_apply]

/-- A linear map applied after `ofComponents T` is `ofComponents` of its values on the
  components. -/
lemma comp_ofComponents {B' : Type*} [AddCommGroup B'] [Module ℂ B'] (σ : B →ₗ[ℂ] B')
    (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    σ ∘ₗ ofComponents T = ofComponents fun d => σ (T d) :=
  (Tensor.basis _).ext fun φ => by simp [ofComponents]

/-- The map of a family is equivariant exactly when the family obeys the transformation law of
  the components of a tensor with `n` four-vector indices. -/
lemma isLorentzCovariant_ofComponents_iff {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    IsLorentzCovariant n B repLorentz (ofComponents T) ↔
      ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
        (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a := by
  have hmat (g : SL(2,ℂ)) (a l : Fin n → Fin 1 ⊕ Fin 3) :
      ∏ i, LinearMap.toMatrix (complexLorentzTensor.basis Color.up)
        (complexLorentzTensor.basis Color.up) (complexLorentzTensor.rep Color.up g)
        ((vectorIdx n).symm a i) ((vectorIdx n).symm l i)
      = ∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ) :=
    Finset.prod_congr rfl fun i _ => by
      rw [vectorIdx_symm_apply, vectorIdx_symm_apply]
      exact toMatrix_rep_up_apply g (a i) (l i)
  constructor
  · intro hf g l
    have h := hf.equivariant g (Tensor.basis _ ((vectorIdx n).symm l))
    rw [smul_basis_eq_sum, ← (vectorIdx n).symm.sum_comp, map_sum] at h
    simpa [ofComponents, hmat] using h.symm
  · intro hT
    refine isEquivariant_constr _ fun g φ => ?_
    obtain ⟨l, rfl⟩ := (vectorIdx n).symm.surjective φ
    rw [Equiv.apply_symm_apply, hT, ← (vectorIdx n).symm.sum_comp]
    simp only [Equiv.apply_symm_apply, hmat]

end Components

end Lorentz
