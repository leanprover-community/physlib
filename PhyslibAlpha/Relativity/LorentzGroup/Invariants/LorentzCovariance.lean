/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.AdjointClosed
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
`Λ(g)` of `g`. Permuting the slots by `permT σ` reads the coefficient tensor and the family at
permuted index vectors (`permT_coeffEquiv_symm`, `ofComponents_comp_permT`).

## ii. Key results

- `Lorentz.IsLorentzCovariant` : equivariant maps out of tensors with `n` four-vector indices.
- `Lorentz.coeffEquiv` : the components of such a tensor, as a coefficient tensor.
- `Lorentz.invariant_iff_isInvariantCoeff` : a tensor is invariant exactly when its coefficient
  tensor is.
- `Lorentz.IsLorentzCovariant.reducesInvariantsTo_span` : a spanning set of the invariant
  coefficient tensors gives a reduction of the invariants of the range.
- `Lorentz.isLorentzCovariant_ofComponents_iff` : the map of a family is equivariant exactly when
  the family obeys the transformation law.
- `Lorentz.IsLorentzCovariant.mul_fixed`, `Lorentz.IsLorentzCovariant.mul_vector` : products of a
  family with a Lorentz-inert element or with a Lorentz vector.

## iii. Table of contents

- A. Equivariant maps
- B. Coefficient tensors
- C. The reduction to invariant coefficient tensors
- D. Maps from components
- E. Products of families in an algebra

## iv. References

* None.

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

/-- A sum over families of no four-vector indices is its single term. -/
lemma sum_pi_fin_zero {M : Type*} [AddCommMonoid M] (f : (Fin 0 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 0 → Fin 1 ⊕ Fin 3, f d = f ![] :=
  Finset.sum_eq_single (![] : Fin 0 → Fin 1 ⊕ Fin 3)
    (fun b _ hb => absurd (Subsingleton.elim b ![]) hb)
    (fun hb => absurd (Finset.mem_univ _) hb)

/-- A sum over families of one four-vector index is a single sum. -/
lemma sum_pi_fin_one {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 1 → Fin 1 ⊕ Fin 3, f d = ∑ x : Fin 1 ⊕ Fin 3, f ![x] :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 1 ⊕ Fin 3)) _ _ fun d => by
    congr 1
    funext i
    fin_cases i
    simp

/-- A family of one four-vector index is the tuple of its own entry. -/
lemma vecCons_fin_one_eta (l : Fin 1 → Fin 1 ⊕ Fin 3) : ![l 0] = l := by
  funext i
  fin_cases i
  rfl

/-- A sum over families of three four-vector indices is a triple sum. -/
lemma sum_pi_fin_three {M : Type*} [AddCommMonoid M] (f : (Fin 3 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 3 → Fin 1 ⊕ Fin 3, f d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3, f ![x, y, z] := by
  rw [show (∑ d : Fin 3 → Fin 1 ⊕ Fin 3, f d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
        f ![p.1, p.2.1, p.2.2] from
      Fintype.sum_equiv
        { toFun := fun d => (d 0, d 1, d 2)
          invFun := fun p => ![p.1, p.2.1, p.2.2]
          left_inv := fun d => by funext i; fin_cases i <;> simp
          right_inv := fun p => by simp } _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp]
  simp only [Fintype.sum_prod_type]

/-!

## B. Coefficient tensors

-/

section Coefficients

variable {n : ℕ}

/-- The component indices of a tensor with `n` contravariant indices, which are labelled by
  `Fin 1 ⊕ Fin 3` in each slot. -/
def vectorIdx (n : ℕ) :
    ComponentIdx (S := complexLorentzTensor) (fun _ : Fin n => Color.up)
      ≃ (Fin n → Fin 1 ⊕ Fin 3) :=
  Equiv.refl _

lemma vectorIdx_symm_apply (d : Fin n → Fin 1 ⊕ Fin 3) (i : Fin n) :
    (vectorIdx n).symm d i = d i := rfl

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

/-- Permuting the slots of a tensor by `σ` permutes its coefficient tensor: slot `i` of
  `permT σ h t` holds slot `σ i` of `t`, so the new coefficient at `d` is the old one at
  `d ∘ σ.symm`. -/
lemma permT_coeffEquiv_symm (σ : Equiv.Perm (Fin n))
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    permT σ h ((coeffEquiv n).symm c) = (coeffEquiv n).symm fun d => c (d ∘ σ.symm) := by
  rw [coeffEquiv_symm_apply, coeffEquiv_symm_apply, map_sum]
  simp only [map_smul, permT_basis]
  rw [← (Equiv.arrowCongr σ (Equiv.refl (Fin 1 ⊕ Fin 3))).sum_comp]
  refine Finset.sum_congr rfl fun d _ => ?_
  have he : Equiv.arrowCongr σ (Equiv.refl (Fin 1 ⊕ Fin 3)) d = d ∘ σ.symm := rfl
  rw [he]
  congr 2
  funext i
  simp [vectorIdx_symm_apply]

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

/-- Precomposing `ofComponents T` with the slot permutation `permT σ` reads the family at the
  permuted index vectors `d ∘ σ`. -/
lemma ofComponents_comp_permT (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    ofComponents T ∘ₗ permT σ h = ofComponents fun d => T (d ∘ σ) :=
  (Tensor.basis _).ext fun φ => by
    rw [LinearMap.comp_apply, permT_basis]
    simp only [ofComponents, Module.Basis.constr_basis]
    rfl

/-- A family antisymmetric under reading its index vectors through `σ` gives a map
  antisymmetric under `permT σ`. -/
lemma ofComponents_comp_permT_eq_neg (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B} (hT : ∀ d, T (d ∘ σ) = -T d) :
    ofComponents T ∘ₗ permT σ h = -ofComponents T := by
  rw [ofComponents_comp_permT]
  exact (Tensor.basis _).ext fun φ => by simp [ofComponents, hT]

/-- A family symmetric under reading its index vectors through `σ` gives a map invariant under
  `permT σ`. -/
lemma ofComponents_comp_permT_eq_self (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B} (hT : ∀ d, T (d ∘ σ) = T d) :
    ofComponents T ∘ₗ permT σ h = ofComponents T := by
  rw [ofComponents_comp_permT]
  exact congrArg ofComponents (funext hT)

/-- The map of a family is equivariant exactly when the family obeys the transformation law of
  the components of a tensor with `n` four-vector indices. -/
lemma isLorentzCovariant_ofComponents_iff {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    IsLorentzCovariant n B repLorentz (ofComponents T) ↔
      ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
        (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a := by
  constructor
  · intro hf g l
    have h := hf.equivariant g (Tensor.basis _ ((vectorIdx n).symm l))
    rw [smul_basis_eq_sum, ← (vectorIdx n).symm.sum_comp, map_sum] at h
    simpa [ofComponents, vectorIdx, LorentzGroup.toComplex] using h.symm
  · intro hT
    refine isEquivariant_constr _ fun g φ => ?_
    obtain ⟨l, rfl⟩ := (vectorIdx n).symm.surjective φ
    rw [Equiv.apply_symm_apply, hT, ← (vectorIdx n).symm.sum_comp]
    simp [vectorIdx, LorentzGroup.toComplex]

end Components

/-!

## E. Products of families in an algebra

When the families take values in an algebra on which `SL(2,ℂ)` acts multiplicatively, a family
times a Lorentz-inert element keeps its rank, and a rank-two family times a Lorentz vector is a
rank-three family.

-/

section Products

variable {B : Type*} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- Multiplying a Lorentz tensor family by a Lorentz-inert element gives a family of the
  same rank, the element riding through the transformation law untouched. -/
lemma IsLorentzCovariant.mul_fixed {n : ℕ}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B} (hT : IsLorentzCovariant n B repLorentz (ofComponents T))
    {y : B} (hy : ∀ g : SL(2,ℂ), repLorentz g y = y) :
    IsLorentzCovariant n B repLorentz (ofComponents fun d => T d * y) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [hmul, (isLorentzCovariant_ofComponents_iff T).1 hT g l, hy g, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => smul_mul_assoc _ _ _

/-- A rank-two family against a Lorentz vector is a rank-three family, the two covector
  indices of the first factor and the single index of the second make three. -/
lemma IsLorentzCovariant.mul_vector
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B} (hT : IsLorentzCovariant 2 B repLorentz (ofComponents T))
    {U : (Fin 1 ⊕ Fin 3) → B}
    (hU : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3), repLorentz g (U μ)
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ) • U ν) :
    IsLorentzCovariant 3 B repLorentz
      (ofComponents fun d : Fin 3 → Fin 1 ⊕ Fin 3 => T ![d 0, d 1] * U (d 2)) := by
  refine (isLorentzCovariant_ofComponents_iff _).2 fun g l => ?_
  rw [hmul, (isLorentzCovariant_ofComponents_iff T).1 hT g ![l 0, l 1], hU g (l 2),
    sum_pi_fin_two, sum_pi_fin_three, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  all_goals simp [Fin.prod_univ_two, Fin.prod_univ_three, mul_assoc]

end Products

end Lorentz
