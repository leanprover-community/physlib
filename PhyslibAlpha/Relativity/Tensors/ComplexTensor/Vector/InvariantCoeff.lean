/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.LorentzGroup.Boosts.Axis
public import PhyslibAlpha.Relativity.SL2C.AxisRotations
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.Reynolds
/-!
# Invariant coefficient tensors of the complex vector representation

Invariant coefficient tensors on spacetime indices, and equivariant maps out of the tensors with
`n` four-vector indices.

## i. Overview

The tensors `ℂT(fun _ : Fin n => .up)` with `n` contravariant indices are the `n`-th tensor power
of the complex vector representation `ComplexVector`. This file holds the machinery that the
classifications of their invariants use: the odd ranks in
`PhyslibAlpha.Relativity.Bispinors.ComplexifiedAction`, rank two in
`PhyslibAlpha.Relativity.Tensors.ComplexTensor.Metrics.Basic` and rank four in
`PhyslibAlpha.Relativity.Tensors.ComplexTensor.Vector.ContractionTensor`.

A real `4 × 4` matrix acts on coefficient tensors one factor per slot, `Invariants.act`, and an
invariant coefficient tensor is one fixed by the Lorentz matrix of every element of `SL(2, ℂ)`
(A). Section B collects sums over index vectors.

The components of a tensor, relabelled by `Fin 1 ⊕ Fin 3` in each slot, are a coefficient tensor,
`coeffEquiv` (C), on which `SL(2,ℂ)` acts by `Invariants.act`. An invariant tensor therefore has
an invariant coefficient tensor, `Invariants.IsInvariantCoeff`, and a classification of the
invariant coefficient tensors is a classification of the invariant tensors (D).

A family `T` of vectors indexed by `n` directions is the map `liftComponents T`, sending each basis
tensor to the matching vector, and it is equivariant exactly when the vectors obey the
transformation law of the components of a tensor (E, `isEquivariant_liftComponents_up_iff`),

`repLorentz g (T l) = ∑_a (∏ i, Λ(g)_{a i, l i}) • T a`,

with `l` free and `a` summed, and the summed index first in each factor of the Lorentz matrix
`Λ(g)` of `g`. Permuting the slots by `permT σ` reads the coefficient tensor and the family at
permuted index vectors (`permT_coeffEquiv_symm`, `liftComponents_comp_permT`). Products of a family
with a Lorentz-inert element or with a Lorentz vector are again such families (F).

## ii. Key results

- `Lorentz.Invariants.IsInvariantCoeff` : invariant coefficient tensors.
- `Lorentz.coeffEquiv` : the components of a tensor with `n` four-vector indices, as a coefficient
  tensor.
- `Lorentz.invariant_iff_isInvariantCoeff` : a tensor is invariant exactly when its coefficient
  tensor is.
- `Lorentz.invariants_tensorRep_le_map` : the invariant tensors come from the invariant
  coefficient tensors.
- `Lorentz.isEquivariant_liftComponents_up_iff` : the map of a family is equivariant exactly when
  the family obeys the transformation law.
- `Lorentz.isEquivariant_liftComponents_up_mul_fixed`,
  `Lorentz.isEquivariant_liftComponents_up_mul_vector` : products of a family with a Lorentz-inert
  element or with a Lorentz vector.

## iii. Table of contents

- A. Coefficient tensors on spacetime indices
- B. Sums over index vectors
- C. Coefficient tensors
- D. Invariant tensors from invariant coefficient tensors
- E. Maps from components
- F. Products of families in an algebra

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C

namespace Invariants

/-!

## A. Coefficient tensors on spacetime indices

-/

section Spacetime

variable {n : ℕ}

/-- The action of a real `4 × 4` matrix on coefficient tensors, one factor per slot:
  `(act Λ c) a = ∑_d c_d Λ_{a₀ d₀} ⋯`, with `a` free and `d` summed. -/
def act (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin n → Fin 1 ⊕ Fin 3) : ℂ :=
  ∑ d, c d * ∏ s, ((Λ (a s) (d s) : ℝ) : ℂ)

/-- A coefficient tensor fixed by `act` of the Lorentz matrix of every `g : SL(2,ℂ)`. -/
def IsInvariantCoeff (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) : Prop :=
  ∀ g : SL(2,ℂ), act (SL2C.toLorentzGroup g).1 c = c

end Spacetime

end Invariants

open Invariants TensorSpecies complexLorentzTensor
open TensorSpecies.Tensor

/-!

## B. Sums over index vectors

-/

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

## C. Coefficient tensors

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

/-- The components of a tensor with `n` contravariant indices, as a coefficient tensor, the
  component equivalence of the species for the labels `vectorIdx n`. -/
noncomputable def coeffEquiv (n : ℕ) :
    ℂT(fun _ : Fin n => Color.up) ≃ₗ[ℂ] ((Fin n → Fin 1 ⊕ Fin 3) → ℂ) :=
  componentEquiv (vectorIdx n)

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

## D. Invariant tensors from invariant coefficient tensors

-/

/-- The invariant tensors lie in the image of any submodule `K` of coefficient tensors which
  contains every invariant coefficient tensor. -/
lemma invariants_tensorRep_le_map {n : ℕ} {K : Submodule ℂ ((Fin n → Fin 1 ⊕ Fin 3) → ℂ)}
    (hK : ∀ c, IsInvariantCoeff c → c ∈ K) :
    (complexLorentzTensor.tensorRep (fun _ : Fin n => Color.up)).invariants ≤
      K.map (coeffEquiv n).symm.toLinearMap := fun t ht => by
  rw [← (coeffEquiv n).symm_apply_apply t]
  exact Submodule.mem_map_of_mem (hK _ ((invariant_iff_isInvariantCoeff t).1 ht))

/-!

## E. Maps from components

-/

section Components

variable {n : ℕ} {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The map of a family contracts the coefficient tensor of its argument with the family. -/
lemma liftComponents_coeffEquiv_symm (T : (Fin n → Fin 1 ⊕ Fin 3) → B)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    liftComponents T ((coeffEquiv n).symm c)
      = ∑ d, c d • T d := by
  rw [coeffEquiv_symm_apply, map_sum]
  simp [vectorIdx]

/-- Precomposing the map of a family with the slot permutation `permT σ` reads the family at the
  permuted index vectors `d ∘ σ`. -/
lemma liftComponents_comp_permT (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    liftComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T ∘ₗ permT σ h
      = liftComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) fun d => T (d ∘ σ) :=
  (Tensor.basis _).ext fun φ => by
    rw [LinearMap.comp_apply, permT_basis, liftComponents_basis, liftComponents_basis]
    rfl

/-- A family antisymmetric under reading its index vectors through `σ` gives a map
  antisymmetric under `permT σ`. -/
lemma liftComponents_comp_permT_eq_neg (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B} (hT : ∀ d, T (d ∘ σ) = -T d) :
    liftComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T ∘ₗ permT σ h
      = -liftComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T := by
  rw [liftComponents_comp_permT]
  exact (Tensor.basis _).ext fun φ => by simp [hT]

/-- A family symmetric under reading its index vectors through `σ` gives a map invariant under
  `permT σ`. -/
lemma liftComponents_comp_permT_eq_self (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B} (hT : ∀ d, T (d ∘ σ) = T d) :
    liftComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T ∘ₗ permT σ h
      = liftComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T := by
  rw [liftComponents_comp_permT]
  exact congrArg liftComponents (funext hT)

/-- The map of a family is equivariant exactly when the family obeys the transformation law of
  the components of a tensor with `n` four-vector indices. -/
lemma isEquivariant_liftComponents_up_iff {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin n => .up) repLorentz (liftComponents T) ↔
      ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
        (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a := by
  rw [isEquivariant_liftComponents_iff]
  refine forall_congr' fun g => forall_congr' fun l => ?_
  refine Eq.congr_right (Finset.sum_congr rfl fun a _ => congrArg (· • T a) ?_)
  exact Finset.prod_congr rfl fun i _ => toMatrix_rep_up_apply g (a i) (l i)

end Components

/-!

## F. Products of families in an algebra

When the families take values in an algebra on which `SL(2,ℂ)` acts multiplicatively, a family
times a Lorentz-inert element keeps its rank, and a rank-two family times a Lorentz vector is a
rank-three family.

-/

section Products

variable {B : Type*} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- Multiplying a Lorentz tensor family by a Lorentz-inert element gives a family of the
  same rank, the element riding through the transformation law untouched. -/
lemma isEquivariant_liftComponents_up_mul_fixed {n : ℕ}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B}
    (hT : complexLorentzTensor.IsEquivariant (fun _ : Fin n => .up) repLorentz (liftComponents T))
    {y : B} (hy : ∀ g : SL(2,ℂ), repLorentz g y = y) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin n => .up) repLorentz
      (liftComponents fun d => T d * y) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [hmul, (isEquivariant_liftComponents_up_iff T).1 hT g l, hy g, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => smul_mul_assoc _ _ _

/-- A rank-two family against a Lorentz vector is a rank-three family, the two covector
  indices of the first factor and the single index of the second make three. -/
lemma isEquivariant_liftComponents_up_mul_vector
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentz (liftComponents T))
    {U : (Fin 1 ⊕ Fin 3) → B}
    (hU : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3), repLorentz g (U μ)
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ) • U ν) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 3 => .up) repLorentz
      (liftComponents fun d : Fin 3 → Fin 1 ⊕ Fin 3 => T ![d 0, d 1] * U (d 2)) := by
  refine (isEquivariant_liftComponents_up_iff _).2 fun g l => ?_
  rw [hmul, (isEquivariant_liftComponents_up_iff T).1 hT g ![l 0, l 1], hU g (l 2),
    sum_pi_fin_two, sum_pi_fin_three, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  simp [Fin.prod_univ_two, Fin.prod_univ_three, mul_assoc]

end Products

end Lorentz
