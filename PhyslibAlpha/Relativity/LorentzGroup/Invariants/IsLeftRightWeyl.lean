/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.IsBiLeftWeyl
/-!
# Lorentz invariants of a left-handed and a right-handed Weyl index

A left-handed and a right-handed Weyl index carry no Lorentz invariant but zero.

## i. Overview

A bispinor `T^{α α'}`, carrying one left-handed and one right-handed Weyl index, has no Lorentz
invariant but `0`: the pair carries the `(1/2, 1/2)` representation, a single four-vector index,
which has nothing to contract with. The same holds for the dual pair `T_{α α'}`. The families are
equivariant linear maps out of `ℂT[.upL, .upR]` and `ℂT[.downL, .downR]`, `IsLeftRightWeyl` and
`IsDualLeftRightWeyl` (A).

By `TensorSpecies.IsEquivariant.reducesInvariantsTo_bot` it is enough that the only invariant
tensor is zero (B). A tensor with two indices is `fromPairT` of an element of the tensor product
of the two Weyl representations, and two Weyl indices of opposite chirality have no invariants,
`Fermion.LeftHandedWeyl.invariants_tprod_rightHandedWeyl_eq_bot` and
`Fermion.DualLeftHandedWeyl.invariants_tprod_dualRightHandedWeyl_eq_bot`. The classification of
the invariants of a family follows (C).

A product of two one-index families of opposite chirality, `X_α Y_α'`, in an algebra with a
multiplicative Lorentz action, is a dual left-right family (D). This is the shape of a Dirac
mass term `ψ̄ ψ`, which therefore has no Lorentz invariant. A finite join of the spans of such
products is discarded from any Lorentz-stable submodule (E).

## ii. Key results

- `Lorentz.eq_zero_of_invariant_leftRight` : an invariant tensor with a left- and a
  right-handed Weyl index is zero.
- `Lorentz.IsLeftRightWeyl.reducesInvariantsTo_bot` : the invariants of the range of a
  left-right family reduce to `⊥`.
- `Lorentz.IsDualLeftRightWeyl.reducesInvariantsTo_bot` : the same for the dual indices.
- `Lorentz.isDualLeftRightWeyl_mul` : an undotted family times a dotted one is a dual
  left-right family.
- `Lorentz.mem_of_lorentz_invariant_iSup_dualLeftRightWeyl_span` : a Lorentz invariant of a
  join of spans of dual left-right families and a stable submodule `S` lies in `S`.

## iii. Table of contents

- A. Left-right families as equivariant maps
- B. The invariant tensors vanish
- C. The classification of the invariants
- D. One-index Weyl families and their products
- E. Peeling the pair spans off a Lorentz-stable submodule

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. Left-right families as equivariant maps

-/

/-- A family with a left- and a right-handed Weyl index `T^{α α'}`, an equivariant linear map
  out of `ℂT[.upL, .upR]`. -/
abbrev IsLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.upL, .upR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.upL, .upR] repLorentz f

/-- A family with a dual left- and a dual right-handed Weyl index `T_{α α'}`, an equivariant
  linear map out of `ℂT[.downL, .downR]`. -/
abbrev IsDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.downL, .downR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.downL, .downR] repLorentz f

/-!

## B. The invariant tensors vanish

-/

/-- An invariant tensor with a left- and a right-handed Weyl index, or with their duals, is
  zero. It comes from the tensor product of the two Weyl representations, which has no
  invariants but zero. -/
lemma eq_zero_of_invariant_leftRight {k k' : complexLorentzTensor.Color}
    (hk : (k = .upL ∧ k' = .upR) ∨ (k = .downL ∧ k' = .downR)) {t : ℂT[k, k']}
    (ht : ∀ g : SL(2,ℂ), g • t = t) : t = 0 := by
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Tensor.eq_zero_of_invariant_of_invariants_eq_bot (S := complexLorentzTensor)
      (c1 := .upL) (c2 := .upR) Fermion.LeftHandedWeyl.invariants_tprod_rightHandedWeyl_eq_bot ht
  · exact Tensor.eq_zero_of_invariant_of_invariants_eq_bot (S := complexLorentzTensor)
      (c1 := .downL) (c2 := .downR)
      Fermion.DualLeftHandedWeyl.invariants_tprod_dualRightHandedWeyl_eq_bot ht

/-!

## C. The classification of the invariants

-/

section Classification

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The invariants of the range of a left-right family reduce to `⊥`. A Lorentz invariant of
  `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, lies in `S`. -/
lemma IsLeftRightWeyl.reducesInvariantsTo_bot {f : ℂT[.upL, .upR] →ₗ[ℂ] B}
    (hf : IsLeftRightWeyl B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ :=
  TensorSpecies.IsEquivariant.reducesInvariantsTo_bot hf (complexLorentzTensor.isAdjointClosed _)
    fun _ ht => eq_zero_of_invariant_leftRight (Or.inl ⟨rfl, rfl⟩) ht

/-- Every Lorentz invariant in the range of a left-right family is zero. -/
lemma IsLeftRightWeyl.eq_zero_of_invariant {f : ℂT[.upL, .upR] →ₗ[ℂ] B}
    (hf : IsLeftRightWeyl B repLorentz f) {x : B} (hx : x ∈ LinearMap.range f)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  TensorSpecies.IsEquivariant.eq_zero_of_invariant hf (complexLorentzTensor.isAdjointClosed _)
    (fun _ ht => eq_zero_of_invariant_leftRight (Or.inl ⟨rfl, rfl⟩) ht) hx hinv

/-- The invariants of the range of a dual left-right family reduce to `⊥`. A Lorentz invariant
  of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, lies in `S`. -/
lemma IsDualLeftRightWeyl.reducesInvariantsTo_bot {f : ℂT[.downL, .downR] →ₗ[ℂ] B}
    (hf : IsDualLeftRightWeyl B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ :=
  TensorSpecies.IsEquivariant.reducesInvariantsTo_bot hf (complexLorentzTensor.isAdjointClosed _)
    fun _ ht => eq_zero_of_invariant_leftRight (Or.inr ⟨rfl, rfl⟩) ht

/-- Every Lorentz invariant in the range of a dual left-right family is zero. -/
lemma IsDualLeftRightWeyl.eq_zero_of_invariant {f : ℂT[.downL, .downR] →ₗ[ℂ] B}
    (hf : IsDualLeftRightWeyl B repLorentz f) {x : B} (hx : x ∈ LinearMap.range f)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  TensorSpecies.IsEquivariant.eq_zero_of_invariant hf (complexLorentzTensor.isAdjointClosed _)
    (fun _ ht => eq_zero_of_invariant_leftRight (Or.inr ⟨rfl, rfl⟩) ht) hx hinv

end Classification

/-!

## D. One-index Weyl families and their products

A two-element family of elements of an algebra `B` can carry one dual Weyl index, undotted
(`IsDualLeftWeyl`) or dotted (`IsDualRightWeyl`). Both laws are contragredient, and the dotted
law carries the extra complex conjugation. A fermion field of the Standard Model with every
index but its spinor index frozen is such a family. When the Lorentz action is multiplicative,
an undotted family times a dotted one is a dual left-right Weyl family, in either order.

-/

section ChiralFamilies

variable {B : Type} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- A two-element family `X` of elements of `B` carries a dual undotted spinor index, transforming
  by the contragredient of the left-handed Weyl representation. -/
def IsDualLeftWeyl (repLorentz : Representation ℂ SL(2,ℂ) B) (X : Fin 2 → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (X a) = ∑ β, (Λ⁻¹).1 a β • X β

/-- A two-element family `Y` of elements of `B` carries a dual dotted spinor index, transforming by
  the contragredient of the right-handed Weyl representation, which is the conjugate of the undotted
  law. -/
def IsDualRightWeyl (repLorentz : Representation ℂ SL(2,ℂ) B) (Y : Fin 2 → B) : Prop :=
  ∀ (Λ : SL(2,ℂ)) (a : Fin 2), repLorentz Λ (Y a) = ∑ β, star ((Λ⁻¹).1 a β) • Y β

variable (hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
  repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)

include hrepLorentz_mul

/-- An undotted family times a dotted one is a dual left-right Weyl family. -/
lemma isDualLeftRightWeyl_mul {X Y : Fin 2 → B} (hX : IsDualLeftWeyl repLorentz X)
    (hY : IsDualRightWeyl repLorentz Y) :
    IsDualLeftRightWeyl B repLorentz
      (ofPairComponents (k := .downL) (k' := .downR) fun a b => X a * Y b) :=
  isEquivariant_ofPairComponents _ fun g a b => by
    rw [toMatrix_rep_downL, toMatrix_rep_downR, hrepLorentz_mul, hX g a, hY g b,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]

/-- A dotted family times an undotted one is a dual left-right Weyl family, the two
  spinor slots exchanged. -/
lemma isDualLeftRightWeyl_mul_swap {X Y : Fin 2 → B} (hX : IsDualRightWeyl repLorentz X)
    (hY : IsDualLeftWeyl repLorentz Y) :
    IsDualLeftRightWeyl B repLorentz
      (ofPairComponents (k := .downL) (k' := .downR) fun a b => X b * Y a) :=
  isEquivariant_ofPairComponents _ fun g a b => by
    rw [toMatrix_rep_downL, toMatrix_rep_downR, hrepLorentz_mul, hX g b, hY g a,
      Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_smul_comm]
    congr 1
    rw [Matrix.transpose_apply, Matrix.conjTranspose_apply, ← SL2C.inverse_coe]
    ring

end ChiralFamilies

/-!

## E. Peeling the pair spans off a Lorentz-stable submodule

A dual left-right Weyl family carries no invariant, so the span of its components, here the
join of the lines through them, reduces to `⊥`. Each such span is stable under the Lorentz
group, so `ReducesInvariantsTo.biSup` combines the reductions over a finite family of them,
and a whole join is discarded from a Lorentz-stable submodule.

-/

section Peeling

variable {B : Type} [AddCommGroup B] [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- A finite join of the spans of dual left-right Weyl families carries no Lorentz
  invariant modulo a Lorentz-stable submodule. Such a family has no invariant, so each span
  reduces to `⊥`, and `ReducesInvariantsTo.biSup` combines the reductions. A Lorentz
  invariant of the join together with `S` lies in `S`. -/
lemma mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span {ι : Type} [DecidableEq ι]
    {T : ι → Fin 2 × Fin 2 → B} (hT : ∀ i, IsDualLeftRightWeyl B repLorentz
      (ofPairComponents (k := .downL) (k' := .downR) fun a b => T i (a, b)))
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (s : Finset ι)
    {x : B} (hx : x ∈ (⨆ i ∈ s, ⨆ l, ℂ ∙ T i l) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hr : ∀ i, (⨆ l, ℂ ∙ T i l)
      = LinearMap.range (ofPairComponents (k := .downL) (k' := .downR) fun a b => T i (a, b)) :=
    fun i => by rw [range_ofPairComponents, Submodule.span_range_eq_iSup]
  simp_rw [hr] at hx
  simpa using ReducesInvariantsTo.biSup (fun i => (hT i).reducesInvariantsTo_bot)
    (fun i => (hT i).isStableUnder_range) isStableUnder_bot s S hS x hx hinv

/-- The version of `mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span` joining over a
  whole finite index type. -/
lemma mem_of_lorentz_invariant_iSup_dualLeftRightWeyl_span {ι : Type} [Fintype ι]
    [DecidableEq ι] {T : ι → Fin 2 × Fin 2 → B}
    (hT : ∀ i, IsDualLeftRightWeyl B repLorentz
      (ofPairComponents (k := .downL) (k' := .downR) fun a b => T i (a, b))) (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ (⨆ i, ⨆ l, ℂ ∙ T i l) ⊔ S)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  refine mem_of_lorentz_invariant_biSup_dualLeftRightWeyl_span hT S hS Finset.univ ?_ hinv
  refine sup_le_sup_right (iSup_le fun i => ?_) S hx
  exact le_iSup₂_of_le i (Finset.mem_univ i) le_rfl

end Peeling

end Lorentz
