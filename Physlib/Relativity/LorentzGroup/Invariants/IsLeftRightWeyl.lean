/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsBiLeftWeyl
/-!
# Lorentz invariants of a left-handed and a right-handed Weyl index

## i. Overview

A bispinor `T^{α α'}`, carrying one left-handed and one right-handed Weyl index, has no Lorentz
invariant but `0`: the pair carries the `(1/2, 1/2)` representation, a single four-vector index,
which has nothing to contract with. The same holds for the dual pair `T_{α α'}`. The families are
equivariant linear maps out of `ℂT[.upL, .upR]` and `ℂT[.downL, .downR]`, `IsLeftRightWeyl` and
`IsDualLeftRightWeyl` (A).

By `TensorSpecies.IsEquivariant.reducesInvariantsTo_bot` it is enough that the only invariant
tensor is zero (B). Two diagonal elements of `SL(2,ℂ)` already force this. A diagonal
`g = diag (λ₀, λ₁)` multiplies the component `(a₁, a₂)` of a tensor of `ℂT[.upL, .upR]` by
`λ_{a₁} * conj λ_{a₂}`, and that of a tensor of `ℂT[.downL, .downR]` by the inverse of this. The
boost `diag (2, 2⁻¹)` along `z` scales `(0, 0)` by `4` and `(1, 1)` by `4⁻¹`, so these vanish,
and the half turn `diag (-i, i)` about `z` multiplies `(0, 1)` and `(1, 0)` by `-1`, so these
vanish too (C).

## ii. Key results

- `Lorentz.eq_zero_of_invariant_leftRight` : an invariant tensor with a left- and a
  right-handed Weyl index is zero.
- `Lorentz.IsLeftRightWeyl.reducesInvariantsTo_bot` : the invariants of the range of a
  left-right family reduce to `⊥`.
- `Lorentz.IsDualLeftRightWeyl.reducesInvariantsTo_bot` : the same for the dual indices.

## iii. Table of contents

- A. Left-right families as equivariant maps
- B. The invariant tensors vanish
- C. The classification of the invariants

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. Left-right families as equivariant maps

-/

/-- A family with a left- and a right-handed Weyl index `T^{α α'}`: an equivariant linear map
  out of `ℂT[.upL, .upR]`. -/
abbrev IsLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.upL, .upR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.upL, .upR] repLorentz f

/-- A family with a dual left- and a dual right-handed Weyl index `T_{α α'}`: an equivariant
  linear map out of `ℂT[.downL, .downR]`. -/
abbrev IsDualLeftRightWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B) (f : ℂT[.downL, .downR] →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant ![.downL, .downR] repLorentz f

/-!

## B. The invariant tensors vanish

-/

/-- An invariant tensor with a left- and a right-handed Weyl index, or with their duals, is
  zero. The inverse boost along `z` scales the two diagonal components by `4⁻¹` and `4`, and the
  inverse half turn about `z` negates the two mixed ones; for the dual colours the inverse
  cancels against the inverse in the matrix of the colour. -/
lemma eq_zero_of_invariant_leftRight {k k' : complexLorentzTensor.Color}
    (hk : (k = .upL ∧ k' = .upR) ∨ (k = .downL ∧ k' = .downR)) {t : ℂT[k, k']}
    (ht : ∀ g : SL(2,ℂ), g • t = t) : t = 0 := by
  have hinv : ∀ g : SL(2,ℂ), (g⁻¹).1⁻¹ = g.1 := fun g => by rw [SL2C.inverse_coe, inv_inv]
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have h := fun (g : SL(2,ℂ)) (x y : Fin 2) => congrArg (fun s : type_of% t =>
      (Tensor.basis (S := complexLorentzTensor) _).repr s
        ((piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![_, _] j))).symm (x, y))) (ht g)
    have h1 := h (SL2C.boostAxis 2 2 two_ne_zero)⁻¹ 0 0
    have h2 := h (SL2C.boostAxis 2 2 two_ne_zero)⁻¹ 1 1
    have h3 := h (SL2C.halfTurn 2)⁻¹ 0 1
    have h4 := h (SL2C.halfTurn 2)⁻¹ 1 0
    rw [basis_repr_smul_pair] at h1 h2 h3 h4
    first
      | rw [toMatrix_rep_upL, toMatrix_rep_upR] at h1 h2 h3 h4
      | rw [toMatrix_rep_downL, toMatrix_rep_downR] at h1 h2 h3 h4
    try simp only [hinv] at h1 h2 h3 h4
    simp [Fin.sum_univ_two, Matrix.adjugate_fin_two, map_ofNat] at h1 h2 h3 h4
    apply (Tensor.basis (S := complexLorentzTensor) _).repr.injective
    ext φ
    obtain ⟨⟨a, b⟩, rfl⟩ :=
      (piFinTwoEquiv fun j : Fin 2 => Fin (repDim (![_, _] j))).symm.surjective φ
    revert a b
    change ∀ a b : Fin 2, _
    simp only [Fin.forall_fin_two, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact ⟨⟨(mul_left_eq_self₀.1 h1).resolve_left (by norm_num),
      CharZero.neg_eq_self_iff.1 h3⟩, CharZero.neg_eq_self_iff.1 h4,
      (mul_left_eq_self₀.1 h2).resolve_left (by norm_num)⟩

/-!

## C. The classification of the invariants

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The invariants of the range of a left-right family reduce to `⊥`: a Lorentz invariant of
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

/-- The invariants of the range of a dual left-right family reduce to `⊥`: a Lorentz invariant
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

end Lorentz
