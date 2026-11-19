/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.LightConeDeriv
public import PhyslibAlpha.Relativity.SL2C.AxisRotations
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.Reynolds
/-!
# Tensor powers of the complex vector representation

Invariant coefficient tensors on spacetime indices, and equivariant maps out of the tensors with
`n` four-vector indices.

## i. Overview

The tensors `ℂT(fun _ : Fin n => .up)` with `n` contravariant indices are the `n`-th tensor power
of the complex vector representation `ComplexVector`. This file holds the machinery that the
classifications of their invariants (`OddRank`, `RankTwo`, `RankFour` in this folder) use.

A matrix `M` acts on coefficient functions by `actMat M`, and a covector that the transposed
matrix reproduces up to a scalar reads off a component that `actMat M` scales by that scalar, so
an invariant coefficient function has no such component unless the scalar is `1` (A). Writing
each slot of a coefficient tensor in the light-cone basis of an axis splits it into pieces that
a boost scales by powers of its parameter, and an invariant keeps only the piece of weight zero:
`Invariants.IsInvariantCoeff.lightConeComponent_eq_zero` (B). Section C records what the half
turns about the axes and the cyclic rotation of the axes force on an invariant coefficient
tensor, for any number of slots. Section D collects sums over index vectors.

The components of a tensor, relabelled by `Fin 1 ⊕ Fin 3` in each slot, are a coefficient tensor,
`coeffEquiv` (E), on which `SL(2,ℂ)` acts by `Invariants.act`. An invariant tensor therefore has
an invariant coefficient tensor, `Invariants.IsInvariantCoeff`, and a classification of the
invariant coefficient tensors is a classification of the invariant tensors (F).

A family `T` of vectors indexed by `n` directions is the map `ofComponents T`, sending each basis
tensor to the matching vector, and it is equivariant exactly when the vectors obey the
transformation law of the components of a tensor (G, `isEquivariant_ofComponents_up_iff`),

`repLorentz g (T l) = ∑_a (∏ i, Λ(g)_{a i, l i}) • T a`,

with `l` free and `a` summed, and the summed index first in each factor of the Lorentz matrix
`Λ(g)` of `g`. Permuting the slots by `permT σ` reads the coefficient tensor and the family at
permuted index vectors (`permT_coeffEquiv_symm`, `ofComponents_comp_permT`). Products of a family
with a Lorentz-inert element or with a Lorentz vector are again such families (H).

## ii. Key results

- `Lorentz.Invariants.IsInvariantCoeff` : invariant coefficient tensors.
- `Lorentz.Invariants.IsInvariantCoeff.lightConeComponent_eq_zero` : the boost kills the
  light-cone components of nonzero weight.
- `Lorentz.coeffEquiv` : the components of a tensor with `n` four-vector indices, as a coefficient
  tensor.
- `Lorentz.invariant_iff_isInvariantCoeff` : a tensor is invariant exactly when its coefficient
  tensor is.
- `Lorentz.invariants_tensorRep_le_map` : the invariant tensors come from the invariant
  coefficient tensors.
- `Lorentz.isEquivariant_ofComponents_up_iff` : the map of a family is equivariant exactly when
  the family obeys the transformation law.
- `Lorentz.isEquivariant_ofComponents_up_mul_fixed`,
  `Lorentz.isEquivariant_ofComponents_up_mul_vector` : products of a family with a Lorentz-inert
  element or with a Lorentz vector.

## iii. Table of contents

- A. Coefficient functions moved by a matrix
- B. Coefficient tensors on spacetime indices
- C. The half turns and the cyclic rotation
- D. Sums over index vectors
- E. Coefficient tensors
- F. Invariant tensors from invariant coefficient tensors
- G. Maps from components
- H. Products of families in an algebra

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C

namespace Invariants

/-!

## A. Coefficient functions moved by a matrix

A matrix `M` acts on coefficient functions by `actMat M`. The weight argument is generic: a
covector that the transposed matrix reproduces up to a scalar reads off a component that
`actMat M` scales by that scalar, so an invariant coefficient function has no such component
unless the scalar is `1`.

-/

section Mat

variable {ι : Type} [Fintype ι]

/-- The action on coefficient functions of a matrix moving the components:
  `(actMat M c) a = ∑_d c_d M_{a d}`, with `a` free and `d` summed. -/
def actMat (M : ι → ι → ℂ) (c : ι → ℂ) (a : ι) : ℂ := ∑ d, c d * M a d

/-- A covector `P` that the transposed matrix reproduces up to a scalar `k` reads off a
  component of the coefficients that `actMat M` scales by `k`. -/
lemma sum_mul_actMat (M : ι → ι → ℂ) (P c : ι → ℂ) (k : ℂ)
    (hP : ∀ d, ∑ a, P a * M a d = k * P d) :
    ∑ a, P a * actMat M c a = k * ∑ a, P a * c a := by
  simp only [actMat, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← mul_assoc, mul_comm _ (c d), ← hP d, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- A coefficient function fixed by `actMat M` has no component along a covector that the
  transposed matrix scales by an eigenvalue other than `1`. -/
lemma sum_mul_eq_zero_of_actMat_eq (M : ι → ι → ℂ) {P c : ι → ℂ} (hc : actMat M c = c) {k : ℂ}
    (hP : ∀ d, ∑ a, P a * M a d = k * P d) (hk : k ≠ 1) :
    ∑ a, P a * c a = 0 := by
  have h := sum_mul_actMat M P c k hP
  rw [hc] at h
  exact (mul_left_eq_self₀.1 h.symm).resolve_left hk

/-- The boost with parameter `2` distinguishes every nonzero weight: `2 ^ w ≠ 1` for `w ≠ 0`. -/
lemma two_zpow_ne_one {w : ℤ} (hw : w ≠ 0) : ((2 : ℝ) : ℂ) ^ w ≠ 1 := by
  rw [← Complex.ofReal_zpow, Ne, Complex.ofReal_eq_one,
    zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)]
  exact hw

end Mat

/-!

## B. Coefficient tensors on spacetime indices

-/

section Spacetime

variable {n : ℕ}

/-- The action of a real `4 × 4` matrix on coefficient tensors, one factor per slot:
  `(act Λ c) a = ∑_d c_d Λ_{a₀ d₀} ⋯`, with `a` free and `d` summed. -/
def act (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin n → Fin 1 ⊕ Fin 3) : ℂ :=
  ∑ d, c d * ∏ s, ((Λ (a s) (d s) : ℝ) : ℂ)

/-- The action on coefficient tensors is that of the matrix of products, one factor per slot. -/
lemma act_eq_actMat (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    act Λ c = actMat (fun a d => ∏ i, ((Λ (a i) (d i) : ℝ) : ℂ)) c := rfl

/-- A coefficient tensor fixed by `act` of the Lorentz matrix of every `g : SL(2,ℂ)`. -/
def IsInvariantCoeff (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) : Prop :=
  ∀ g : SL(2,ℂ), act (SL2C.toLorentzGroup g).1 c = c

/-- A light-cone component of a coefficient tensor along axis `i`: the multi-index `κ` picks
  one light-cone direction per slot and `c` is contracted against that choice. -/
def lightConeComponent (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) : ℂ :=
  ∑ a, (∏ s, lightConeCoeff i (κ s) (a s)) * c a

/-- A light-cone multi-index that `Λ` reproduces up to a scalar `k` has its light-cone
  component scaled by `k`. The hypothesis is the eigenvector equation for the covector
  `∏ₛ lightConeCoeff i (κ s) (·)` under the transposed action, which is the form the light-cone
  directions of an axis satisfy for the transformations diagonal in that basis: the boost along
  the axis, with `k` a power of its parameter, and the half turn about it, with `k` the product
  of the signs of the slots. -/
lemma lightConeComponent_act (i : Fin 3) (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) (k : ℂ)
    (hΛ : ∀ d : Fin n → Fin 1 ⊕ Fin 3,
      ∑ a : Fin n → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (κ s) (a s))
          * ∏ s, ((Λ (a s) (d s) : ℝ) : ℂ)
        = k * ∏ s, lightConeCoeff i (κ s) (d s)) :
    lightConeComponent i (act Λ c) κ = k * lightConeComponent i c κ :=
  sum_mul_actMat _ _ c k hΛ

/-- The Lorentz matrix of a boost is symmetric. -/
lemma toLorentzGroup_boostAxis_symm (i : Fin 3) {t : ℝ} (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 a b
      = (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 b a :=
  congrFun (congrFun
    (SL2C.toLorentzGroup_conjTranspose (SL2C.boostAxis_conjTranspose i t ht).symm) a) b

/-- An invariant coefficient tensor has no light-cone component of nonzero weight: the boost at
  `t = 2` would rescale such a component by a factor other than `1`. -/
lemma IsInvariantCoeff.lightConeComponent_eq_zero {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (i : Fin 3) {κ : Fin n → Fin 4}
    (hκ : ∑ s, lightConeWeight (κ s) ≠ 0) :
    lightConeComponent i c κ = 0 :=
  sum_mul_eq_zero_of_actMat_eq _ (hc (SL2C.boostAxis i 2 two_ne_zero))
    (fun d => by
      simpa only [toLorentzGroup_boostAxis_symm i two_ne_zero (d _)] using
        sum_prod_lightConeCoeff i κ d two_ne_zero)
    (two_zpow_ne_one hκ)

/-- A coefficient tensor is recovered from its light-cone components. -/
lemma eq_sum_lightConeComponent (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ)
    (d : Fin n → Fin 1 ⊕ Fin 3) :
    c d = ∑ κ, (∏ s, lightConeCoeffInv i (d s) (κ s)) * lightConeComponent i c κ := by
  simp only [lightConeComponent, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_prod_lightConeCoeffInv, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-!

## C. The half turns and the cyclic rotation

The half turn `SL2C.halfTurn k` has a diagonal Lorentz matrix with the signs `halfTurnSign k`,
so it multiplies the coefficient at `d` by the product of the signs of the slots of `d`. That
product is `1` or `-1`, and where it is `-1` invariance forces the coefficient to vanish.

The cyclic rotation `SL2C.rotationCycle` has the permutation matrix of `cycDir`, so it moves
coefficients rather than rescaling them, and invariance says that a coefficient tensor takes
the same value at `d` and at `cycIdx d`, the index vector with every slot rotated.

-/

/-- The half turn about the axis `k` multiplies the coefficient at `a` by the product of the
  signs `halfTurnSign k` of the slots of `a`. -/
lemma act_halfTurn (k : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin n → Fin 1 ⊕ Fin 3) :
    act (SL2C.toLorentzGroup (SL2C.halfTurn k)).1 c a
      = ((∏ s, halfTurnSign k (a s) : ℤ) : ℂ) * c a := by
  rw [act, Finset.sum_eq_single a]
  · rw [mul_comm]
    push_cast
    congr 1
    exact Finset.prod_congr rfl fun s _ => by
      rw [SL2C.toLorentzGroup_halfTurn_apply, ite_eq_left rfl, Complex.ofReal_intCast]
  · intro d _ hd
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hd.symm
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    rw [SL2C.toLorentzGroup_halfTurn_apply, ite_eq_right hs, Complex.ofReal_zero]
  · exact fun h => absurd (Finset.mem_univ a) h

/-- The sign a half turn attaches to a coefficient is `1` or `-1`, being a product of such
  signs. -/
lemma prod_halfTurnSign_eq_one_or (k : Fin 3) (d : Fin n → Fin 1 ⊕ Fin 3) :
    ∏ s, halfTurnSign k (d s) = 1 ∨ ∏ s, halfTurnSign k (d s) = -1 := by
  refine Finset.prod_induction _ (fun m : ℤ => m = 1 ∨ m = -1) ?_ (Or.inl rfl) fun s _ => ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · unfold halfTurnSign
    split_ifs <;> simp

/-- An invariant coefficient tensor vanishes at every index vector that some half turn
  negates. -/
lemma IsInvariantCoeff.eq_zero_of_prod_halfTurnSign_ne_one {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) {k : Fin 3} {d : Fin n → Fin 1 ⊕ Fin 3}
    (hd : ∏ s, halfTurnSign k (d s) ≠ 1) : c d = 0 := by
  have h := congrFun (hc (SL2C.halfTurn k)) d
  rw [act_halfTurn, (prod_halfTurnSign_eq_one_or k d).resolve_left hd] at h
  push_cast at h
  linear_combination (-2⁻¹ : ℂ) * h

/-- The relabelling `cycDir`, which fixes time and sends `x → y → z → x`, applied in every
  slot. -/
def cycIdx (d : Fin n → Fin 1 ⊕ Fin 3) : Fin n → Fin 1 ⊕ Fin 3 := fun s => cycDir (d s)

/-- Cycling the axes three times is the identity. -/
lemma cycIdx_cycIdx_cycIdx (d : Fin n → Fin 1 ⊕ Fin 3) : cycIdx (cycIdx (cycIdx d)) = d :=
  funext fun s => cycDir_cycDir_cycDir (d s)

/-- The cyclic rotation permutes coefficients: the new coefficient at `a` is the old one at `a`
  cycled back. -/
lemma act_rotationCycle (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin n → Fin 1 ⊕ Fin 3) :
    act (SL2C.toLorentzGroup SL2C.rotationCycle).1 c a = c (cycIdx (cycIdx a)) := by
  rw [act, Finset.sum_eq_single (cycIdx (cycIdx a))]
  · rw [Finset.prod_eq_one fun s _ => ?_, mul_one]
    rw [SL2C.toLorentzGroup_rotationCycle_apply, ite_eq_left, Complex.ofReal_one]
    exact (congrFun (cycIdx_cycIdx_cycIdx a) s).symm
  · intro d _ hd
    have hne : cycIdx d ≠ a := fun h => hd (by rw [← h, cycIdx_cycIdx_cycIdx])
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hne
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    rw [SL2C.toLorentzGroup_rotationCycle_apply,
      ite_eq_right fun h : a s = cycDir (d s) => hs h.symm, Complex.ofReal_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- An invariant coefficient tensor is constant on the orbits of the cyclic rotation. -/
lemma IsInvariantCoeff.apply_cycIdx {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (d : Fin n → Fin 1 ⊕ Fin 3) : c (cycIdx d) = c d := by
  have h := congrFun (hc SL2C.rotationCycle) (cycIdx d)
  rw [act_rotationCycle, cycIdx_cycIdx_cycIdx] at h
  exact h.symm

end Spacetime

end Invariants

open Invariants TensorSpecies complexLorentzTensor
open TensorSpecies.Tensor hiding ofComponents

/-!

## D. Sums over index vectors

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

## E. Coefficient tensors

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

## F. Invariant tensors from invariant coefficient tensors

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

## G. Maps from components

-/

section Components

variable {n : ℕ} {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The map of a family contracts the coefficient tensor of its argument with the family. -/
lemma ofComponents_coeffEquiv_symm (T : (Fin n → Fin 1 ⊕ Fin 3) → B)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    ofComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T ((coeffEquiv n).symm c)
      = ∑ d, c d • T d := by
  rw [coeffEquiv_symm_apply, map_sum]
  simp [vectorIdx]

/-- Precomposing the map of a family with the slot permutation `permT σ` reads the family at the
  permuted index vectors `d ∘ σ`. -/
lemma ofComponents_comp_permT (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    ofComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T ∘ₗ permT σ h
      = ofComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) fun d => T (d ∘ σ) :=
  (Tensor.basis _).ext fun φ => by
    rw [LinearMap.comp_apply, permT_basis, ofComponents_basis, ofComponents_basis]
    rfl

/-- A family antisymmetric under reading its index vectors through `σ` gives a map
  antisymmetric under `permT σ`. -/
lemma ofComponents_comp_permT_eq_neg (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B} (hT : ∀ d, T (d ∘ σ) = -T d) :
    ofComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T ∘ₗ permT σ h
      = -ofComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T := by
  rw [ofComponents_comp_permT]
  exact (Tensor.basis _).ext fun φ => by simp [hT]

/-- A family symmetric under reading its index vectors through `σ` gives a map invariant under
  `permT σ`. -/
lemma ofComponents_comp_permT_eq_self (σ : Fin n → Fin n)
    (h : IsReindexing (fun _ : Fin n => Color.up) (fun _ => Color.up) σ)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B} (hT : ∀ d, T (d ∘ σ) = T d) :
    ofComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T ∘ₗ permT σ h
      = ofComponents (S := complexLorentzTensor) (c := fun _ : Fin n => .up) T := by
  rw [ofComponents_comp_permT]
  exact congrArg ofComponents (funext hT)

/-- The map of a family is equivariant exactly when the family obeys the transformation law of
  the components of a tensor with `n` four-vector indices. -/
lemma isEquivariant_ofComponents_up_iff {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : (Fin n → Fin 1 ⊕ Fin 3) → B) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin n => .up) repLorentz (ofComponents T) ↔
      ∀ (g : SL(2,ℂ)) l, repLorentz g (T l) = ∑ a : Fin n → Fin 1 ⊕ Fin 3,
        (∏ i, (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a := by
  rw [isEquivariant_ofComponents_iff]
  refine forall_congr' fun g => forall_congr' fun l => ?_
  refine Eq.congr_right (Finset.sum_congr rfl fun a _ => congrArg (· • T a) ?_)
  exact Finset.prod_congr rfl fun i _ => toMatrix_rep_up_apply g (a i) (l i)

end Components

/-!

## H. Products of families in an algebra

When the families take values in an algebra on which `SL(2,ℂ)` acts multiplicatively, a family
times a Lorentz-inert element keeps its rank, and a rank-two family times a Lorentz vector is a
rank-three family.

-/

section Products

variable {B : Type*} [Ring B] [Algebra ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- Multiplying a Lorentz tensor family by a Lorentz-inert element gives a family of the
  same rank, the element riding through the transformation law untouched. -/
lemma isEquivariant_ofComponents_up_mul_fixed {n : ℕ}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin n → Fin 1 ⊕ Fin 3) → B}
    (hT : complexLorentzTensor.IsEquivariant (fun _ : Fin n => .up) repLorentz (ofComponents T))
    {y : B} (hy : ∀ g : SL(2,ℂ), repLorentz g y = y) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin n => .up) repLorentz
      (ofComponents fun d => T d * y) := by
  refine (isEquivariant_ofComponents_up_iff _).2 fun g l => ?_
  rw [hmul, (isEquivariant_ofComponents_up_iff T).1 hT g l, hy g, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => smul_mul_assoc _ _ _

/-- A rank-two family against a Lorentz vector is a rank-three family, the two covector
  indices of the first factor and the single index of the second make three. -/
lemma isEquivariant_ofComponents_up_mul_vector
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : B), repLorentz Λ (x * y) = repLorentz Λ x * repLorentz Λ y)
    {T : (Fin 2 → Fin 1 ⊕ Fin 3) → B}
    (hT : complexLorentzTensor.IsEquivariant (fun _ : Fin 2 => .up) repLorentz (ofComponents T))
    {U : (Fin 1 ⊕ Fin 3) → B}
    (hU : ∀ (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3), repLorentz g (U μ)
      = ∑ ν : Fin 1 ⊕ Fin 3, (((SL2C.toLorentzGroup g).1 ν μ : ℝ) : ℂ) • U ν) :
    complexLorentzTensor.IsEquivariant (fun _ : Fin 3 => .up) repLorentz
      (ofComponents fun d : Fin 3 → Fin 1 ⊕ Fin 3 => T ![d 0, d 1] * U (d 2)) := by
  refine (isEquivariant_ofComponents_up_iff _).2 fun g l => ?_
  rw [hmul, (isEquivariant_ofComponents_up_iff T).1 hT g ![l 0, l 1], hU g (l 2),
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
